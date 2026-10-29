import BstLean.Part268CellShard33Data

/-! Twenty scalar cells per dimension in a 25-dimension shard. -/
namespace BstLean.Part268
open Real BstLean.Part263

theorem cert13175_0 : CellCertificate 13175 (109234983089769 / 1250000000000000 : ℝ) (1594245139920879 / 1000000000000000000 : ℝ) (321755767267503 / 10000000000000000 : ℝ)
    (cell13175 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · have h := gap_lower (n := 13175) (a := (84069063429517 / 100000000000000 : ℝ)) (b := (156274406463 / 100000000000000 : ℝ)) (q := (2196346919641 / 100000000000000 : ℝ))
      (E := (cell13175 ⟨0, by decide⟩).energy) (xi := (321755767267503 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13175 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13175]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13175])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13175) (a := (84069063429517 / 100000000000000 : ℝ)) (b := (156274406463 / 100000000000000 : ℝ)) (q := (2196346919641 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13175])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13175])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13175]

theorem cert13175_1 : CellCertificate 13175 (109234983089769 / 1250000000000000 : ℝ) (1594245139920879 / 1000000000000000000 : ℝ) (321755767267503 / 10000000000000000 : ℝ)
    (cell13175 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · have h := gap_lower (n := 13175) (a := (3361367002827 / 4000000000000 : ℝ)) (b := (156274406463 / 100000000000000 : ℝ)) (q := (2196350938203 / 100000000000000 : ℝ))
      (E := (cell13175 ⟨1, by decide⟩).energy) (xi := (321755767267503 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13175 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13175]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13175])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13175) (a := (3361367002827 / 4000000000000 : ℝ)) (b := (156274406463 / 100000000000000 : ℝ)) (q := (2196350938203 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13175])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13175])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13175]

theorem cert13175_2 : CellCertificate 13175 (109234983089769 / 1250000000000000 : ℝ) (1594245139920879 / 1000000000000000000 : ℝ) (321755767267503 / 10000000000000000 : ℝ)
    (cell13175 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · have h := gap_lower (n := 13175) (a := (41999655762181 / 50000000000000 : ℝ)) (b := (156274406463 / 100000000000000 : ℝ)) (q := (2196354962243 / 100000000000000 : ℝ))
      (E := (cell13175 ⟨2, by decide⟩).energy) (xi := (321755767267503 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13175 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13175]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13175])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13175) (a := (41999655762181 / 50000000000000 : ℝ)) (b := (156274406463 / 100000000000000 : ℝ)) (q := (2196354962243 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13175])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13175])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13175]

theorem cert13175_3 : CellCertificate 13175 (109234983089769 / 1250000000000000 : ℝ) (1594245139920879 / 1000000000000000000 : ℝ) (321755767267503 / 10000000000000000 : ℝ)
    (cell13175 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · have h := gap_lower (n := 13175) (a := (20991118188587 / 25000000000000 : ℝ)) (b := (156274406463 / 100000000000000 : ℝ)) (q := (4289763559 / 195312500000 : ℝ))
      (E := (cell13175 ⟨3, by decide⟩).energy) (xi := (321755767267503 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13175 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13175]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13175])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13175) (a := (20991118188587 / 25000000000000 : ℝ)) (b := (156274406463 / 100000000000000 : ℝ)) (q := (4289763559 / 195312500000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13175])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13175])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13175]

theorem cert13175_4 : CellCertificate 13175 (109234983089769 / 1250000000000000 : ℝ) (1594245139920879 / 1000000000000000000 : ℝ) (321755767267503 / 10000000000000000 : ℝ)
    (cell13175 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · have h := gap_lower (n := 13175) (a := (83929658724591 / 100000000000000 : ℝ)) (b := (156274406463 / 100000000000000 : ℝ)) (q := (1098181501023 / 50000000000000 : ℝ))
      (E := (cell13175 ⟨4, by decide⟩).energy) (xi := (321755767267503 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13175 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13175]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13175])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13175) (a := (83929658724591 / 100000000000000 : ℝ)) (b := (156274406463 / 100000000000000 : ℝ)) (q := (1098181501023 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13175])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13175])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13175]

theorem cert13175_5 : CellCertificate 13175 (109234983089769 / 1250000000000000 : ℝ) (1594245139920879 / 1000000000000000000 : ℝ) (321755767267503 / 10000000000000000 : ℝ)
    (cell13175 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · have h := gap_lower (n := 13175) (a := (2097371734981 / 2500000000000 : ℝ)) (b := (156274406463 / 100000000000000 : ℝ)) (q := (274545871971 / 12500000000000 : ℝ))
      (E := (cell13175 ⟨5, by decide⟩).energy) (xi := (321755767267503 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13175 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13175]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13175])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13175) (a := (2097371734981 / 2500000000000 : ℝ)) (b := (156274406463 / 100000000000000 : ℝ)) (q := (274545871971 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13175])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13175])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13175]

theorem cert13175_6 : CellCertificate 13175 (109234983089769 / 1250000000000000 : ℝ) (1594245139920879 / 1000000000000000000 : ℝ) (321755767267503 / 10000000000000000 : ℝ)
    (cell13175 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · have h := gap_lower (n := 13175) (a := (8386010474263 / 10000000000000 : ℝ)) (b := (156274406463 / 100000000000000 : ℝ)) (q := (439274197367 / 20000000000000 : ℝ))
      (E := (cell13175 ⟨6, by decide⟩).energy) (xi := (321755767267503 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13175 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13175]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13175])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13175) (a := (8386010474263 / 10000000000000 : ℝ)) (b := (156274406463 / 100000000000000 : ℝ)) (q := (439274197367 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13175])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13175])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13175]

theorem cert13175_7 : CellCertificate 13175 (109234983089769 / 1250000000000000 : ℝ) (1594245139920879 / 1000000000000000000 : ℝ) (321755767267503 / 10000000000000000 : ℝ)
    (cell13175 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · have h := gap_lower (n := 13175) (a := (16765072943857 / 20000000000000 : ℝ)) (b := (156274406463 / 100000000000000 : ℝ)) (q := (10981875213 / 500000000000 : ℝ))
      (E := (cell13175 ⟨7, by decide⟩).energy) (xi := (321755767267503 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13175 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13175]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13175])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13175) (a := (16765072943857 / 20000000000000 : ℝ)) (b := (156274406463 / 100000000000000 : ℝ)) (q := (10981875213 / 500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13175])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13175])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13175]

theorem cert13175_8 : CellCertificate 13175 (109234983089769 / 1250000000000000 : ℝ) (1594245139920879 / 1000000000000000000 : ℝ) (321755767267503 / 10000000000000000 : ℝ)
    (cell13175 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · have h := gap_lower (n := 13175) (a := (41895324646957 / 50000000000000 : ℝ)) (b := (156274406463 / 100000000000000 : ℝ)) (q := (1098189517039 / 50000000000000 : ℝ))
      (E := (cell13175 ⟨8, by decide⟩).energy) (xi := (321755767267503 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13175 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13175]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13175])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13175) (a := (41895324646957 / 50000000000000 : ℝ)) (b := (156274406463 / 100000000000000 : ℝ)) (q := (1098189517039 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13175])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13175])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13175]

theorem cert13175_9 : CellCertificate 13175 (109234983089769 / 1250000000000000 : ℝ) (1594245139920879 / 1000000000000000000 : ℝ) (321755767267503 / 10000000000000000 : ℝ)
    (cell13175 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · have h := gap_lower (n := 13175) (a := (5234747401963 / 6250000000000 : ℝ)) (b := (156274406463 / 100000000000000 : ℝ)) (q := (17159242391 / 781250000000 : ℝ))
      (E := (cell13175 ⟨9, by decide⟩).energy) (xi := (321755767267503 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13175 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13175]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13175])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13175) (a := (5234747401963 / 6250000000000 : ℝ)) (b := (156274406463 / 100000000000000 : ℝ)) (q := (17159242391 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13175])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13175])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13175]

theorem cert13175_10 : CellCertificate 13175 (109234983089769 / 1250000000000000 : ℝ) (1594245139920879 / 1000000000000000000 : ℝ) (321755767267503 / 10000000000000000 : ℝ)
    (cell13175 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · have h := gap_lower (n := 13175) (a := (16744258419369 / 20000000000000 : ℝ)) (b := (156274406463 / 100000000000000 : ℝ)) (q := (274548385391 / 12500000000000 : ℝ))
      (E := (cell13175 ⟨10, by decide⟩).energy) (xi := (321755767267503 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13175 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13175]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13175])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13175) (a := (16744258419369 / 20000000000000 : ℝ)) (b := (156274406463 / 100000000000000 : ℝ)) (q := (274548385391 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13175])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13175])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13175]

theorem cert13175_11 : CellCertificate 13175 (109234983089769 / 1250000000000000 : ℝ) (1594245139920879 / 1000000000000000000 : ℝ) (321755767267503 / 10000000000000000 : ℝ)
    (cell13175 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · have h := gap_lower (n := 13175) (a := (83686650255481 / 100000000000000 : ℝ)) (b := (156274406463 / 100000000000000 : ℝ)) (q := (1098195547723 / 50000000000000 : ℝ))
      (E := (cell13175 ⟨11, by decide⟩).energy) (xi := (321755767267503 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13175 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13175]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13175])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13175) (a := (83686650255481 / 100000000000000 : ℝ)) (b := (156274406463 / 100000000000000 : ℝ)) (q := (1098195547723 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13175])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13175])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13175]

theorem cert13175_12 : CellCertificate 13175 (109234983089769 / 1250000000000000 : ℝ) (1594245139920879 / 1000000000000000000 : ℝ) (321755767267503 / 10000000000000000 : ℝ)
    (cell13175 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · have h := gap_lower (n := 13175) (a := (83652032872757 / 100000000000000 : ℝ)) (b := (156274406463 / 100000000000000 : ℝ)) (q := (439279013793 / 20000000000000 : ℝ))
      (E := (cell13175 ⟨12, by decide⟩).energy) (xi := (321755767267503 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13175 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13175]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13175])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13175) (a := (83652032872757 / 100000000000000 : ℝ)) (b := (156274406463 / 100000000000000 : ℝ)) (q := (439279013793 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13175])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13175])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13175]

theorem cert13175_13 : CellCertificate 13175 (109234983089769 / 1250000000000000 : ℝ) (1594245139920879 / 1000000000000000000 : ℝ) (321755767267503 / 10000000000000000 : ℝ)
    (cell13175 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · have h := gap_lower (n := 13175) (a := (83617439914289 / 100000000000000 : ℝ)) (b := (156274406463 / 100000000000000 : ℝ)) (q := (549099781431 / 25000000000000 : ℝ))
      (E := (cell13175 ⟨13, by decide⟩).energy) (xi := (321755767267503 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13175 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13175]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13175])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13175) (a := (83617439914289 / 100000000000000 : ℝ)) (b := (156274406463 / 100000000000000 : ℝ)) (q := (549099781431 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13175])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13175])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13175]

theorem cert13175_14 : CellCertificate 13175 (109234983089769 / 1250000000000000 : ℝ) (1594245139920879 / 1000000000000000000 : ℝ) (321755767267503 / 10000000000000000 : ℝ)
    (cell13175 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · have h := gap_lower (n := 13175) (a := (20895717836469 / 25000000000000 : ℝ)) (b := (156274406463 / 100000000000000 : ℝ)) (q := (2196403096783 / 100000000000000 : ℝ))
      (E := (cell13175 ⟨14, by decide⟩).energy) (xi := (321755767267503 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13175 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13175]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13175])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13175) (a := (20895717836469 / 25000000000000 : ℝ)) (b := (156274406463 / 100000000000000 : ℝ)) (q := (2196403096783 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13175])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13175])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13175]

theorem cert13175_15 : CellCertificate 13175 (109234983089769 / 1250000000000000 : ℝ) (1594245139920879 / 1000000000000000000 : ℝ) (321755767267503 / 10000000000000000 : ℝ)
    (cell13175 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · have h := gap_lower (n := 13175) (a := (8354832713349 / 10000000000000 : ℝ)) (b := (156274406463 / 100000000000000 : ℝ)) (q := (549101790481 / 25000000000000 : ℝ))
      (E := (cell13175 ⟨15, by decide⟩).energy) (xi := (321755767267503 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13175 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13175]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13175])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13175) (a := (8354832713349 / 10000000000000 : ℝ)) (b := (156274406463 / 100000000000000 : ℝ)) (q := (549101790481 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13175])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13175])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13175]

theorem cert13175_16 : CellCertificate 13175 (109234983089769 / 1250000000000000 : ℝ) (1594245139920879 / 1000000000000000000 : ℝ) (321755767267503 / 10000000000000000 : ℝ)
    (cell13175 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · have h := gap_lower (n := 13175) (a := (41756903621641 / 50000000000000 : ℝ)) (b := (156274406463 / 100000000000000 : ℝ)) (q := (109820557579 / 5000000000000 : ℝ))
      (E := (cell13175 ⟨16, by decide⟩).energy) (xi := (321755767267503 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13175 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13175]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13175])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13175) (a := (41756903621641 / 50000000000000 : ℝ)) (b := (156274406463 / 100000000000000 : ℝ)) (q := (109820557579 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13175])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13175])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13175]

theorem cert13175_17 : CellCertificate 13175 (109234983089769 / 1250000000000000 : ℝ) (1594245139920879 / 1000000000000000000 : ℝ) (321755767267503 / 10000000000000000 : ℝ)
    (cell13175 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · have h := gap_lower (n := 13175) (a := (83479311641577 / 100000000000000 : ℝ)) (b := (156274406463 / 100000000000000 : ℝ)) (q := (219641518693 / 10000000000000 : ℝ))
      (E := (cell13175 ⟨17, by decide⟩).energy) (xi := (321755767267503 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13175 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13175]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13175])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13175) (a := (83479311641577 / 100000000000000 : ℝ)) (b := (156274406463 / 100000000000000 : ℝ)) (q := (219641518693 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13175])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13175])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13175]

theorem cert13175_18 : CellCertificate 13175 (109234983089769 / 1250000000000000 : ℝ) (1594245139920879 / 1000000000000000000 : ℝ) (321755767267503 / 10000000000000000 : ℝ)
    (cell13175 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · have h := gap_lower (n := 13175) (a := (667558722359 / 800000000000 : ℝ)) (b := (156274406463 / 100000000000000 : ℝ)) (q := (2196419155993 / 100000000000000 : ℝ))
      (E := (cell13175 ⟨18, by decide⟩).energy) (xi := (321755767267503 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13175 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13175]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13175])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13175) (a := (667558722359 / 800000000000 : ℝ)) (b := (156274406463 / 100000000000000 : ℝ)) (q := (2196419155993 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13175])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13175])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13175]

theorem cert13175_19 : CellCertificate 13175 (109234983089769 / 1250000000000000 : ℝ) (1594245139920879 / 1000000000000000000 : ℝ) (321755767267503 / 10000000000000000 : ℝ)
    (cell13175 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · have h := gap_lower (n := 13175) (a := (10426299146231 / 12500000000000 : ℝ)) (b := (156274406463 / 100000000000000 : ℝ)) (q := (2196423179561 / 100000000000000 : ℝ))
      (E := (cell13175 ⟨19, by decide⟩).energy) (xi := (321755767267503 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13175 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13175]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13175])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13175) (a := (10426299146231 / 12500000000000 : ℝ)) (b := (156274406463 / 100000000000000 : ℝ)) (q := (2196423179561 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13175])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13175])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13175]

theorem cert13176_0 : CellCertificate 13176 (174770765719119 / 2000000000000000 : ℝ) (1594124105435359 / 1000000000000000000 : ℝ) (80432697922471 / 2500000000000000 : ℝ)
    (cell13176 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · have h := gap_lower (n := 13176) (a := (42034524686941 / 50000000000000 : ℝ)) (b := (19532801371 / 12500000000000 : ℝ)) (q := (1098118215429 / 50000000000000 : ℝ))
      (E := (cell13176 ⟨0, by decide⟩).energy) (xi := (80432697922471 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13176 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13176]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13176])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13176) (a := (42034524686941 / 50000000000000 : ℝ)) (b := (19532801371 / 12500000000000 : ℝ)) (q := (1098118215429 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13176])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13176])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13176]

theorem cert13176_1 : CellCertificate 13176 (174770765719119 / 2000000000000000 : ℝ) (1594124105435359 / 1000000000000000000 : ℝ) (80432697922471 / 2500000000000000 : ℝ)
    (cell13176 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · have h := gap_lower (n := 13176) (a := (84034161021279 / 100000000000000 : ℝ)) (b := (19532801371 / 12500000000000 : ℝ)) (q := (2196240445923 / 100000000000000 : ℝ))
      (E := (cell13176 ⟨1, by decide⟩).energy) (xi := (80432697922471 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13176 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13176]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13176])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13176) (a := (84034161021279 / 100000000000000 : ℝ)) (b := (19532801371 / 12500000000000 : ℝ)) (q := (2196240445923 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13176])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13176])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13176]

theorem cert13176_2 : CellCertificate 13176 (174770765719119 / 2000000000000000 : ℝ) (1594124105435359 / 1000000000000000000 : ℝ) (80432697922471 / 2500000000000000 : ℝ)
    (cell13176 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · have h := gap_lower (n := 13176) (a := (83999297481201 / 100000000000000 : ℝ)) (b := (19532801371 / 12500000000000 : ℝ)) (q := (137265279157 / 6250000000000 : ℝ))
      (E := (cell13176 ⟨2, by decide⟩).energy) (xi := (80432697922471 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13176 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13176]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13176])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13176) (a := (83999297481201 / 100000000000000 : ℝ)) (b := (19532801371 / 12500000000000 : ℝ)) (q := (137265279157 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13176])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13176])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13176]

theorem cert13176_3 : CellCertificate 13176 (174770765719119 / 2000000000000000 : ℝ) (1594124105435359 / 1000000000000000000 : ℝ) (80432697922471 / 2500000000000000 : ℝ)
    (cell13176 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · have h := gap_lower (n := 13176) (a := (16792891743483 / 20000000000000 : ℝ)) (b := (19532801371 / 12500000000000 : ℝ)) (q := (2196248501001 / 100000000000000 : ℝ))
      (E := (cell13176 ⟨3, by decide⟩).energy) (xi := (80432697922471 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13176 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13176]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13176])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13176) (a := (16792891743483 / 20000000000000 : ℝ)) (b := (19532801371 / 12500000000000 : ℝ)) (q := (2196248501001 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13176])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13176])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13176]

theorem cert13176_4 : CellCertificate 13176 (174770765719119 / 2000000000000000 : ℝ) (1594124105435359 / 1000000000000000000 : ℝ) (80432697922471 / 2500000000000000 : ℝ)
    (cell13176 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · have h := gap_lower (n := 13176) (a := (83929644693881 / 100000000000000 : ℝ)) (b := (19532801371 / 12500000000000 : ℝ)) (q := (439250499911 / 20000000000000 : ℝ))
      (E := (cell13176 ⟨4, by decide⟩).energy) (xi := (80432697922471 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13176 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13176]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13176])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13176) (a := (83929644693881 / 100000000000000 : ℝ)) (b := (19532801371 / 12500000000000 : ℝ)) (q := (439250499911 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13176])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13176])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13176]

theorem cert13176_5 : CellCertificate 13176 (174770765719119 / 2000000000000000 : ℝ) (1594124105435359 / 1000000000000000000 : ℝ) (80432697922471 / 2500000000000000 : ℝ)
    (cell13176 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · have h := gap_lower (n := 13176) (a := (83894855374747 / 100000000000000 : ℝ)) (b := (19532801371 / 12500000000000 : ℝ)) (q := (2196256527941 / 100000000000000 : ℝ))
      (E := (cell13176 ⟨5, by decide⟩).energy) (xi := (80432697922471 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13176 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13176]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13176])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13176) (a := (83894855374747 / 100000000000000 : ℝ)) (b := (19532801371 / 12500000000000 : ℝ)) (q := (2196256527941 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13176])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13176])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13176]

theorem cert13176_6 : CellCertificate 13176 (174770765719119 / 2000000000000000 : ℝ) (1594124105435359 / 1000000000000000000 : ℝ) (80432697922471 / 2500000000000000 : ℝ)
    (cell13176 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · have h := gap_lower (n := 13176) (a := (83860090724349 / 100000000000000 : ℝ)) (b := (19532801371 / 12500000000000 : ℝ)) (q := (2196260535769 / 100000000000000 : ℝ))
      (E := (cell13176 ⟨6, by decide⟩).energy) (xi := (80432697922471 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13176 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13176]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13176])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13176) (a := (83860090724349 / 100000000000000 : ℝ)) (b := (19532801371 / 12500000000000 : ℝ)) (q := (2196260535769 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13176])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13176])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13176]

theorem cert13176_7 : CellCertificate 13176 (174770765719119 / 2000000000000000 : ℝ) (1594124105435359 / 1000000000000000000 : ℝ) (80432697922471 / 2500000000000000 : ℝ)
    (cell13176 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · have h := gap_lower (n := 13176) (a := (8382535070721 / 10000000000000 : ℝ)) (b := (19532801371 / 12500000000000 : ℝ)) (q := (1098132265161 / 50000000000000 : ℝ))
      (E := (cell13176 ⟨7, by decide⟩).energy) (xi := (80432697922471 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13176 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13176]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13176])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13176) (a := (8382535070721 / 10000000000000 : ℝ)) (b := (19532801371 / 12500000000000 : ℝ)) (q := (1098132265161 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13176])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13176])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13176]

theorem cert13176_8 : CellCertificate 13176 (174770765719119 / 2000000000000000 : ℝ) (1594124105435359 / 1000000000000000000 : ℝ) (80432697922471 / 2500000000000000 : ℝ)
    (cell13176 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · have h := gap_lower (n := 13176) (a := (2094765882201 / 2500000000000 : ℝ)) (b := (19532801371 / 12500000000000 : ℝ)) (q := (87850743067 / 4000000000000 : ℝ))
      (E := (cell13176 ⟨8, by decide⟩).energy) (xi := (80432697922471 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13176 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13176]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13176])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13176) (a := (2094765882201 / 2500000000000 : ℝ)) (b := (19532801371 / 12500000000000 : ℝ)) (q := (87850743067 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13176])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13176])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13176]

theorem cert13176_9 : CellCertificate 13176 (174770765719119 / 2000000000000000 : ℝ) (1594124105435359 / 1000000000000000000 : ℝ) (80432697922471 / 2500000000000000 : ℝ)
    (cell13176 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · have h := gap_lower (n := 13176) (a := (83755944431729 / 100000000000000 : ℝ)) (b := (19532801371 / 12500000000000 : ℝ)) (q := (2196272565547 / 100000000000000 : ℝ))
      (E := (cell13176 ⟨9, by decide⟩).energy) (xi := (80432697922471 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13176 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13176]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13176])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13176) (a := (83755944431729 / 100000000000000 : ℝ)) (b := (19532801371 / 12500000000000 : ℝ)) (q := (2196272565547 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13176])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13176])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13176]

theorem cert13176_10 : CellCertificate 13176 (174770765719119 / 2000000000000000 : ℝ) (1594124105435359 / 1000000000000000000 : ℝ) (80432697922471 / 2500000000000000 : ℝ)
    (cell13176 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · have h := gap_lower (n := 13176) (a := (20930319525839 / 25000000000000 : ℝ)) (b := (19532801371 / 12500000000000 : ℝ)) (q := (439255312297 / 20000000000000 : ℝ))
      (E := (cell13176 ⟨10, by decide⟩).energy) (xi := (80432697922471 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13176 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13176]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13176])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13176) (a := (20930319525839 / 25000000000000 : ℝ)) (b := (19532801371 / 12500000000000 : ℝ)) (q := (439255312297 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13176])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13176])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13176]

theorem cert13176_11 : CellCertificate 13176 (174770765719119 / 2000000000000000 : ℝ) (1594124105435359 / 1000000000000000000 : ℝ) (80432697922471 / 2500000000000000 : ℝ)
    (cell13176 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · have h := gap_lower (n := 13176) (a := (83686636268177 / 100000000000000 : ℝ)) (b := (19532801371 / 12500000000000 : ℝ)) (q := (87851222831 / 4000000000000 : ℝ))
      (E := (cell13176 ⟨11, by decide⟩).energy) (xi := (80432697922471 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13176 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13176]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13176])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13176) (a := (83686636268177 / 100000000000000 : ℝ)) (b := (19532801371 / 12500000000000 : ℝ)) (q := (87851222831 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13176])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13176])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13176]

theorem cert13176_12 : CellCertificate 13176 (174770765719119 / 2000000000000000 : ℝ) (1594124105435359 / 1000000000000000000 : ℝ) (80432697922471 / 2500000000000000 : ℝ)
    (cell13176 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · have h := gap_lower (n := 13176) (a := (83652018891631 / 100000000000000 : ℝ)) (b := (19532801371 / 12500000000000 : ℝ)) (q := (43925691989 / 2000000000000 : ℝ))
      (E := (cell13176 ⟨12, by decide⟩).energy) (xi := (80432697922471 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13176 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13176]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13176])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13176) (a := (83652018891631 / 100000000000000 : ℝ)) (b := (19532801371 / 12500000000000 : ℝ)) (q := (43925691989 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13176])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13176])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13176]

theorem cert13176_13 : CellCertificate 13176 (174770765719119 / 2000000000000000 : ℝ) (1594124105435359 / 1000000000000000000 : ℝ) (80432697922471 / 2500000000000000 : ℝ)
    (cell13176 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · have h := gap_lower (n := 13176) (a := (83617425939337 / 100000000000000 : ℝ)) (b := (19532801371 / 12500000000000 : ℝ)) (q := (2196288653297 / 100000000000000 : ℝ))
      (E := (cell13176 ⟨13, by decide⟩).energy) (xi := (80432697922471 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13176 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13176]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13176])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13176) (a := (83617425939337 / 100000000000000 : ℝ)) (b := (19532801371 / 12500000000000 : ℝ)) (q := (2196288653297 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13176])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13176])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13176]

theorem cert13176_14 : CellCertificate 13176 (174770765719119 / 2000000000000000 : ℝ) (1594124105435359 / 1000000000000000000 : ℝ) (80432697922471 / 2500000000000000 : ℝ)
    (cell13176 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · have h := gap_lower (n := 13176) (a := (83582857377091 / 100000000000000 : ℝ)) (b := (19532801371 / 12500000000000 : ℝ)) (q := (1098146310747 / 50000000000000 : ℝ))
      (E := (cell13176 ⟨14, by decide⟩).energy) (xi := (80432697922471 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13176 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13176]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13176])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13176) (a := (83582857377091 / 100000000000000 : ℝ)) (b := (19532801371 / 12500000000000 : ℝ)) (q := (1098146310747 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13176])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13176])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13176]

theorem cert13176_15 : CellCertificate 13176 (174770765719119 / 2000000000000000 : ℝ) (1594124105435359 / 1000000000000000000 : ℝ) (80432697922471 / 2500000000000000 : ℝ)
    (cell13176 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · have h := gap_lower (n := 13176) (a := (83548313170867 / 100000000000000 : ℝ)) (b := (19532801371 / 12500000000000 : ℝ)) (q := (2196296683817 / 100000000000000 : ℝ))
      (E := (cell13176 ⟨15, by decide⟩).energy) (xi := (80432697922471 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13176 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13176]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13176])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13176) (a := (83548313170867 / 100000000000000 : ℝ)) (b := (19532801371 / 12500000000000 : ℝ)) (q := (2196296683817 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13176])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13176])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13176]

theorem cert13176_16 : CellCertificate 13176 (174770765719119 / 2000000000000000 : ℝ) (1594124105435359 / 1000000000000000000 : ℝ) (80432697922471 / 2500000000000000 : ℝ)
    (cell13176 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · have h := gap_lower (n := 13176) (a := (83513793286817 / 100000000000000 : ℝ)) (b := (19532801371 / 12500000000000 : ℝ)) (q := (2196300670701 / 100000000000000 : ℝ))
      (E := (cell13176 ⟨16, by decide⟩).energy) (xi := (80432697922471 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13176 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13176]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13176])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13176) (a := (83513793286817 / 100000000000000 : ℝ)) (b := (19532801371 / 12500000000000 : ℝ)) (q := (2196300670701 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13176])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13176])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13176]

theorem cert13176_17 : CellCertificate 13176 (174770765719119 / 2000000000000000 : ℝ) (1594124105435359 / 1000000000000000000 : ℝ) (80432697922471 / 2500000000000000 : ℝ)
    (cell13176 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · have h := gap_lower (n := 13176) (a := (652182013213 / 781250000000 : ℝ)) (b := (19532801371 / 12500000000000 : ℝ)) (q := (68634521979 / 3125000000000 : ℝ))
      (E := (cell13176 ⟨17, by decide⟩).energy) (xi := (80432697922471 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13176 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13176]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13176])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13176) (a := (652182013213 / 781250000000 : ℝ)) (b := (19532801371 / 12500000000000 : ℝ)) (q := (68634521979 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13176])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13176])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13176]

theorem cert13176_18 : CellCertificate 13176 (174770765719119 / 2000000000000000 : ℝ) (1594124105435359 / 1000000000000000000 : ℝ) (80432697922471 / 2500000000000000 : ℝ)
    (cell13176 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · have h := gap_lower (n := 13176) (a := (20861206587677 / 25000000000000 : ℝ)) (b := (19532801371 / 12500000000000 : ℝ)) (q := (2196308727991 / 100000000000000 : ℝ))
      (E := (cell13176 ⟨18, by decide⟩).energy) (xi := (80432697922471 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13176 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13176]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13176])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13176) (a := (20861206587677 / 25000000000000 : ℝ)) (b := (19532801371 / 12500000000000 : ℝ)) (q := (2196308727991 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13176])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13176])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13176]

theorem cert13176_19 : CellCertificate 13176 (174770765719119 / 2000000000000000 : ℝ) (1594124105435359 / 1000000000000000000 : ℝ) (80432697922471 / 2500000000000000 : ℝ)
    (cell13176 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · have h := gap_lower (n := 13176) (a := (41705189615911 / 50000000000000 : ℝ)) (b := (19532801371 / 12500000000000 : ℝ)) (q := (2196312690651 / 100000000000000 : ℝ))
      (E := (cell13176 ⟨19, by decide⟩).energy) (xi := (80432697922471 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13176 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13176]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13176])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13176) (a := (41705189615911 / 50000000000000 : ℝ)) (b := (19532801371 / 12500000000000 : ℝ)) (q := (2196312690651 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13176])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13176])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13176]

theorem cert13177_0 : CellCertificate 13177 (873827796253663 / 10000000000000000 : ℝ) (797001544663113 / 500000000000000000 : ℝ) (321705820013891 / 10000000000000000 : ℝ)
    (cell13177 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · have h := gap_lower (n := 13177) (a := (42034517660191 / 50000000000000 : ℝ)) (b := (156250417321 / 100000000000000 : ℝ)) (q := (549031498933 / 25000000000000 : ℝ))
      (E := (cell13177 ⟨0, by decide⟩).energy) (xi := (321705820013891 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13177 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13177]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13177])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13177) (a := (42034517660191 / 50000000000000 : ℝ)) (b := (156250417321 / 100000000000000 : ℝ)) (q := (549031498933 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13177])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13177])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13177]

theorem cert13177_1 : CellCertificate 13177 (873827796253663 / 10000000000000000 : ℝ) (797001544663113 / 500000000000000000 : ℝ) (321705820013891 / 10000000000000000 : ℝ)
    (cell13177 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · have h := gap_lower (n := 13177) (a := (42017073487009 / 50000000000000 : ℝ)) (b := (156250417321 / 100000000000000 : ℝ)) (q := (549032501831 / 25000000000000 : ℝ))
      (E := (cell13177 ⟨1, by decide⟩).energy) (xi := (321705820013891 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13177 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13177]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13177])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13177) (a := (42017073487009 / 50000000000000 : ℝ)) (b := (156250417321 / 100000000000000 : ℝ)) (q := (549032501831 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13177])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13177])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13177]

theorem cert13177_2 : CellCertificate 13177 (873827796253663 / 10000000000000000 : ℝ) (797001544663113 / 500000000000000000 : ℝ) (321705820013891 / 10000000000000000 : ℝ)
    (cell13177 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · have h := gap_lower (n := 13177) (a := (83999283440173 / 100000000000000 : ℝ)) (b := (156250417321 / 100000000000000 : ℝ)) (q := (2196134024487 / 100000000000000 : ℝ))
      (E := (cell13177 ⟨2, by decide⟩).energy) (xi := (321705820013891 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13177 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13177]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13177])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13177) (a := (83999283440173 / 100000000000000 : ℝ)) (b := (156250417321 / 100000000000000 : ℝ)) (q := (2196134024487 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13177])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13177])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13177]

theorem cert13177_3 : CellCertificate 13177 (873827796253663 / 10000000000000000 : ℝ) (797001544663113 / 500000000000000000 : ℝ) (321705820013891 / 10000000000000000 : ℝ)
    (cell13177 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · have h := gap_lower (n := 13177) (a := (16792888936523 / 20000000000000 : ℝ)) (b := (156250417321 / 100000000000000 : ℝ)) (q := (219613799767 / 10000000000000 : ℝ))
      (E := (cell13177 ⟨3, by decide⟩).energy) (xi := (321705820013891 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13177 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13177]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13177])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13177) (a := (16792888936523 / 20000000000000 : ℝ)) (b := (156250417321 / 100000000000000 : ℝ)) (q := (219613799767 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13177])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13177])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13177]

theorem cert13177_4 : CellCertificate 13177 (873827796253663 / 10000000000000000 : ℝ) (797001544663113 / 500000000000000000 : ℝ) (321705820013891 / 10000000000000000 : ℝ)
    (cell13177 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · have h := gap_lower (n := 13177) (a := (83929630665303 / 100000000000000 : ℝ)) (b := (156250417321 / 100000000000000 : ℝ)) (q := (2196142050819 / 100000000000000 : ℝ))
      (E := (cell13177 ⟨4, by decide⟩).energy) (xi := (321705820013891 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13177 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13177]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13177])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13177) (a := (83929630665303 / 100000000000000 : ℝ)) (b := (156250417321 / 100000000000000 : ℝ)) (q := (2196142050819 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13177])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13177])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13177]

theorem cert13177_5 : CellCertificate 13177 (873827796253663 / 10000000000000000 : ℝ) (797001544663113 / 500000000000000000 : ℝ) (321705820013891 / 10000000000000000 : ℝ)
    (cell13177 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · have h := gap_lower (n := 13177) (a := (16778968270477 / 20000000000000 : ℝ)) (b := (156250417321 / 100000000000000 : ℝ)) (q := (27451825949 / 1250000000000 : ℝ))
      (E := (cell13177 ⟨5, by decide⟩).energy) (xi := (321705820013891 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13177 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13177]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13177])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13177) (a := (16778968270477 / 20000000000000 : ℝ)) (b := (156250417321 / 100000000000000 : ℝ)) (q := (27451825949 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13177])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13177])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13177]

theorem cert13177_6 : CellCertificate 13177 (873827796253663 / 10000000000000000 : ℝ) (797001544663113 / 500000000000000000 : ℝ) (321705820013891 / 10000000000000000 : ℝ)
    (cell13177 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · have h := gap_lower (n := 13177) (a := (41930038354099 / 50000000000000 : ℝ)) (b := (156250417321 / 100000000000000 : ℝ)) (q := (2196150080509 / 100000000000000 : ℝ))
      (E := (cell13177 ⟨6, by decide⟩).energy) (xi := (321705820013891 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13177 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13177]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13177])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13177) (a := (41930038354099 / 50000000000000 : ℝ)) (b := (156250417321 / 100000000000000 : ℝ)) (q := (2196150080509 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13177])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13177])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13177]

theorem cert13177_7 : CellCertificate 13177 (873827796253663 / 10000000000000000 : ℝ) (797001544663113 / 500000000000000000 : ℝ) (321705820013891 / 10000000000000000 : ℝ)
    (cell13177 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · have h := gap_lower (n := 13177) (a := (16765067339453 / 20000000000000 : ℝ)) (b := (156250417321 / 100000000000000 : ℝ)) (q := (2196154071871 / 100000000000000 : ℝ))
      (E := (cell13177 ⟨7, by decide⟩).energy) (xi := (321705820013891 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13177 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13177]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13177])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13177) (a := (16765067339453 / 20000000000000 : ℝ)) (b := (156250417321 / 100000000000000 : ℝ)) (q := (2196154071871 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13177])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13177])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13177]

theorem cert13177_8 : CellCertificate 13177 (873827796253663 / 10000000000000000 : ℝ) (797001544663113 / 500000000000000000 : ℝ) (321705820013891 / 10000000000000000 : ℝ)
    (cell13177 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · have h := gap_lower (n := 13177) (a := (41895310642147 / 50000000000000 : ℝ)) (b := (156250417321 / 100000000000000 : ℝ)) (q := (2196158115079 / 100000000000000 : ℝ))
      (E := (cell13177 ⟨8, by decide⟩).energy) (xi := (321705820013891 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13177 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13177]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13177])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13177) (a := (41895310642147 / 50000000000000 : ℝ)) (b := (156250417321 / 100000000000000 : ℝ)) (q := (2196158115079 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13177])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13177])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13177]

theorem cert13177_9 : CellCertificate 13177 (873827796253663 / 10000000000000000 : ℝ) (797001544663113 / 500000000000000000 : ℝ) (321705820013891 / 10000000000000000 : ℝ)
    (cell13177 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · have h := gap_lower (n := 13177) (a := (41877965217089 / 50000000000000 : ℝ)) (b := (156250417321 / 100000000000000 : ℝ)) (q := (2196162100853 / 100000000000000 : ℝ))
      (E := (cell13177 ⟨9, by decide⟩).energy) (xi := (321705820013891 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13177 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13177]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13177])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13177) (a := (41877965217089 / 50000000000000 : ℝ)) (b := (156250417321 / 100000000000000 : ℝ)) (q := (2196162100853 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13177])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13177])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13177]

theorem cert13177_10 : CellCertificate 13177 (873827796253663 / 10000000000000000 : ℝ) (797001544663113 / 500000000000000000 : ℝ) (321705820013891 / 10000000000000000 : ℝ)
    (cell13177 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · have h := gap_lower (n := 13177) (a := (83721264111993 / 100000000000000 : ℝ)) (b := (156250417321 / 100000000000000 : ℝ)) (q := (274520768979 / 12500000000000 : ℝ))
      (E := (cell13177 ⟨10, by decide⟩).energy) (xi := (321705820013891 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13177 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13177]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13177])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13177) (a := (83721264111993 / 100000000000000 : ℝ)) (b := (156250417321 / 100000000000000 : ℝ)) (q := (274520768979 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13177])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13177])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13177]

theorem cert13177_11 : CellCertificate 13177 (873827796253663 / 10000000000000000 : ℝ) (797001544663113 / 500000000000000000 : ℝ) (321705820013891 / 10000000000000000 : ℝ)
    (cell13177 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · have h := gap_lower (n := 13177) (a := (83686622282997 / 100000000000000 : ℝ)) (b := (156250417321 / 100000000000000 : ℝ)) (q := (1098085079071 / 50000000000000 : ℝ))
      (E := (cell13177 ⟨11, by decide⟩).energy) (xi := (321705820013891 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13177 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13177]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13177])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13177) (a := (83686622282997 / 100000000000000 : ℝ)) (b := (156250417321 / 100000000000000 : ℝ)) (q := (1098085079071 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13177])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13177])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13177]

theorem cert13177_12 : CellCertificate 13177 (873827796253663 / 10000000000000000 : ℝ) (797001544663113 / 500000000000000000 : ℝ) (321705820013891 / 10000000000000000 : ℝ)
    (cell13177 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · have h := gap_lower (n := 13177) (a := (83652004912629 / 100000000000000 : ℝ)) (b := (156250417321 / 100000000000000 : ℝ)) (q := (2196174125747 / 100000000000000 : ℝ))
      (E := (cell13177 ⟨12, by decide⟩).energy) (xi := (321705820013891 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13177 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13177]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13177])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13177) (a := (83652004912629 / 100000000000000 : ℝ)) (b := (156250417321 / 100000000000000 : ℝ)) (q := (2196174125747 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13177])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13177])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13177]

theorem cert13177_13 : CellCertificate 13177 (873827796253663 / 10000000000000000 : ℝ) (797001544663113 / 500000000000000000 : ℝ) (321705820013891 / 10000000000000000 : ℝ)
    (cell13177 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · have h := gap_lower (n := 13177) (a := (20904352991627 / 25000000000000 : ℝ)) (b := (156250417321 / 100000000000000 : ℝ)) (q := (2196178176683 / 100000000000000 : ℝ))
      (E := (cell13177 ⟨13, by decide⟩).energy) (xi := (321705820013891 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13177 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13177]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13177])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13177) (a := (20904352991627 / 25000000000000 : ℝ)) (b := (156250417321 / 100000000000000 : ℝ)) (q := (2196178176683 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13177])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13177])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13177]

theorem cert13177_14 : CellCertificate 13177 (873827796253663 / 10000000000000000 : ℝ) (797001544663113 / 500000000000000000 : ℝ) (321705820013891 / 10000000000000000 : ℝ)
    (cell13177 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · have h := gap_lower (n := 13177) (a := (83582843410429 / 100000000000000 : ℝ)) (b := (156250417321 / 100000000000000 : ℝ)) (q := (10980911001 / 500000000000 : ℝ))
      (E := (cell13177 ⟨14, by decide⟩).energy) (xi := (321705820013891 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13177 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13177]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13177])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13177) (a := (83582843410429 / 100000000000000 : ℝ)) (b := (156250417321 / 100000000000000 : ℝ)) (q := (10980911001 / 500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13177])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13177])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13177]

theorem cert13177_15 : CellCertificate 13177 (873827796253663 / 10000000000000000 : ℝ) (797001544663113 / 500000000000000000 : ℝ) (321705820013891 / 10000000000000000 : ℝ)
    (cell13177 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · have h := gap_lower (n := 13177) (a := (83548299210367 / 100000000000000 : ℝ)) (b := (156250417321 / 100000000000000 : ℝ)) (q := (2196186201523 / 100000000000000 : ℝ))
      (E := (cell13177 ⟨15, by decide⟩).energy) (xi := (321705820013891 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13177 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13177]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13177])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13177) (a := (83548299210367 / 100000000000000 : ℝ)) (b := (156250417321 / 100000000000000 : ℝ)) (q := (2196186201523 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13177])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13177])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13177]

theorem cert13177_16 : CellCertificate 13177 (873827796253663 / 10000000000000000 : ℝ) (797001544663113 / 500000000000000000 : ℝ) (321705820013891 / 10000000000000000 : ℝ)
    (cell13177 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · have h := gap_lower (n := 13177) (a := (83513779332473 / 100000000000000 : ℝ)) (b := (156250417321 / 100000000000000 : ℝ)) (q := (1098095092819 / 50000000000000 : ℝ))
      (E := (cell13177 ⟨16, by decide⟩).energy) (xi := (321705820013891 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13177 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13177]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13177])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13177) (a := (83513779332473 / 100000000000000 : ℝ)) (b := (156250417321 / 100000000000000 : ℝ)) (q := (1098095092819 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13177])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13177])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13177]

theorem cert13177_17 : CellCertificate 13177 (873827796253663 / 10000000000000000 : ℝ) (797001544663113 / 500000000000000000 : ℝ) (321705820013891 / 10000000000000000 : ℝ)
    (cell13177 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · have h := gap_lower (n := 13177) (a := (83479283743071 / 100000000000000 : ℝ)) (b := (156250417321 / 100000000000000 : ℝ)) (q := (2196194215541 / 100000000000000 : ℝ))
      (E := (cell13177 ⟨17, by decide⟩).energy) (xi := (321705820013891 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13177 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13177]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13177])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13177) (a := (83479283743071 / 100000000000000 : ℝ)) (b := (156250417321 / 100000000000000 : ℝ)) (q := (2196194215541 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13177])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13177])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13177]

theorem cert13177_18 : CellCertificate 13177 (873827796253663 / 10000000000000000 : ℝ) (797001544663113 / 500000000000000000 : ℝ) (321705820013891 / 10000000000000000 : ℝ)
    (cell13177 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · have h := gap_lower (n := 13177) (a := (83444812408661 / 100000000000000 : ℝ)) (b := (156250417321 / 100000000000000 : ℝ)) (q := (2196198237527 / 100000000000000 : ℝ))
      (E := (cell13177 ⟨18, by decide⟩).energy) (xi := (321705820013891 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13177 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13177]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13177])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13177) (a := (83444812408661 / 100000000000000 : ℝ)) (b := (156250417321 / 100000000000000 : ℝ)) (q := (2196198237527 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13177])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13177])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13177]

theorem cert13177_19 : CellCertificate 13177 (873827796253663 / 10000000000000000 : ℝ) (797001544663113 / 500000000000000000 : ℝ) (321705820013891 / 10000000000000000 : ℝ)
    (cell13177 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · have h := gap_lower (n := 13177) (a := (16682073059183 / 20000000000000 : ℝ)) (b := (156250417321 / 100000000000000 : ℝ)) (q := (1098101127929 / 50000000000000 : ℝ))
      (E := (cell13177 ⟨19, by decide⟩).energy) (xi := (321705820013891 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13177 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13177]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13177])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13177) (a := (16682073059183 / 20000000000000 : ℝ)) (b := (156250417321 / 100000000000000 : ℝ)) (q := (1098101127929 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13177])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13177])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13177]

theorem cert13178_0 : CellCertificate 13178 (218450441922873 / 2500000000000000 : ℝ) (99617630724331 / 62500000000000000 : ℝ) (160840426119281 / 5000000000000000 : ℝ)
    (cell13178 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · have h := gap_lower (n := 13178) (a := (42034510634509 / 50000000000000 : ℝ)) (b := (156238425521 / 100000000000000 : ℝ)) (q := (274501944551 / 12500000000000 : ℝ))
      (E := (cell13178 ⟨0, by decide⟩).energy) (xi := (160840426119281 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13178 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13178]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13178])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13178) (a := (42034510634509 / 50000000000000 : ℝ)) (b := (156238425521 / 100000000000000 : ℝ)) (q := (274501944551 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13178])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13178])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13178]

theorem cert13178_1 : CellCertificate 13178 (218450441922873 / 2500000000000000 : ℝ) (99617630724331 / 62500000000000000 : ℝ) (160840426119281 / 5000000000000000 : ℝ)
    (cell13178 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · have h := gap_lower (n := 13178) (a := (21008533232223 / 25000000000000 : ℝ)) (b := (156238425521 / 100000000000000 : ℝ)) (q := (2196019564527 / 100000000000000 : ℝ))
      (E := (cell13178 ⟨1, by decide⟩).energy) (xi := (160840426119281 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13178 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13178]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13178])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13178) (a := (21008533232223 / 25000000000000 : ℝ)) (b := (156238425521 / 100000000000000 : ℝ)) (q := (2196019564527 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13178])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13178])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13178]

theorem cert13178_2 : CellCertificate 13178 (218450441922873 / 2500000000000000 : ℝ) (99617630724331 / 62500000000000000 : ℝ) (160840426119281 / 5000000000000000 : ℝ)
    (cell13178 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · have h := gap_lower (n := 13178) (a := (83999269401279 / 100000000000000 : ℝ)) (b := (156238425521 / 100000000000000 : ℝ)) (q := (439204715653 / 20000000000000 : ℝ))
      (E := (cell13178 ⟨2, by decide⟩).energy) (xi := (160840426119281 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13178 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13178]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13178])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13178) (a := (83999269401279 / 100000000000000 : ℝ)) (b := (156238425521 / 100000000000000 : ℝ)) (q := (439204715653 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13178])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13178])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13178]

theorem cert13178_3 : CellCertificate 13178 (218450441922873 / 2500000000000000 : ℝ) (99617630724331 / 62500000000000000 : ℝ) (160840426119281 / 5000000000000000 : ℝ)
    (cell13178 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · have h := gap_lower (n := 13178) (a := (20991107662487 / 25000000000000 : ℝ)) (b := (156238425521 / 100000000000000 : ℝ)) (q := (439205521199 / 20000000000000 : ℝ))
      (E := (cell13178 ⟨3, by decide⟩).energy) (xi := (160840426119281 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13178 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13178]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13178])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13178) (a := (20991107662487 / 25000000000000 : ℝ)) (b := (156238425521 / 100000000000000 : ℝ)) (q := (439205521199 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13178])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13178])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13178]

theorem cert13178_4 : CellCertificate 13178 (218450441922873 / 2500000000000000 : ℝ) (99617630724331 / 62500000000000000 : ℝ) (160840426119281 / 5000000000000000 : ℝ)
    (cell13178 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · have h := gap_lower (n := 13178) (a := (83929616638857 / 100000000000000 : ℝ)) (b := (156238425521 / 100000000000000 : ℝ)) (q := (2196031597887 / 100000000000000 : ℝ))
      (E := (cell13178 ⟨4, by decide⟩).energy) (xi := (160840426119281 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13178 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13178]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13178])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13178) (a := (83929616638857 / 100000000000000 : ℝ)) (b := (156238425521 / 100000000000000 : ℝ)) (q := (2196031597887 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13178])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13178])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13178]

theorem cert13178_5 : CellCertificate 13178 (218450441922873 / 2500000000000000 : ℝ) (99617630724331 / 62500000000000000 : ℝ) (160840426119281 / 5000000000000000 : ℝ)
    (cell13178 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · have h := gap_lower (n := 13178) (a := (16778965466431 / 20000000000000 : ℝ)) (b := (156238425521 / 100000000000000 : ℝ)) (q := (2196035619703 / 100000000000000 : ℝ))
      (E := (cell13178 ⟨5, by decide⟩).energy) (xi := (160840426119281 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13178 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13178]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13178])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13178) (a := (16778965466431 / 20000000000000 : ℝ)) (b := (156238425521 / 100000000000000 : ℝ)) (q := (2196035619703 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13178])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13178])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13178]

theorem cert13178_6 : CellCertificate 13178 (218450441922873 / 2500000000000000 : ℝ) (99617630724331 / 62500000000000000 : ℝ) (160840426119281 / 5000000000000000 : ℝ)
    (cell13178 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · have h := gap_lower (n := 13178) (a := (41930031347089 / 50000000000000 : ℝ)) (b := (156238425521 / 100000000000000 : ℝ)) (q := (439207924211 / 20000000000000 : ℝ))
      (E := (cell13178 ⟨6, by decide⟩).energy) (xi := (160840426119281 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13178 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13178]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13178])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13178) (a := (41930031347089 / 50000000000000 : ℝ)) (b := (156238425521 / 100000000000000 : ℝ)) (q := (439207924211 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13178])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13178])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13178]

theorem cert13178_7 : CellCertificate 13178 (218450441922873 / 2500000000000000 : ℝ) (99617630724331 / 62500000000000000 : ℝ) (160840426119281 / 5000000000000000 : ℝ)
    (cell13178 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · have h := gap_lower (n := 13178) (a := (83825322689449 / 100000000000000 : ℝ)) (b := (156238425521 / 100000000000000 : ℝ)) (q := (2196043667247 / 100000000000000 : ℝ))
      (E := (cell13178 ⟨7, by decide⟩).energy) (xi := (160840426119281 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13178 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13178]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13178])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13178) (a := (83825322689449 / 100000000000000 : ℝ)) (b := (156238425521 / 100000000000000 : ℝ)) (q := (2196043667247 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13178])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13178])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13178]

theorem cert13178_8 : CellCertificate 13178 (218450441922873 / 2500000000000000 : ℝ) (99617630724331 / 62500000000000000 : ℝ) (160840426119281 / 5000000000000000 : ℝ)
    (cell13178 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · have h := gap_lower (n := 13178) (a := (20947651820669 / 25000000000000 : ℝ)) (b := (156238425521 / 100000000000000 : ℝ)) (q := (2196047649293 / 100000000000000 : ℝ))
      (E := (cell13178 ⟨8, by decide⟩).energy) (xi := (160840426119281 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13178 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13178]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13178])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13178) (a := (20947651820669 / 25000000000000 : ℝ)) (b := (156238425521 / 100000000000000 : ℝ)) (q := (2196047649293 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13178])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13178])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13178]

theorem cert13178_9 : CellCertificate 13178 (218450441922873 / 2500000000000000 : ℝ) (99617630724331 / 62500000000000000 : ℝ) (160840426119281 / 5000000000000000 : ℝ)
    (cell13178 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · have h := gap_lower (n := 13178) (a := (41877958219377 / 50000000000000 : ℝ)) (b := (156238425521 / 100000000000000 : ℝ)) (q := (549012922509 / 25000000000000 : ℝ))
      (E := (cell13178 ⟨9, by decide⟩).energy) (xi := (160840426119281 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13178 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13178]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13178])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13178) (a := (41877958219377 / 50000000000000 : ℝ)) (b := (156238425521 / 100000000000000 : ℝ)) (q := (549012922509 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13178])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13178])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13178]

theorem cert13178_10 : CellCertificate 13178 (218450441922873 / 2500000000000000 : ℝ) (99617630724331 / 62500000000000000 : ℝ) (160840426119281 / 5000000000000000 : ℝ)
    (cell13178 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · have h := gap_lower (n := 13178) (a := (83721250122757 / 100000000000000 : ℝ)) (b := (156238425521 / 100000000000000 : ℝ)) (q := (2196055679899 / 100000000000000 : ℝ))
      (E := (cell13178 ⟨10, by decide⟩).energy) (xi := (160840426119281 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13178 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13178]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13178])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13178) (a := (83721250122757 / 100000000000000 : ℝ)) (b := (156238425521 / 100000000000000 : ℝ)) (q := (2196055679899 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13178])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13178])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13178]

theorem cert13178_11 : CellCertificate 13178 (218450441922873 / 2500000000000000 : ℝ) (99617630724331 / 62500000000000000 : ℝ) (160840426119281 / 5000000000000000 : ℝ)
    (cell13178 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · have h := gap_lower (n := 13178) (a := (83686608299943 / 100000000000000 : ℝ)) (b := (156238425521 / 100000000000000 : ℝ)) (q := (1098029841603 / 50000000000000 : ℝ))
      (E := (cell13178 ⟨11, by decide⟩).energy) (xi := (160840426119281 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13178 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13178]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13178])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13178) (a := (83686608299943 / 100000000000000 : ℝ)) (b := (156238425521 / 100000000000000 : ℝ)) (q := (1098029841603 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13178])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13178])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13178]

theorem cert13178_12 : CellCertificate 13178 (218450441922873 / 2500000000000000 : ℝ) (99617630724331 / 62500000000000000 : ℝ) (160840426119281 / 5000000000000000 : ℝ)
    (cell13178 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · have h := gap_lower (n := 13178) (a := (10456498866969 / 12500000000000 : ℝ)) (b := (156238425521 / 100000000000000 : ℝ)) (q := (2196063705991 / 100000000000000 : ℝ))
      (E := (cell13178 ⟨12, by decide⟩).energy) (xi := (160840426119281 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13178 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13178]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13178])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13178) (a := (10456498866969 / 12500000000000 : ℝ)) (b := (156238425521 / 100000000000000 : ℝ)) (q := (2196063705991 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13178])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13178])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13178]

theorem cert13178_13 : CellCertificate 13178 (218450441922873 / 2500000000000000 : ℝ) (99617630724331 / 62500000000000000 : ℝ) (160840426119281 / 5000000000000000 : ℝ)
    (cell13178 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · have h := gap_lower (n := 13178) (a := (41808698997901 / 50000000000000 : ℝ)) (b := (156238425521 / 100000000000000 : ℝ)) (q := (2196067754043 / 100000000000000 : ℝ))
      (E := (cell13178 ⟨13, by decide⟩).energy) (xi := (160840426119281 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13178 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13178]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13178])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13178) (a := (41808698997901 / 50000000000000 : ℝ)) (b := (156238425521 / 100000000000000 : ℝ)) (q := (2196067754043 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13178])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13178])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13178]

theorem cert13178_14 : CellCertificate 13178 (218450441922873 / 2500000000000000 : ℝ) (99617630724331 / 62500000000000000 : ℝ) (160840426119281 / 5000000000000000 : ℝ)
    (cell13178 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · have h := gap_lower (n := 13178) (a := (83582829445889 / 100000000000000 : ℝ)) (b := (156238425521 / 100000000000000 : ℝ)) (q := (2196071716537 / 100000000000000 : ℝ))
      (E := (cell13178 ⟨14, by decide⟩).energy) (xi := (160840426119281 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13178 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13178]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13178])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13178) (a := (83582829445889 / 100000000000000 : ℝ)) (b := (156238425521 / 100000000000000 : ℝ)) (q := (2196071716537 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13178])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13178])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13178]

theorem cert13178_15 : CellCertificate 13178 (218450441922873 / 2500000000000000 : ℝ) (99617630724331 / 62500000000000000 : ℝ) (160840426119281 / 5000000000000000 : ℝ)
    (cell13178 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · have h := gap_lower (n := 13178) (a := (20887071312997 / 25000000000000 : ℝ)) (b := (156238425521 / 100000000000000 : ℝ)) (q := (2196075773251 / 100000000000000 : ℝ))
      (E := (cell13178 ⟨15, by decide⟩).energy) (xi := (160840426119281 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13178 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13178]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13178])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13178) (a := (20887071312997 / 25000000000000 : ℝ)) (b := (156238425521 / 100000000000000 : ℝ)) (q := (2196075773251 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13178])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13178])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13178]

theorem cert13178_16 : CellCertificate 13178 (218450441922873 / 2500000000000000 : ℝ) (99617630724331 / 62500000000000000 : ℝ) (160840426119281 / 5000000000000000 : ℝ)
    (cell13178 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · have h := gap_lower (n := 13178) (a := (83513765380249 / 100000000000000 : ℝ)) (b := (156238425521 / 100000000000000 : ℝ)) (q := (109803987731 / 5000000000000 : ℝ))
      (E := (cell13178 ⟨16, by decide⟩).energy) (xi := (160840426119281 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13178 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13178]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13178])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13178) (a := (83513765380249 / 100000000000000 : ℝ)) (b := (156238425521 / 100000000000000 : ℝ)) (q := (109803987731 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13178])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13178])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13178]

theorem cert13178_17 : CellCertificate 13178 (218450441922873 / 2500000000000000 : ℝ) (99617630724331 / 62500000000000000 : ℝ) (160840426119281 / 5000000000000000 : ℝ)
    (cell13178 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · have h := gap_lower (n := 13178) (a := (83479269796997 / 100000000000000 : ℝ)) (b := (156238425521 / 100000000000000 : ℝ)) (q := (87843351273 / 4000000000000 : ℝ))
      (E := (cell13178 ⟨17, by decide⟩).energy) (xi := (160840426119281 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13178 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13178]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13178])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13178) (a := (83479269796997 / 100000000000000 : ℝ)) (b := (156238425521 / 100000000000000 : ℝ)) (q := (87843351273 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13178])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13178])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13178]

theorem cert13178_18 : CellCertificate 13178 (218450441922873 / 2500000000000000 : ℝ) (99617630724331 / 62500000000000000 : ℝ) (160840426119281 / 5000000000000000 : ℝ)
    (cell13178 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · have h := gap_lower (n := 13178) (a := (20861199617183 / 25000000000000 : ℝ)) (b := (156238425521 / 100000000000000 : ℝ)) (q := (1098043900579 / 50000000000000 : ℝ))
      (E := (cell13178 ⟨18, by decide⟩).energy) (xi := (160840426119281 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13178 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13178]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13178])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13178) (a := (20861199617183 / 25000000000000 : ℝ)) (b := (156238425521 / 100000000000000 : ℝ)) (q := (1098043900579 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13178])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13178])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13178]

theorem cert13178_19 : CellCertificate 13178 (218450441922873 / 2500000000000000 : ℝ) (99617630724331 / 62500000000000000 : ℝ) (160840426119281 / 5000000000000000 : ℝ)
    (cell13178 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · have h := gap_lower (n := 13178) (a := (667282810897 / 800000000000 : ℝ)) (b := (156238425521 / 100000000000000 : ℝ)) (q := (549022954221 / 25000000000000 : ℝ))
      (E := (cell13178 ⟨19, by decide⟩).energy) (xi := (160840426119281 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13178 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13178]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13178])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13178) (a := (667282810897 / 800000000000 : ℝ)) (b := (156238425521 / 100000000000000 : ℝ)) (q := (549022954221 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13178])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13178])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13178]

theorem cert13179_0 : CellCertificate 13179 (43688787145411 / 500000000000000 : ℝ) (796880556110193 / 500000000000000000 : ℝ) (40206986045367 / 1250000000000000 : ℝ)
    (cell13179 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · have h := gap_lower (n := 13179) (a := (84069007219789 / 100000000000000 : ℝ)) (b := (9764152223 / 6250000000000 : ℝ)) (q := (1097952556443 / 50000000000000 : ℝ))
      (E := (cell13179 ⟨0, by decide⟩).energy) (xi := (40206986045367 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13179 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13179]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13179])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13179) (a := (84069007219789 / 100000000000000 : ℝ)) (b := (9764152223 / 6250000000000 : ℝ)) (q := (1097952556443 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13179])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13179])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13179]

theorem cert13179_1 : CellCertificate 13179 (43688787145411 / 500000000000000 : ℝ) (796880556110193 / 500000000000000000 : ℝ) (40206986045367 / 1250000000000000 : ℝ)
    (cell13179 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · have h := gap_lower (n := 13179) (a := (840341188859 / 1000000000000 : ℝ)) (b := (9764152223 / 6250000000000 : ℝ)) (q := (1097954558767 / 50000000000000 : ℝ))
      (E := (cell13179 ⟨1, by decide⟩).energy) (xi := (40206986045367 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13179 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13179]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13179])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13179) (a := (840341188859 / 1000000000000 : ℝ)) (b := (9764152223 / 6250000000000 : ℝ)) (q := (1097954558767 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13179])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13179])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13179]

theorem cert13179_2 : CellCertificate 13179 (43688787145411 / 500000000000000 : ℝ) (796880556110193 / 500000000000000000 : ℝ) (40206986045367 / 1250000000000000 : ℝ)
    (cell13179 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · have h := gap_lower (n := 13179) (a := (83999255364519 / 100000000000000 : ℝ)) (b := (9764152223 / 6250000000000 : ℝ)) (q := (1097956563923 / 50000000000000 : ℝ))
      (E := (cell13179 ⟨2, by decide⟩).energy) (xi := (40206986045367 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13179 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13179]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13179])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13179) (a := (83999255364519 / 100000000000000 : ℝ)) (b := (9764152223 / 6250000000000 : ℝ)) (q := (1097956563923 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13179])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13179])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13179]

theorem cert13179_3 : CellCertificate 13179 (43688787145411 / 500000000000000 : ℝ) (796880556110193 / 500000000000000000 : ℝ) (40206986045367 / 1250000000000000 : ℝ)
    (cell13179 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · have h := gap_lower (n := 13179) (a := (83964416619413 / 100000000000000 : ℝ)) (b := (9764152223 / 6250000000000 : ℝ)) (q := (10979585761 / 500000000000 : ℝ))
      (E := (cell13179 ⟨3, by decide⟩).energy) (xi := (40206986045367 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13179 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13179]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13179])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13179) (a := (83964416619413 / 100000000000000 : ℝ)) (b := (9764152223 / 6250000000000 : ℝ)) (q := (10979585761 / 500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13179])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13179])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13179]

theorem cert13179_4 : CellCertificate 13179 (43688787145411 / 500000000000000 : ℝ) (796880556110193 / 500000000000000000 : ℝ) (40206986045367 / 1250000000000000 : ℝ)
    (cell13179 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · have h := gap_lower (n := 13179) (a := (41964801307271 / 50000000000000 : ℝ)) (b := (9764152223 / 6250000000000 : ℝ)) (q := (2195921198711 / 100000000000000 : ℝ))
      (E := (cell13179 ⟨4, by decide⟩).energy) (xi := (40206986045367 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13179 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13179]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13179])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13179) (a := (41964801307271 / 50000000000000 : ℝ)) (b := (9764152223 / 6250000000000 : ℝ)) (q := (2195921198711 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13179])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13179])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13179]

theorem cert13179_5 : CellCertificate 13179 (43688787145411 / 500000000000000 : ℝ) (796880556110193 / 500000000000000000 : ℝ) (40206986045367 / 1250000000000000 : ℝ)
    (cell13179 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · have h := gap_lower (n := 13179) (a := (41947406657027 / 50000000000000 : ℝ)) (b := (9764152223 / 6250000000000 : ℝ)) (q := (548981304317 / 25000000000000 : ℝ))
      (E := (cell13179 ⟨5, by decide⟩).energy) (xi := (40206986045367 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13179 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13179]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13179])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13179) (a := (41947406657027 / 50000000000000 : ℝ)) (b := (9764152223 / 6250000000000 : ℝ)) (q := (548981304317 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13179])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13179])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13179]

theorem cert13179_6 : CellCertificate 13179 (43688787145411 / 500000000000000 : ℝ) (796880556110193 / 500000000000000000 : ℝ) (40206986045367 / 1250000000000000 : ℝ)
    (cell13179 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · have h := gap_lower (n := 13179) (a := (41930024341143 / 50000000000000 : ℝ)) (b := (9764152223 / 6250000000000 : ℝ)) (q := (2195929215407 / 100000000000000 : ℝ))
      (E := (cell13179 ⟨6, by decide⟩).energy) (xi := (40206986045367 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13179 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13179]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13179])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13179) (a := (41930024341143 / 50000000000000 : ℝ)) (b := (9764152223 / 6250000000000 : ℝ)) (q := (2195929215407 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13179])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13179])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13179]

theorem cert13179_7 : CellCertificate 13179 (43688787145411 / 500000000000000 : ℝ) (796880556110193 / 500000000000000000 : ℝ) (40206986045367 / 1250000000000000 : ℝ)
    (cell13179 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · have h := gap_lower (n := 13179) (a := (83825308683761 / 100000000000000 : ℝ)) (b := (9764152223 / 6250000000000 : ℝ)) (q := (548983300103 / 25000000000000 : ℝ))
      (E := (cell13179 ⟨7, by decide⟩).energy) (xi := (40206986045367 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13179 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13179]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13179])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13179) (a := (83825308683761 / 100000000000000 : ℝ)) (b := (9764152223 / 6250000000000 : ℝ)) (q := (548983300103 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13179])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13179])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13179]

theorem cert13179_8 : CellCertificate 13179 (43688787145411 / 500000000000000 : ℝ) (796880556110193 / 500000000000000000 : ℝ) (40206986045367 / 1250000000000000 : ℝ)
    (cell13179 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · have h := gap_lower (n := 13179) (a := (41895296641593 / 50000000000000 : ℝ)) (b := (9764152223 / 6250000000000 : ℝ)) (q := (2195937237359 / 100000000000000 : ℝ))
      (E := (cell13179 ⟨8, by decide⟩).energy) (xi := (40206986045367 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13179 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13179]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13179])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13179) (a := (41895296641593 / 50000000000000 : ℝ)) (b := (9764152223 / 6250000000000 : ℝ)) (q := (2195937237359 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13179])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13179])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13179]

theorem cert13179_9 : CellCertificate 13179 (43688787145411 / 500000000000000 : ℝ) (796880556110193 / 500000000000000000 : ℝ) (40206986045367 / 1250000000000000 : ℝ)
    (cell13179 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · have h := gap_lower (n := 13179) (a := (5234743902841 / 6250000000000 : ℝ)) (b := (9764152223 / 6250000000000 : ℝ)) (q := (219594127503 / 10000000000000 : ℝ))
      (E := (cell13179 ⟨9, by decide⟩).energy) (xi := (40206986045367 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13179 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13179]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13179])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13179) (a := (5234743902841 / 6250000000000 : ℝ)) (b := (9764152223 / 6250000000000 : ℝ)) (q := (219594127503 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13179])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13179])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13179]

theorem cert13179_10 : CellCertificate 13179 (43688787145411 / 500000000000000 : ℝ) (796880556110193 / 500000000000000000 : ℝ) (40206986045367 / 1250000000000000 : ℝ)
    (cell13179 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · have h := gap_lower (n := 13179) (a := (41860618067823 / 50000000000000 : ℝ)) (b := (9764152223 / 6250000000000 : ℝ)) (q := (2195945261867 / 100000000000000 : ℝ))
      (E := (cell13179 ⟨10, by decide⟩).energy) (xi := (40206986045367 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13179 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13179]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13179])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13179) (a := (41860618067823 / 50000000000000 : ℝ)) (b := (9764152223 / 6250000000000 : ℝ)) (q := (2195945261867 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13179])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13179])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13179]

theorem cert13179_11 : CellCertificate 13179 (43688787145411 / 500000000000000 : ℝ) (796880556110193 / 500000000000000000 : ℝ) (40206986045367 / 1250000000000000 : ℝ)
    (cell13179 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · have h := gap_lower (n := 13179) (a := (41843297159507 / 50000000000000 : ℝ)) (b := (9764152223 / 6250000000000 : ℝ)) (q := (439189852439 / 20000000000000 : ℝ))
      (E := (cell13179 ⟨11, by decide⟩).energy) (xi := (40206986045367 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13179 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13179]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13179])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13179) (a := (41843297159507 / 50000000000000 : ℝ)) (b := (9764152223 / 6250000000000 : ℝ)) (q := (439189852439 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13179])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13179])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13179]

theorem cert13179_12 : CellCertificate 13179 (43688787145411 / 500000000000000 : ℝ) (796880556110193 / 500000000000000000 : ℝ) (40206986045367 / 1250000000000000 : ℝ)
    (cell13179 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · have h := gap_lower (n := 13179) (a := (83651976960999 / 100000000000000 : ℝ)) (b := (9764152223 / 6250000000000 : ℝ)) (q := (2195953282049 / 100000000000000 : ℝ))
      (E := (cell13179 ⟨12, by decide⟩).energy) (xi := (40206986045367 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13179 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13179]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13179])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13179) (a := (83651976960999 / 100000000000000 : ℝ)) (b := (9764152223 / 6250000000000 : ℝ)) (q := (2195953282049 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13179])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13179])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13179]

theorem cert13179_13 : CellCertificate 13179 (43688787145411 / 500000000000000 : ℝ) (796880556110193 / 500000000000000000 : ℝ) (40206986045367 / 1250000000000000 : ℝ)
    (cell13179 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · have h := gap_lower (n := 13179) (a := (83617384027219 / 100000000000000 : ℝ)) (b := (9764152223 / 6250000000000 : ℝ)) (q := (137247332951 / 6250000000000 : ℝ))
      (E := (cell13179 ⟨13, by decide⟩).energy) (xi := (40206986045367 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13179 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13179]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13179])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13179) (a := (83617384027219 / 100000000000000 : ℝ)) (b := (9764152223 / 6250000000000 : ℝ)) (q := (137247332951 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13179])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13179])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13179]

theorem cert13179_14 : CellCertificate 13179 (43688787145411 / 500000000000000 : ℝ) (796880556110193 / 500000000000000000 : ℝ) (40206986045367 / 1250000000000000 : ℝ)
    (cell13179 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · have h := gap_lower (n := 13179) (a := (5223925967717 / 6250000000000 : ℝ)) (b := (9764152223 / 6250000000000 : ℝ)) (q := (1097980672527 / 50000000000000 : ℝ))
      (E := (cell13179 ⟨14, by decide⟩).energy) (xi := (40206986045367 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13179 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13179]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13179])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13179) (a := (5223925967717 / 6250000000000 : ℝ)) (b := (9764152223 / 6250000000000 : ℝ)) (q := (1097980672527 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13179])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13179])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13179]

theorem cert13179_15 : CellCertificate 13179 (43688787145411 / 500000000000000 : ℝ) (796880556110193 / 500000000000000000 : ℝ) (40206986045367 / 1250000000000000 : ℝ)
    (cell13179 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · have h := gap_lower (n := 13179) (a := (8354827129573 / 10000000000000 : ℝ)) (b := (9764152223 / 6250000000000 : ℝ)) (q := (1097982670397 / 50000000000000 : ℝ))
      (E := (cell13179 ⟨15, by decide⟩).energy) (xi := (40206986045367 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13179 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13179]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13179])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13179) (a := (8354827129573 / 10000000000000 : ℝ)) (b := (9764152223 / 6250000000000 : ℝ)) (q := (1097982670397 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13179])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13179])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13179]

theorem cert13179_16 : CellCertificate 13179 (43688787145411 / 500000000000000 : ℝ) (796880556110193 / 500000000000000000 : ℝ) (40206986045367 / 1250000000000000 : ℝ)
    (cell13179 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · have h := gap_lower (n := 13179) (a := (16702750286029 / 20000000000000 : ℝ)) (b := (9764152223 / 6250000000000 : ℝ)) (q := (43919387553 / 2000000000000 : ℝ))
      (E := (cell13179 ⟨16, by decide⟩).energy) (xi := (40206986045367 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13179 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13179]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13179])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13179) (a := (16702750286029 / 20000000000000 : ℝ)) (b := (9764152223 / 6250000000000 : ℝ)) (q := (43919387553 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13179])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13179])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13179]

theorem cert13179_17 : CellCertificate 13179 (43688787145411 / 500000000000000 : ℝ) (796880556110193 / 500000000000000000 : ℝ) (40206986045367 / 1250000000000000 : ℝ)
    (cell13179 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · have h := gap_lower (n := 13179) (a := (41739627926521 / 50000000000000 : ℝ)) (b := (9764152223 / 6250000000000 : ℝ)) (q := (1097986671963 / 50000000000000 : ℝ))
      (E := (cell13179 ⟨17, by decide⟩).energy) (xi := (40206986045367 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13179 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13179]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13179])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13179) (a := (41739627926521 / 50000000000000 : ℝ)) (b := (9764152223 / 6250000000000 : ℝ)) (q := (1097986671963 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13179])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13179])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13179]

theorem cert13179_18 : CellCertificate 13179 (43688787145411 / 500000000000000 : ℝ) (796880556110193 / 500000000000000000 : ℝ) (40206986045367 / 1250000000000000 : ℝ)
    (cell13179 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · have h := gap_lower (n := 13179) (a := (83444784530921 / 100000000000000 : ℝ)) (b := (9764152223 / 6250000000000 : ℝ)) (q := (2195977360607 / 100000000000000 : ℝ))
      (E := (cell13179 ⟨18, by decide⟩).energy) (xi := (40206986045367 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13179 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13179]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13179])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13179) (a := (83444784530921 / 100000000000000 : ℝ)) (b := (9764152223 / 6250000000000 : ℝ)) (q := (2195977360607 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13179])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13179])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13179]

theorem cert13179_19 : CellCertificate 13179 (43688787145411 / 500000000000000 : ℝ) (796880556110193 / 500000000000000000 : ℝ) (40206986045367 / 1250000000000000 : ℝ)
    (cell13179 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · have h := gap_lower (n := 13179) (a := (20852584357613 / 25000000000000 : ℝ)) (b := (9764152223 / 6250000000000 : ℝ)) (q := (2195981373729 / 100000000000000 : ℝ))
      (E := (cell13179 ⟨19, by decide⟩).energy) (xi := (40206986045367 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13179 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13179]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13179])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13179) (a := (20852584357613 / 25000000000000 : ℝ)) (b := (9764152223 / 6250000000000 : ℝ)) (q := (2195981373729 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13179])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13179])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13179]

theorem cert13180_0 : CellCertificate 13180 (436874860951491 / 5000000000000000 : ℝ) (1593640151215313 / 1000000000000000000 : ℝ) (80407732096513 / 2500000000000000 : ℝ)
    (cell13180 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · have h := gap_lower (n := 13180) (a := (42034496586347 / 50000000000000 : ℝ)) (b := (156214447461 / 100000000000000 : ℝ)) (q := (87831788921 / 4000000000000 : ℝ))
      (E := (cell13180 ⟨0, by decide⟩).energy) (xi := (80407732096513 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13180 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13180]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13180])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13180) (a := (42034496586347 / 50000000000000 : ℝ)) (b := (156214447461 / 100000000000000 : ℝ)) (q := (87831788921 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13180])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13180])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13180]

theorem cert13180_1 : CellCertificate 13180 (436874860951491 / 5000000000000000 : ℝ) (1593640151215313 / 1000000000000000000 : ℝ) (80407732096513 / 2500000000000000 : ℝ)
    (cell13180 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · have h := gap_lower (n := 13180) (a := (42017052422521 / 50000000000000 : ℝ)) (b := (156214447461 / 100000000000000 : ℝ)) (q := (17154677533 / 781250000000 : ℝ))
      (E := (cell13180 ⟨1, by decide⟩).energy) (xi := (80407732096513 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13180 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13180]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13180])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13180) (a := (42017052422521 / 50000000000000 : ℝ)) (b := (156214447461 / 100000000000000 : ℝ)) (q := (17154677533 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13180])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13180])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13180]

theorem cert13180_2 : CellCertificate 13180 (436874860951491 / 5000000000000000 : ℝ) (1593640151215313 / 1000000000000000000 : ℝ) (80407732096513 / 2500000000000000 : ℝ)
    (cell13180 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · have h := gap_lower (n := 13180) (a := (8399924132989 / 10000000000000 : ℝ)) (b := (156214447461 / 100000000000000 : ℝ)) (q := (1097901365569 / 50000000000000 : ℝ))
      (E := (cell13180 ⟨2, by decide⟩).energy) (xi := (80407732096513 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13180 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13180]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13180])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13180) (a := (8399924132989 / 10000000000000 : ℝ)) (b := (156214447461 / 100000000000000 : ℝ)) (q := (1097901365569 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13180])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13180])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13180]

theorem cert13180_3 : CellCertificate 13180 (436874860951491 / 5000000000000000 : ℝ) (1593640151215313 / 1000000000000000000 : ℝ) (80407732096513 / 2500000000000000 : ℝ)
    (cell13180 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · have h := gap_lower (n := 13180) (a := (8396440259101 / 10000000000000 : ℝ)) (b := (156214447461 / 100000000000000 : ℝ)) (q := (2195806752137 / 100000000000000 : ℝ))
      (E := (cell13180 ⟨3, by decide⟩).energy) (xi := (80407732096513 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13180 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13180]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13180])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13180) (a := (8396440259101 / 10000000000000 : ℝ)) (b := (156214447461 / 100000000000000 : ℝ)) (q := (2195806752137 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13180])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13180])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13180]

theorem cert13180_4 : CellCertificate 13180 (436874860951491 / 5000000000000000 : ℝ) (1593640151215313 / 1000000000000000000 : ℝ) (80407732096513 / 2500000000000000 : ℝ)
    (cell13180 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · have h := gap_lower (n := 13180) (a := (41964794296179 / 50000000000000 : ℝ)) (b := (156214447461 / 100000000000000 : ℝ)) (q := (1097905397671 / 50000000000000 : ℝ))
      (E := (cell13180 ⟨4, by decide⟩).energy) (xi := (80407732096513 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13180 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13180]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13180])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13180) (a := (41964794296179 / 50000000000000 : ℝ)) (b := (156214447461 / 100000000000000 : ℝ)) (q := (1097905397671 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13180])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13180])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13180]

theorem cert13180_5 : CellCertificate 13180 (436874860951491 / 5000000000000000 : ℝ) (1593640151215313 / 1000000000000000000 : ℝ) (80407732096513 / 2500000000000000 : ℝ)
    (cell13180 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · have h := gap_lower (n := 13180) (a := (20973699824521 / 25000000000000 : ℝ)) (b := (156214447461 / 100000000000000 : ℝ)) (q := (27447685133 / 1250000000000 : ℝ))
      (E := (cell13180 ⟨5, by decide⟩).energy) (xi := (80407732096513 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13180 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13180]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13180])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13180) (a := (20973699824521 / 25000000000000 : ℝ)) (b := (156214447461 / 100000000000000 : ℝ)) (q := (27447685133 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13180])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13180])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13180]

theorem cert13180_6 : CellCertificate 13180 (436874860951491 / 5000000000000000 : ℝ) (1593640151215313 / 1000000000000000000 : ℝ) (80407732096513 / 2500000000000000 : ℝ)
    (cell13180 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · have h := gap_lower (n := 13180) (a := (20965008668131 / 25000000000000 : ℝ)) (b := (156214447461 / 100000000000000 : ℝ)) (q := (2195818805567 / 100000000000000 : ℝ))
      (E := (cell13180 ⟨6, by decide⟩).energy) (xi := (80407732096513 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13180 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13180]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13180])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13180) (a := (20965008668131 / 25000000000000 : ℝ)) (b := (156214447461 / 100000000000000 : ℝ)) (q := (2195818805567 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13180])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13180])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13180]

theorem cert13180_7 : CellCertificate 13180 (436874860951491 / 5000000000000000 : ℝ) (1593640151215313 / 1000000000000000000 : ℝ) (80407732096513 / 2500000000000000 : ℝ)
    (cell13180 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · have h := gap_lower (n := 13180) (a := (83825294680201 / 100000000000000 : ℝ)) (b := (156214447461 / 100000000000000 : ℝ)) (q := (2195822845427 / 100000000000000 : ℝ))
      (E := (cell13180 ⟨7, by decide⟩).energy) (xi := (80407732096513 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13180 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13180]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13180])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13180) (a := (83825294680201 / 100000000000000 : ℝ)) (b := (156214447461 / 100000000000000 : ℝ)) (q := (2195822845427 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13180])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13180])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13180]

theorem cert13180_8 : CellCertificate 13180 (436874860951491 / 5000000000000000 : ℝ) (1593640151215313 / 1000000000000000000 : ℝ) (80407732096513 / 2500000000000000 : ℝ)
    (cell13180 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · have h := gap_lower (n := 13180) (a := (83790579285823 / 100000000000000 : ℝ)) (b := (156214447461 / 100000000000000 : ℝ)) (q := (439165364247 / 20000000000000 : ℝ))
      (E := (cell13180 ⟨8, by decide⟩).energy) (xi := (80407732096513 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13180 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13180]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13180])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13180) (a := (83790579285823 / 100000000000000 : ℝ)) (b := (156214447461 / 100000000000000 : ℝ)) (q := (439165364247 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13180])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13180])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13180]

theorem cert13180_9 : CellCertificate 13180 (436874860951491 / 5000000000000000 : ℝ) (1593640151215313 / 1000000000000000000 : ℝ) (80407732096513 / 2500000000000000 : ℝ)
    (cell13180 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · have h := gap_lower (n := 13180) (a := (20938972113571 / 25000000000000 : ℝ)) (b := (156214447461 / 100000000000000 : ℝ)) (q := (548957713959 / 25000000000000 : ℝ))
      (E := (cell13180 ⟨9, by decide⟩).energy) (xi := (80407732096513 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13180 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13180]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13180])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13180) (a := (20938972113571 / 25000000000000 : ℝ)) (b := (156214447461 / 100000000000000 : ℝ)) (q := (548957713959 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13180])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13180])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13180]

theorem cert13180_10 : CellCertificate 13180 (436874860951491 / 5000000000000000 : ℝ) (1593640151215313 / 1000000000000000000 : ℝ) (80407732096513 / 2500000000000000 : ℝ)
    (cell13180 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · have h := gap_lower (n := 13180) (a := (4186061107533 / 5000000000000 : ℝ)) (b := (156214447461 / 100000000000000 : ℝ)) (q := (68619838739 / 3125000000000 : ℝ))
      (E := (cell13180 ⟨10, by decide⟩).energy) (xi := (80407732096513 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13180 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13180]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13180])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13180) (a := (4186061107533 / 5000000000000 : ℝ)) (b := (156214447461 / 100000000000000 : ℝ)) (q := (68619838739 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13180])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13180])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13180]

theorem cert13180_11 : CellCertificate 13180 (436874860951491 / 5000000000000000 : ℝ) (1593640151215313 / 1000000000000000000 : ℝ) (80407732096513 / 2500000000000000 : ℝ)
    (cell13180 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · have h := gap_lower (n := 13180) (a := (83686580340209 / 100000000000000 : ℝ)) (b := (156214447461 / 100000000000000 : ℝ)) (q := (274479861889 / 12500000000000 : ℝ))
      (E := (cell13180 ⟨11, by decide⟩).energy) (xi := (80407732096513 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13180 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13180]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13180])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13180) (a := (83686580340209 / 100000000000000 : ℝ)) (b := (156214447461 / 100000000000000 : ℝ)) (q := (274479861889 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13180])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13180])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13180]

theorem cert13180_12 : CellCertificate 13180 (436874860951491 / 5000000000000000 : ℝ) (1593640151215313 / 1000000000000000000 : ℝ) (80407732096513 / 2500000000000000 : ℝ)
    (cell13180 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · have h := gap_lower (n := 13180) (a := (83651962988369 / 100000000000000 : ℝ)) (b := (156214447461 / 100000000000000 : ℝ)) (q := (1097921456029 / 50000000000000 : ℝ))
      (E := (cell13180 ⟨12, by decide⟩).energy) (xi := (80407732096513 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13180 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13180]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13180])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13180) (a := (83651962988369 / 100000000000000 : ℝ)) (b := (156214447461 / 100000000000000 : ℝ)) (q := (1097921456029 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13180])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13180])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13180]

theorem cert13180_13 : CellCertificate 13180 (436874860951491 / 5000000000000000 : ℝ) (1593640151215313 / 1000000000000000000 : ℝ) (80407732096513 / 2500000000000000 : ℝ)
    (cell13180 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · have h := gap_lower (n := 13180) (a := (83617370060759 / 100000000000000 : ℝ)) (b := (156214447461 / 100000000000000 : ℝ)) (q := (548961724051 / 25000000000000 : ℝ))
      (E := (cell13180 ⟨13, by decide⟩).energy) (xi := (80407732096513 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13180 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13180]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13180])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13180) (a := (83617370060759 / 100000000000000 : ℝ)) (b := (156214447461 / 100000000000000 : ℝ)) (q := (548961724051 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13180])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13180])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13180]

theorem cert13180_14 : CellCertificate 13180 (436874860951491 / 5000000000000000 : ℝ) (1593640151215313 / 1000000000000000000 : ℝ) (80407732096513 / 2500000000000000 : ℝ)
    (cell13180 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · have h := gap_lower (n := 13180) (a := (3343312060927 / 4000000000000 : ℝ)) (b := (156214447461 / 100000000000000 : ℝ)) (q := (1097925455603 / 50000000000000 : ℝ))
      (E := (cell13180 ⟨14, by decide⟩).energy) (xi := (80407732096513 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13180 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13180]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13180])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13180) (a := (3343312060927 / 4000000000000 : ℝ)) (b := (156214447461 / 100000000000000 : ℝ)) (q := (1097925455603 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13180])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13180])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13180]

theorem cert13180_15 : CellCertificate 13180 (436874860951491 / 5000000000000000 : ℝ) (1593640151215313 / 1000000000000000000 : ℝ) (80407732096513 / 2500000000000000 : ℝ)
    (cell13180 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · have h := gap_lower (n := 13180) (a := (83548257341593 / 100000000000000 : ℝ)) (b := (156214447461 / 100000000000000 : ℝ)) (q := (2195854962361 / 100000000000000 : ℝ))
      (E := (cell13180 ⟨15, by decide⟩).energy) (xi := (80407732096513 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13180 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13180]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13180])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13180) (a := (83548257341593 / 100000000000000 : ℝ)) (b := (156214447461 / 100000000000000 : ℝ)) (q := (2195854962361 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13180])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13180])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13180]

theorem cert13180_16 : CellCertificate 13180 (436874860951491 / 5000000000000000 : ℝ) (1593640151215313 / 1000000000000000000 : ℝ) (80407732096513 / 2500000000000000 : ℝ)
    (cell13180 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · have h := gap_lower (n := 13180) (a := (83513737482161 / 100000000000000 : ℝ)) (b := (156214447461 / 100000000000000 : ℝ)) (q := (1097929469133 / 50000000000000 : ℝ))
      (E := (cell13180 ⟨16, by decide⟩).energy) (xi := (80407732096513 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13180 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13180]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13180])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13180) (a := (83513737482161 / 100000000000000 : ℝ)) (b := (156214447461 / 100000000000000 : ℝ)) (q := (1097929469133 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13180])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13180])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13180]

theorem cert13180_17 : CellCertificate 13180 (436874860951491 / 5000000000000000 : ℝ) (1593640151215313 / 1000000000000000000 : ℝ) (80407732096513 / 2500000000000000 : ℝ)
    (cell13180 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · have h := gap_lower (n := 13180) (a := (41739620955603 / 50000000000000 : ℝ)) (b := (156214447461 / 100000000000000 : ℝ)) (q := (2195862960099 / 100000000000000 : ℝ))
      (E := (cell13180 ⟨17, by decide⟩).energy) (xi := (80407732096513 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13180 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13180]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13180])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13180) (a := (41739620955603 / 50000000000000 : ℝ)) (b := (156214447461 / 100000000000000 : ℝ)) (q := (2195862960099 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13180])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13180])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13180]

theorem cert13180_18 : CellCertificate 13180 (436874860951491 / 5000000000000000 : ℝ) (1593640151215313 / 1000000000000000000 : ℝ) (80407732096513 / 2500000000000000 : ℝ)
    (cell13180 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · have h := gap_lower (n := 13180) (a := (83444770595227 / 100000000000000 : ℝ)) (b := (156214447461 / 100000000000000 : ℝ)) (q := (1097933487077 / 50000000000000 : ℝ))
      (E := (cell13180 ⟨18, by decide⟩).energy) (xi := (80407732096513 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13180 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13180]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13180])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13180) (a := (83444770595227 / 100000000000000 : ℝ)) (b := (156214447461 / 100000000000000 : ℝ)) (q := (1097933487077 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13180])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13180])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13180]

theorem cert13180_19 : CellCertificate 13180 (436874860951491 / 5000000000000000 : ℝ) (1593640151215313 / 1000000000000000000 : ℝ) (80407732096513 / 2500000000000000 : ℝ)
    (cell13180 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · have h := gap_lower (n := 13180) (a := (2606572609403 / 3125000000000 : ℝ)) (b := (156214447461 / 100000000000000 : ℝ)) (q := (1097935492347 / 50000000000000 : ℝ))
      (E := (cell13180 ⟨19, by decide⟩).energy) (xi := (80407732096513 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13180 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13180]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13180])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13180) (a := (2606572609403 / 3125000000000 : ℝ)) (b := (156214447461 / 100000000000000 : ℝ)) (q := (1097935492347 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13180])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13180])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13180]

theorem cert13181_0 : CellCertificate 13181 (174744740934983 / 2000000000000000 : ℝ) (199189901071237 / 125000000000000000 : ℝ) (321605972306947 / 10000000000000000 : ℝ)
    (cell13181 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · have h := gap_lower (n := 13181) (a := (42034489563867 / 50000000000000 : ℝ)) (b := (156202461199 / 100000000000000 : ℝ)) (q := (2195684328969 / 100000000000000 : ℝ))
      (E := (cell13181 ⟨0, by decide⟩).energy) (xi := (321605972306947 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13181 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13181]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13181])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13181) (a := (42034489563867 / 50000000000000 : ℝ)) (b := (156202461199 / 100000000000000 : ℝ)) (q := (2195684328969 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13181])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13181])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13181]

theorem cert13181_1 : CellCertificate 13181 (174744740934983 / 2000000000000000 : ℝ) (199189901071237 / 125000000000000000 : ℝ) (321605972306947 / 10000000000000000 : ℝ)
    (cell13181 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · have h := gap_lower (n := 13181) (a := (21008522701579 / 25000000000000 : ℝ)) (b := (156202461199 / 100000000000000 : ℝ)) (q := (1097844192301 / 50000000000000 : ℝ))
      (E := (cell13181 ⟨1, by decide⟩).energy) (xi := (321605972306947 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13181 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13181]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13181])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13181) (a := (21008522701579 / 25000000000000 : ℝ)) (b := (156202461199 / 100000000000000 : ℝ)) (q := (1097844192301 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13181])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13181])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13181]

theorem cert13181_2 : CellCertificate 13181 (174744740934983 / 2000000000000000 : ℝ) (199189901071237 / 125000000000000000 : ℝ) (321605972306947 / 10000000000000000 : ℝ)
    (cell13181 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · have h := gap_lower (n := 13181) (a := (16799845459479 / 20000000000000 : ℝ)) (b := (156202461199 / 100000000000000 : ℝ)) (q := (1097846194069 / 50000000000000 : ℝ))
      (E := (cell13181 ⟨2, by decide⟩).energy) (xi := (321605972306947 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13181 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13181]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13181])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13181) (a := (16799845459479 / 20000000000000 : ℝ)) (b := (156202461199 / 100000000000000 : ℝ)) (q := (1097846194069 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13181])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13181])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13181]

theorem cert13181_3 : CellCertificate 13181 (174744740934983 / 2000000000000000 : ℝ) (199189901071237 / 125000000000000000 : ℝ) (321605972306947 / 10000000000000000 : ℝ)
    (cell13181 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · have h := gap_lower (n := 13181) (a := (41982194282369 / 50000000000000 : ℝ)) (b := (156202461199 / 100000000000000 : ℝ)) (q := (219569640581 / 10000000000000 : ℝ))
      (E := (cell13181 ⟨3, by decide⟩).energy) (xi := (321605972306947 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13181 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13181]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13181])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13181) (a := (41982194282369 / 50000000000000 : ℝ)) (b := (156202461199 / 100000000000000 : ℝ)) (q := (219569640581 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13181])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13181])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13181]

theorem cert13181_4 : CellCertificate 13181 (174744740934983 / 2000000000000000 : ℝ) (199189901071237 / 125000000000000000 : ℝ) (321605972306947 / 10000000000000000 : ℝ)
    (cell13181 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · have h := gap_lower (n := 13181) (a := (5245598410769 / 6250000000000 : ℝ)) (b := (156202461199 / 100000000000000 : ℝ)) (q := (2195700387783 / 100000000000000 : ℝ))
      (E := (cell13181 ⟨4, by decide⟩).energy) (xi := (321605972306947 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13181 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13181]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13181])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13181) (a := (5245598410769 / 6250000000000 : ℝ)) (b := (156202461199 / 100000000000000 : ℝ)) (q := (2195700387783 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13181])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13181])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13181]

theorem cert13181_5 : CellCertificate 13181 (174744740934983 / 2000000000000000 : ℝ) (199189901071237 / 125000000000000000 : ℝ) (321605972306947 / 10000000000000000 : ℝ)
    (cell13181 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · have h := gap_lower (n := 13181) (a := (83894785284243 / 100000000000000 : ℝ)) (b := (156202461199 / 100000000000000 : ℝ)) (q := (1097852199911 / 50000000000000 : ℝ))
      (E := (cell13181 ⟨5, by decide⟩).energy) (xi := (321605972306947 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13181 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13181]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13181])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13181) (a := (83894785284243 / 100000000000000 : ℝ)) (b := (156202461199 / 100000000000000 : ℝ)) (q := (1097852199911 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13181])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13181])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13181]

theorem cert13181_6 : CellCertificate 13181 (174744740934983 / 2000000000000000 : ℝ) (199189901071237 / 125000000000000000 : ℝ) (321605972306947 / 10000000000000000 : ℝ)
    (cell13181 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · have h := gap_lower (n := 13181) (a := (8386002066489 / 10000000000000 : ℝ)) (b := (156202461199 / 100000000000000 : ℝ)) (q := (1097854224767 / 50000000000000 : ℝ))
      (E := (cell13181 ⟨6, by decide⟩).energy) (xi := (321605972306947 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13181 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13181]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13181])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13181) (a := (8386002066489 / 10000000000000 : ℝ)) (b := (156202461199 / 100000000000000 : ℝ)) (q := (1097854224767 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13181])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13181])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13181]

theorem cert13181_7 : CellCertificate 13181 (174744740934983 / 2000000000000000 : ℝ) (199189901071237 / 125000000000000000 : ℝ) (321605972306947 / 10000000000000000 : ℝ)
    (cell13181 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · have h := gap_lower (n := 13181) (a := (5239080042423 / 6250000000000 : ℝ)) (b := (156202461199 / 100000000000000 : ℝ)) (q := (1097856214117 / 50000000000000 : ℝ))
      (E := (cell13181 ⟨7, by decide⟩).energy) (xi := (321605972306947 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13181 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13181]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13181])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13181) (a := (5239080042423 / 6250000000000 : ℝ)) (b := (156202461199 / 100000000000000 : ℝ)) (q := (1097856214117 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13181])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13181])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13181]

theorem cert13181_8 : CellCertificate 13181 (174744740934983 / 2000000000000000 : ℝ) (199189901071237 / 125000000000000000 : ℝ) (321605972306947 / 10000000000000000 : ℝ)
    (cell13181 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · have h := gap_lower (n := 13181) (a := (83790565290587 / 100000000000000 : ℝ)) (b := (156202461199 / 100000000000000 : ℝ)) (q := (2195716458967 / 100000000000000 : ℝ))
      (E := (cell13181 ⟨8, by decide⟩).energy) (xi := (321605972306947 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13181 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13181]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13181])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13181) (a := (83790565290587 / 100000000000000 : ℝ)) (b := (156202461199 / 100000000000000 : ℝ)) (q := (2195716458967 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13181])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13181])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13181]

theorem cert13181_9 : CellCertificate 13181 (174744740934983 / 2000000000000000 : ℝ) (199189901071237 / 125000000000000000 : ℝ) (321605972306947 / 10000000000000000 : ℝ)
    (cell13181 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · have h := gap_lower (n := 13181) (a := (41877937232619 / 50000000000000 : ℝ)) (b := (156202461199 / 100000000000000 : ℝ)) (q := (2195720490521 / 100000000000000 : ℝ))
      (E := (cell13181 ⟨9, by decide⟩).energy) (xi := (321605972306947 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13181 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13181]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13181])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13181) (a := (41877937232619 / 50000000000000 : ℝ)) (b := (156202461199 / 100000000000000 : ℝ)) (q := (2195720490521 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13181])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13181])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13181]

theorem cert13181_10 : CellCertificate 13181 (174744740934983 / 2000000000000000 : ℝ) (199189901071237 / 125000000000000000 : ℝ) (321605972306947 / 10000000000000000 : ℝ)
    (cell13181 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · have h := gap_lower (n := 13181) (a := (83721208167799 / 100000000000000 : ℝ)) (b := (156202461199 / 100000000000000 : ℝ)) (q := (2195724471333 / 100000000000000 : ℝ))
      (E := (cell13181 ⟨10, by decide⟩).energy) (xi := (321605972306947 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13181 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13181]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13181])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13181) (a := (83721208167799 / 100000000000000 : ℝ)) (b := (156202461199 / 100000000000000 : ℝ)) (q := (2195724471333 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13181])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13181])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13181]

theorem cert13181_11 : CellCertificate 13181 (174744740934983 / 2000000000000000 : ℝ) (199189901071237 / 125000000000000000 : ℝ) (321605972306947 / 10000000000000000 : ℝ)
    (cell13181 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · have h := gap_lower (n := 13181) (a := (83686566363527 / 100000000000000 : ℝ)) (b := (156202461199 / 100000000000000 : ℝ)) (q := (548932130961 / 25000000000000 : ℝ))
      (E := (cell13181 ⟨11, by decide⟩).energy) (xi := (321605972306947 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13181 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13181]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13181])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13181) (a := (83686566363527 / 100000000000000 : ℝ)) (b := (156202461199 / 100000000000000 : ℝ)) (q := (548932130961 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13181])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13181])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13181]

theorem cert13181_12 : CellCertificate 13181 (174744740934983 / 2000000000000000 : ℝ) (199189901071237 / 125000000000000000 : ℝ) (321605972306947 / 10000000000000000 : ℝ)
    (cell13181 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · have h := gap_lower (n := 13181) (a := (83651949017861 / 100000000000000 : ℝ)) (b := (156202461199 / 100000000000000 : ℝ)) (q := (548933134471 / 25000000000000 : ℝ))
      (E := (cell13181 ⟨12, by decide⟩).energy) (xi := (321605972306947 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13181 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13181]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13181])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13181) (a := (83651949017861 / 100000000000000 : ℝ)) (b := (156202461199 / 100000000000000 : ℝ)) (q := (548933134471 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13181])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13181])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13181]

theorem cert13181_13 : CellCertificate 13181 (174744740934983 / 2000000000000000 : ℝ) (199189901071237 / 125000000000000000 : ℝ) (321605972306947 / 10000000000000000 : ℝ)
    (cell13181 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · have h := gap_lower (n := 13181) (a := (4180867804821 / 5000000000000 : ℝ)) (b := (156202461199 / 100000000000000 : ℝ)) (q := (2195736519169 / 100000000000000 : ℝ))
      (E := (cell13181 ⟨13, by decide⟩).energy) (xi := (321605972306947 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13181 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13181]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13181])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13181) (a := (4180867804821 / 5000000000000 : ℝ)) (b := (156202461199 / 100000000000000 : ℝ)) (q := (2195736519169 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13181])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13181])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13181]

theorem cert13181_14 : CellCertificate 13181 (174744740934983 / 2000000000000000 : ℝ) (199189901071237 / 125000000000000000 : ℝ) (321605972306947 / 10000000000000000 : ℝ)
    (cell13181 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · have h := gap_lower (n := 13181) (a := (16716557513 / 20000000000 : ℝ)) (b := (156202461199 / 100000000000000 : ℝ)) (q := (1097870265679 / 50000000000000 : ℝ))
      (E := (cell13181 ⟨14, by decide⟩).energy) (xi := (321605972306947 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13181 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13181]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13181])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13181) (a := (16716557513 / 20000000000 : ℝ)) (b := (156202461199 / 100000000000000 : ℝ)) (q := (1097870265679 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13181])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13181])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13181]

theorem cert13181_15 : CellCertificate 13181 (174744740934983 / 2000000000000000 : ℝ) (199189901071237 / 125000000000000000 : ℝ) (321605972306947 / 10000000000000000 : ℝ)
    (cell13181 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · have h := gap_lower (n := 13181) (a := (3341929735583 / 4000000000000 : ℝ)) (b := (156202461199 / 100000000000000 : ℝ)) (q := (548936144937 / 25000000000000 : ℝ))
      (E := (cell13181 ⟨15, by decide⟩).energy) (xi := (321605972306947 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13181 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13181]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13181])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13181) (a := (3341929735583 / 4000000000000 : ℝ)) (b := (156202461199 / 100000000000000 : ℝ)) (q := (548936144937 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13181])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13181])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13181]

theorem cert13181_16 : CellCertificate 13181 (174744740934983 / 2000000000000000 : ℝ) (199189901071237 / 125000000000000000 : ℝ) (321605972306947 / 10000000000000000 : ℝ)
    (cell13181 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · have h := gap_lower (n := 13181) (a := (10439215442037 / 12500000000000 : ℝ)) (b := (156202461199 / 100000000000000 : ℝ)) (q := (548937138233 / 25000000000000 : ℝ))
      (E := (cell13181 ⟨16, by decide⟩).energy) (xi := (321605972306947 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13181 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13181]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13181])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13181) (a := (10439215442037 / 12500000000000 : ℝ)) (b := (156202461199 / 100000000000000 : ℝ)) (q := (548937138233 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13181])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13181])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13181]

theorem cert13181_17 : CellCertificate 13181 (174744740934983 / 2000000000000000 : ℝ) (199189901071237 / 125000000000000000 : ℝ) (321605972306947 / 10000000000000000 : ℝ)
    (cell13181 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · have h := gap_lower (n := 13181) (a := (2608725874109 / 3125000000000 : ℝ)) (b := (156202461199 / 100000000000000 : ℝ)) (q := (548938143023 / 25000000000000 : ℝ))
      (E := (cell13181 ⟨17, by decide⟩).energy) (xi := (321605972306947 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13181 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13181]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13181])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13181) (a := (2608725874109 / 3125000000000 : ℝ)) (b := (156202461199 / 100000000000000 : ℝ)) (q := (548938143023 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13181])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13181])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13181]

theorem cert13181_18 : CellCertificate 13181 (174744740934983 / 2000000000000000 : ℝ) (199189901071237 / 125000000000000000 : ℝ) (321605972306947 / 10000000000000000 : ℝ)
    (cell13181 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · have h := gap_lower (n := 13181) (a := (83444756661651 / 100000000000000 : ℝ)) (b := (156202461199 / 100000000000000 : ℝ)) (q := (2195756583521 / 100000000000000 : ℝ))
      (E := (cell13181 ⟨18, by decide⟩).energy) (xi := (321605972306947 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13181 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13181]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13181])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13181) (a := (83444756661651 / 100000000000000 : ℝ)) (b := (156202461199 / 100000000000000 : ℝ)) (q := (2195756583521 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13181])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13181])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13181]

theorem cert13181_19 : CellCertificate 13181 (174744740934983 / 2000000000000000 : ℝ) (199189901071237 / 125000000000000000 : ℝ) (321605972306947 / 10000000000000000 : ℝ)
    (cell13181 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · have h := gap_lower (n := 13181) (a := (5213144348341 / 6250000000000 : ℝ)) (b := (156202461199 / 100000000000000 : ℝ)) (q := (1097880295741 / 50000000000000 : ℝ))
      (E := (cell13181 ⟨19, by decide⟩).energy) (xi := (321605972306947 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13181 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13181]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13181])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13181) (a := (5213144348341 / 6250000000000 : ℝ)) (b := (156202461199 / 100000000000000 : ℝ)) (q := (1097880295741 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13181])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13181])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13181]

theorem cert13182_0 : CellCertificate 13182 (436848845611579 / 5000000000000000 : ℝ) (318679656855991 / 200000000000000000 : ℝ) (160790510062331 / 5000000000000000 : ℝ)
    (cell13182 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · have h := gap_lower (n := 13182) (a := (84068965084907 / 100000000000000 : ℝ)) (b := (156190476783 / 100000000000000 : ℝ)) (q := (1097786994287 / 50000000000000 : ℝ))
      (E := (cell13182 ⟨0, by decide⟩).energy) (xi := (160790510062331 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13182 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13182]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13182])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13182) (a := (84068965084907 / 100000000000000 : ℝ)) (b := (156190476783 / 100000000000000 : ℝ)) (q := (1097786994287 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13182])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13182])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13182]

theorem cert13182_1 : CellCertificate 13182 (436848845611579 / 5000000000000000 : ℝ) (318679656855991 / 200000000000000000 : ℝ) (160790510062331 / 5000000000000000 : ℝ)
    (cell13182 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · have h := gap_lower (n := 13182) (a := (21008519192431 / 25000000000000 : ℝ)) (b := (156190476783 / 100000000000000 : ℝ)) (q := (439115596581 / 20000000000000 : ℝ))
      (E := (cell13182 ⟨1, by decide⟩).energy) (xi := (160790510062331 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13182 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13182]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13182])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13182) (a := (21008519192431 / 25000000000000 : ℝ)) (b := (156190476783 / 100000000000000 : ℝ)) (q := (439115596581 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13182])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13182])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13182]

theorem cert13182_2 : CellCertificate 13182 (436848845611579 / 5000000000000000 : ℝ) (318679656855991 / 200000000000000000 : ℝ) (160790510062331 / 5000000000000000 : ℝ)
    (cell13182 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · have h := gap_lower (n := 13182) (a := (8399921326703 / 10000000000000 : ℝ)) (b := (156190476783 / 100000000000000 : ℝ)) (q := (548895495761 / 25000000000000 : ℝ))
      (E := (cell13182 ⟨2, by decide⟩).energy) (xi := (160790510062331 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13182 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13182]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13182])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13182) (a := (8399921326703 / 10000000000000 : ℝ)) (b := (156190476783 / 100000000000000 : ℝ)) (q := (548895495761 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13182])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13182])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13182]

theorem cert13182_3 : CellCertificate 13182 (436848845611579 / 5000000000000000 : ℝ) (318679656855991 / 200000000000000000 : ℝ) (160790510062331 / 5000000000000000 : ℝ)
    (cell13182 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · have h := gap_lower (n := 13182) (a := (20991093635149 / 25000000000000 : ℝ)) (b := (156190476783 / 100000000000000 : ℝ)) (q := (548896499341 / 25000000000000 : ℝ))
      (E := (cell13182 ⟨3, by decide⟩).energy) (xi := (160790510062331 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13182 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13182]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13182])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13182) (a := (20991093635149 / 25000000000000 : ℝ)) (b := (156190476783 / 100000000000000 : ℝ)) (q := (548896499341 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13182])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13182])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13182]

theorem cert13182_4 : CellCertificate 13182 (436848845611579 / 5000000000000000 : ℝ) (318679656855991 / 200000000000000000 : ℝ) (160790510062331 / 5000000000000000 : ℝ)
    (cell13182 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · have h := gap_lower (n := 13182) (a := (4196478027719 / 5000000000000 : ℝ)) (b := (156190476783 / 100000000000000 : ℝ)) (q := (1097795016991 / 50000000000000 : ℝ))
      (E := (cell13182 ⟨4, by decide⟩).energy) (xi := (160790510062331 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13182 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13182]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13182])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13182) (a := (4196478027719 / 5000000000000 : ℝ)) (b := (156190476783 / 100000000000000 : ℝ)) (q := (1097795016991 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13182])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13182])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13182]

theorem cert13182_5 : CellCertificate 13182 (436848845611579 / 5000000000000000 : ℝ) (318679656855991 / 200000000000000000 : ℝ) (160790510062331 / 5000000000000000 : ℝ)
    (cell13182 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · have h := gap_lower (n := 13182) (a := (8389477127253 / 10000000000000 : ℝ)) (b := (156190476783 / 100000000000000 : ℝ)) (q := (548898510697 / 25000000000000 : ℝ))
      (E := (cell13182 ⟨5, by decide⟩).energy) (xi := (160790510062331 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13182 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13182]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13182])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13182) (a := (8389477127253 / 10000000000000 : ℝ)) (b := (156190476783 / 100000000000000 : ℝ)) (q := (548898510697 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13182])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13182])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13182]

theorem cert13182_6 : CellCertificate 13182 (436848845611579 / 5000000000000000 : ℝ) (318679656855991 / 200000000000000000 : ℝ) (160790510062331 / 5000000000000000 : ℝ)
    (cell13182 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · have h := gap_lower (n := 13182) (a := (10482500832423 / 12500000000000 : ℝ)) (b := (156190476783 / 100000000000000 : ℝ)) (q := (68612440291 / 3125000000000 : ℝ))
      (E := (cell13182 ⟨6, by decide⟩).energy) (xi := (160790510062331 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13182 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13182]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13182])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13182) (a := (10482500832423 / 12500000000000 : ℝ)) (b := (156190476783 / 100000000000000 : ℝ)) (q := (68612440291 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13182])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13182])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13182]

theorem cert13182_7 : CellCertificate 13182 (436848845611579 / 5000000000000000 : ℝ) (318679656855991 / 200000000000000000 : ℝ) (160790510062331 / 5000000000000000 : ℝ)
    (cell13182 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · have h := gap_lower (n := 13182) (a := (83825266679463 / 100000000000000 : ℝ)) (b := (156190476783 / 100000000000000 : ℝ)) (q := (2195602064871 / 100000000000000 : ℝ))
      (E := (cell13182 ⟨7, by decide⟩).energy) (xi := (160790510062331 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13182 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13182]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13182])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13182) (a := (83825266679463 / 100000000000000 : ℝ)) (b := (156190476783 / 100000000000000 : ℝ)) (q := (2195602064871 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13182])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13182])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13182]

theorem cert13182_8 : CellCertificate 13182 (436848845611579 / 5000000000000000 : ℝ) (318679656855991 / 200000000000000000 : ℝ) (160790510062331 / 5000000000000000 : ℝ)
    (cell13182 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · have h := gap_lower (n := 13182) (a := (20947637824369 / 25000000000000 : ℝ)) (b := (156190476783 / 100000000000000 : ℝ)) (q := (2195606092513 / 100000000000000 : ℝ))
      (E := (cell13182 ⟨8, by decide⟩).energy) (xi := (160790510062331 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13182 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13182]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13182])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13182) (a := (20947637824369 / 25000000000000 : ℝ)) (b := (156190476783 / 100000000000000 : ℝ)) (q := (2195606092513 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13182])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13182])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13182]

theorem cert13182_9 : CellCertificate 13182 (436848845611579 / 5000000000000000 : ℝ) (318679656855991 / 200000000000000000 : ℝ) (160790510062331 / 5000000000000000 : ℝ)
    (cell13182 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · have h := gap_lower (n := 13182) (a := (83755860478317 / 100000000000000 : ℝ)) (b := (156190476783 / 100000000000000 : ℝ)) (q := (109780506051 / 5000000000000 : ℝ))
      (E := (cell13182 ⟨9, by decide⟩).energy) (xi := (160790510062331 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13182 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13182]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13182])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13182) (a := (83755860478317 / 100000000000000 : ℝ)) (b := (156190476783 / 100000000000000 : ℝ)) (q := (109780506051 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13182])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13182])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13182]

theorem cert13182_10 : CellCertificate 13182 (436848845611579 / 5000000000000000 : ℝ) (318679656855991 / 200000000000000000 : ℝ) (160790510062331 / 5000000000000000 : ℝ)
    (cell13182 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · have h := gap_lower (n := 13182) (a := (41860597093531 / 50000000000000 : ℝ)) (b := (156190476783 / 100000000000000 : ℝ)) (q := (2195614098833 / 100000000000000 : ℝ))
      (E := (cell13182 ⟨10, by decide⟩).energy) (xi := (160790510062331 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13182 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13182]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13182])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13182) (a := (41860597093531 / 50000000000000 : ℝ)) (b := (156190476783 / 100000000000000 : ℝ)) (q := (2195614098833 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13182])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13182])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13182]

theorem cert13182_11 : CellCertificate 13182 (436848845611579 / 5000000000000000 : ℝ) (318679656855991 / 200000000000000000 : ℝ) (160790510062331 / 5000000000000000 : ℝ)
    (cell13182 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · have h := gap_lower (n := 13182) (a := (83686552388969 / 100000000000000 : ℝ)) (b := (156190476783 / 100000000000000 : ℝ)) (q := (219561814839 / 10000000000000 : ℝ))
      (E := (cell13182 ⟨11, by decide⟩).energy) (xi := (160790510062331 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13182 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13182]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13182])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13182) (a := (83686552388969 / 100000000000000 : ℝ)) (b := (156190476783 / 100000000000000 : ℝ)) (q := (219561814839 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13182])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13182])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13182]

theorem cert13182_12 : CellCertificate 13182 (436848845611579 / 5000000000000000 : ℝ) (318679656855991 / 200000000000000000 : ℝ) (160790510062331 / 5000000000000000 : ℝ)
    (cell13182 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · have h := gap_lower (n := 13182) (a := (20912983762369 / 25000000000000 : ℝ)) (b := (156190476783 / 100000000000000 : ℝ)) (q := (87824886381 / 4000000000000 : ℝ))
      (E := (cell13182 ⟨12, by decide⟩).energy) (xi := (160790510062331 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13182 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13182]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13182])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13182) (a := (20912983762369 / 25000000000000 : ℝ)) (b := (156190476783 / 100000000000000 : ℝ)) (q := (87824886381 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13182])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13182])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13182]

theorem cert13182_13 : CellCertificate 13182 (436848845611579 / 5000000000000000 : ℝ) (318679656855991 / 200000000000000000 : ℝ) (160790510062331 / 5000000000000000 : ℝ)
    (cell13182 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · have h := gap_lower (n := 13182) (a := (83617342134203 / 100000000000000 : ℝ)) (b := (156190476783 / 100000000000000 : ℝ)) (q := (2195626196111 / 100000000000000 : ℝ))
      (E := (cell13182 ⟨13, by decide⟩).energy) (xi := (160790510062331 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13182 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13182]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13182])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13182) (a := (83617342134203 / 100000000000000 : ℝ)) (b := (156190476783 / 100000000000000 : ℝ)) (q := (2195626196111 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13182])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13182])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13182]

theorem cert13182_14 : CellCertificate 13182 (436848845611579 / 5000000000000000 : ℝ) (318679656855991 / 200000000000000000 : ℝ) (160790510062331 / 5000000000000000 : ℝ)
    (cell13182 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · have h := gap_lower (n := 13182) (a := (16716554721789 / 20000000000000 : ℝ)) (b := (156190476783 / 100000000000000 : ℝ)) (q := (2195630205511 / 100000000000000 : ℝ))
      (E := (cell13182 ⟨14, by decide⟩).energy) (xi := (160790510062331 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13182 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13182]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13182])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13182) (a := (16716554721789 / 20000000000000 : ℝ)) (b := (156190476783 / 100000000000000 : ℝ)) (q := (2195630205511 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13182])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13182])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13182]

theorem cert13182_15 : CellCertificate 13182 (436848845611579 / 5000000000000000 : ℝ) (318679656855991 / 200000000000000000 : ℝ) (160790510062331 / 5000000000000000 : ℝ)
    (cell13182 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · have h := gap_lower (n := 13182) (a := (83548229439677 / 100000000000000 : ℝ)) (b := (156190476783 / 100000000000000 : ℝ)) (q := (274454274119 / 12500000000000 : ℝ))
      (E := (cell13182 ⟨15, by decide⟩).energy) (xi := (160790510062331 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13182 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13182]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13182])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13182) (a := (83548229439677 / 100000000000000 : ℝ)) (b := (156190476783 / 100000000000000 : ℝ)) (q := (274454274119 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13182])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13182])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13182]

theorem cert13182_16 : CellCertificate 13182 (436848845611579 / 5000000000000000 : ℝ) (318679656855991 / 200000000000000000 : ℝ) (160790510062331 / 5000000000000000 : ℝ)
    (cell13182 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · have h := gap_lower (n := 13182) (a := (1670274191851 / 2000000000000 : ℝ)) (b := (156190476783 / 100000000000000 : ℝ)) (q := (137227388853 / 6250000000000 : ℝ))
      (E := (cell13182 ⟨16, by decide⟩).energy) (xi := (160790510062331 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13182 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13182]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13182])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13182) (a := (1670274191851 / 2000000000000 : ℝ)) (b := (156190476783 / 100000000000000 : ℝ)) (q := (137227388853 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13182])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13182])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13182]

theorem cert13182_17 : CellCertificate 13182 (436848845611579 / 5000000000000000 : ℝ) (318679656855991 / 200000000000000000 : ℝ) (160790510062331 / 5000000000000000 : ℝ)
    (cell13182 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · have h := gap_lower (n := 13182) (a := (2608725438559 / 3125000000000 : ℝ)) (b := (156190476783 / 100000000000000 : ℝ)) (q := (2195642238159 / 100000000000000 : ℝ))
      (E := (cell13182 ⟨17, by decide⟩).energy) (xi := (160790510062331 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13182 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13182]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13182])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13182) (a := (2608725438559 / 3125000000000 : ℝ)) (b := (156190476783 / 100000000000000 : ℝ)) (q := (2195642238159 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13182])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13182])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13182]

theorem cert13182_18 : CellCertificate 13182 (436848845611579 / 5000000000000000 : ℝ) (318679656855991 / 200000000000000000 : ℝ) (160790510062331 / 5000000000000000 : ℝ)
    (cell13182 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · have h := gap_lower (n := 13182) (a := (5215296420637 / 6250000000000 : ℝ)) (b := (156190476783 / 100000000000000 : ℝ)) (q := (1097823123493 / 50000000000000 : ℝ))
      (E := (cell13182 ⟨18, by decide⟩).energy) (xi := (160790510062331 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13182 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13182]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13182])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13182) (a := (5215296420637 / 6250000000000 : ℝ)) (b := (156190476783 / 100000000000000 : ℝ)) (q := (1097823123493 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13182])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13182])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13182]

theorem cert13182_19 : CellCertificate 13182 (436848845611579 / 5000000000000000 : ℝ) (318679656855991 / 200000000000000000 : ℝ) (160790510062331 / 5000000000000000 : ℝ)
    (cell13182 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · have h := gap_lower (n := 13182) (a := (83410295648133 / 100000000000000 : ℝ)) (b := (156190476783 / 100000000000000 : ℝ)) (q := (274456281549 / 12500000000000 : ℝ))
      (E := (cell13182 ⟨19, by decide⟩).energy) (xi := (160790510062331 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13182 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13182]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13182])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13182) (a := (83410295648133 / 100000000000000 : ℝ)) (b := (156190476783 / 100000000000000 : ℝ)) (q := (274456281549 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13182])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13182])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13182]

theorem cert13183_0 : CellCertificate 13183 (873671681546847 / 10000000000000000 : ℝ) (1593277378341313 / 1000000000000000000 : ℝ) (321556071838237 / 10000000000000000 : ℝ)
    (cell13183 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · have h := gap_lower (n := 13183) (a := (84068951044213 / 100000000000000 : ℝ)) (b := (39044623553 / 25000000000000 : ℝ)) (q := (2195463643987 / 100000000000000 : ℝ))
      (E := (cell13183 ⟨0, by decide⟩).energy) (xi := (321556071838237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13183 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13183]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13183])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13183) (a := (84068951044213 / 100000000000000 : ℝ)) (b := (39044623553 / 25000000000000 : ℝ)) (q := (2195463643987 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13183])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13183])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13183]

theorem cert13183_1 : CellCertificate 13183 (873671681546847 / 10000000000000000 : ℝ) (1593277378341313 / 1000000000000000000 : ℝ) (321556071838237 / 10000000000000000 : ℝ)
    (cell13183 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · have h := gap_lower (n := 13183) (a := (84034062735263 / 100000000000000 : ℝ)) (b := (39044623553 / 25000000000000 : ℝ)) (q := (137216727181 / 6250000000000 : ℝ))
      (E := (cell13183 ⟨1, by decide⟩).energy) (xi := (321556071838237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13183 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13183]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13183])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13183) (a := (84034062735263 / 100000000000000 : ℝ)) (b := (39044623553 / 25000000000000 : ℝ)) (q := (137216727181 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13183])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13183])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13183]

theorem cert13183_2 : CellCertificate 13183 (873671681546847 / 10000000000000000 : ℝ) (1593277378341313 / 1000000000000000000 : ℝ) (321556071838237 / 10000000000000000 : ℝ)
    (cell13183 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · have h := gap_lower (n := 13183) (a := (41999599619399 / 50000000000000 : ℝ)) (b := (39044623553 / 25000000000000 : ℝ)) (q := (2195471689563 / 100000000000000 : ℝ))
      (E := (cell13183 ⟨2, by decide⟩).energy) (xi := (321556071838237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13183 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13183]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13183])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13183) (a := (41999599619399 / 50000000000000 : ℝ)) (b := (39044623553 / 25000000000000 : ℝ)) (q := (2195471689563 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13183])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13183])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13183]

theorem cert13183_3 : CellCertificate 13183 (873671681546847 / 10000000000000000 : ℝ) (1593277378341313 / 1000000000000000000 : ℝ) (321556071838237 / 10000000000000000 : ℝ)
    (cell13183 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · have h := gap_lower (n := 13183) (a := (16792872103717 / 20000000000000 : ℝ)) (b := (39044623553 / 25000000000000 : ℝ)) (q := (109773785029 / 5000000000000 : ℝ))
      (E := (cell13183 ⟨3, by decide⟩).energy) (xi := (321556071838237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13183 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13183]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13183])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13183) (a := (16792872103717 / 20000000000000 : ℝ)) (b := (39044623553 / 25000000000000 : ℝ)) (q := (109773785029 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13183])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13183])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13183]

theorem cert13183_4 : CellCertificate 13183 (873671681546847 / 10000000000000000 : ℝ) (1593277378341313 / 1000000000000000000 : ℝ) (321556071838237 / 10000000000000000 : ℝ)
    (cell13183 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · have h := gap_lower (n := 13183) (a := (16785909307717 / 20000000000000 : ℝ)) (b := (39044623553 / 25000000000000 : ℝ)) (q := (274434959499 / 12500000000000 : ℝ))
      (E := (cell13183 ⟨4, by decide⟩).energy) (xi := (321556071838237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13183 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13183]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13183])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13183) (a := (16785909307717 / 20000000000000 : ℝ)) (b := (39044623553 / 25000000000000 : ℝ)) (q := (274434959499 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13183])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13183])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13183]

theorem cert13183_5 : CellCertificate 13183 (873671681546847 / 10000000000000000 : ℝ) (1593277378341313 / 1000000000000000000 : ℝ) (321556071838237 / 10000000000000000 : ℝ)
    (cell13183 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · have h := gap_lower (n := 13183) (a := (83894757262947 / 100000000000000 : ℝ)) (b := (39044623553 / 25000000000000 : ℝ)) (q := (2195483681563 / 100000000000000 : ℝ))
      (E := (cell13183 ⟨5, by decide⟩).energy) (xi := (321556071838237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13183 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13183]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13183])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13183) (a := (83894757262947 / 100000000000000 : ℝ)) (b := (39044623553 / 25000000000000 : ℝ)) (q := (2195483681563 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13183])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13183])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13183]

theorem cert13183_6 : CellCertificate 13183 (873671681546847 / 10000000000000000 : ℝ) (1593277378341313 / 1000000000000000000 : ℝ) (321556071838237 / 10000000000000000 : ℝ)
    (cell13183 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · have h := gap_lower (n := 13183) (a := (16771998531201 / 20000000000000 : ℝ)) (b := (39044623553 / 25000000000000 : ℝ)) (q := (1097743862451 / 50000000000000 : ℝ))
      (E := (cell13183 ⟨6, by decide⟩).energy) (xi := (321556071838237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13183 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13183]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13183])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13183) (a := (16771998531201 / 20000000000000 : ℝ)) (b := (39044623553 / 25000000000000 : ℝ)) (q := (1097743862451 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13183])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13183])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13183]

theorem cert13183_7 : CellCertificate 13183 (873671681546847 / 10000000000000000 : ℝ) (1593277378341313 / 1000000000000000000 : ℝ) (321556071838237 / 10000000000000000 : ℝ)
    (cell13183 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · have h := gap_lower (n := 13183) (a := (20956313170571 / 25000000000000 : ℝ)) (b := (39044623553 / 25000000000000 : ℝ)) (q := (1097745877671 / 50000000000000 : ℝ))
      (E := (cell13183 ⟨7, by decide⟩).energy) (xi := (321556071838237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13183 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13183]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13183])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13183) (a := (20956313170571 / 25000000000000 : ℝ)) (b := (39044623553 / 25000000000000 : ℝ)) (q := (1097745877671 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13183])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13183])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13183]

theorem cert13183_8 : CellCertificate 13183 (873671681546847 / 10000000000000000 : ℝ) (1593277378341313 / 1000000000000000000 : ℝ) (321556071838237 / 10000000000000000 : ℝ)
    (cell13183 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · have h := gap_lower (n := 13183) (a := (83790537306491 / 100000000000000 : ℝ)) (b := (39044623553 / 25000000000000 : ℝ)) (q := (439099155983 / 20000000000000 : ℝ))
      (E := (cell13183 ⟨8, by decide⟩).energy) (xi := (321556071838237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13183 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13183]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13183])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13183) (a := (83790537306491 / 100000000000000 : ℝ)) (b := (39044623553 / 25000000000000 : ℝ)) (q := (439099155983 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13183])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13183])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13183]

theorem cert13183_9 : CellCertificate 13183 (873671681546847 / 10000000000000000 : ℝ) (1593277378341313 / 1000000000000000000 : ℝ) (321556071838237 / 10000000000000000 : ℝ)
    (cell13183 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · have h := gap_lower (n := 13183) (a := (83755846493521 / 100000000000000 : ℝ)) (b := (39044623553 / 25000000000000 : ℝ)) (q := (548874936833 / 25000000000000 : ℝ))
      (E := (cell13183 ⟨9, by decide⟩).energy) (xi := (321556071838237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13183 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13183]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13183])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13183) (a := (83755846493521 / 100000000000000 : ℝ)) (b := (39044623553 / 25000000000000 : ℝ)) (q := (548874936833 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13183])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13183])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13183]

theorem cert13183_10 : CellCertificate 13183 (873671681546847 / 10000000000000000 : ℝ) (1593277378341313 / 1000000000000000000 : ℝ) (321556071838237 / 10000000000000000 : ℝ)
    (cell13183 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · have h := gap_lower (n := 13183) (a := (83721180208449 / 100000000000000 : ℝ)) (b := (39044623553 / 25000000000000 : ℝ)) (q := (2195503780237 / 100000000000000 : ℝ))
      (E := (cell13183 ⟨10, by decide⟩).energy) (xi := (321556071838237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13183 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13183]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13183])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13183) (a := (83721180208449 / 100000000000000 : ℝ)) (b := (39044623553 / 25000000000000 : ℝ)) (q := (2195503780237 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13183])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13183])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13183]

theorem cert13183_11 : CellCertificate 13183 (873671681546847 / 10000000000000000 : ℝ) (1593277378341313 / 1000000000000000000 : ℝ) (321556071838237 / 10000000000000000 : ℝ)
    (cell13183 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · have h := gap_lower (n := 13183) (a := (41843269208267 / 50000000000000 : ℝ)) (b := (39044623553 / 25000000000000 : ℝ)) (q := (2195507768753 / 100000000000000 : ℝ))
      (E := (cell13183 ⟨11, by decide⟩).energy) (xi := (321556071838237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13183 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13183]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13183])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13183) (a := (41843269208267 / 50000000000000 : ℝ)) (b := (39044623553 / 25000000000000 : ℝ)) (q := (2195507768753 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13183])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13183])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13183]

theorem cert13183_12 : CellCertificate 13183 (873671681546847 / 10000000000000000 : ℝ) (1593277378341313 / 1000000000000000000 : ℝ) (321556071838237 / 10000000000000000 : ℝ)
    (cell13183 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · have h := gap_lower (n := 13183) (a := (83651921083213 / 100000000000000 : ℝ)) (b := (39044623553 / 25000000000000 : ℝ)) (q := (2195511835119 / 100000000000000 : ℝ))
      (E := (cell13183 ⟨12, by decide⟩).energy) (xi := (321556071838237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13183 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13183]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13183])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13183) (a := (83651921083213 / 100000000000000 : ℝ)) (b := (39044623553 / 25000000000000 : ℝ)) (q := (2195511835119 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13183])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13183])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13183]

theorem cert13183_13 : CellCertificate 13183 (873671681546847 / 10000000000000000 : ℝ) (1593277378341313 / 1000000000000000000 : ℝ) (321556071838237 / 10000000000000000 : ℝ)
    (cell13183 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · have h := gap_lower (n := 13183) (a := (41808664087053 / 50000000000000 : ℝ)) (b := (39044623553 / 25000000000000 : ℝ)) (q := (274439476339 / 12500000000000 : ℝ))
      (E := (cell13183 ⟨13, by decide⟩).energy) (xi := (321556071838237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13183 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13183]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13183])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13183) (a := (41808664087053 / 50000000000000 : ℝ)) (b := (39044623553 / 25000000000000 : ℝ)) (q := (274439476339 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13183])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13183])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13183]

theorem cert13183_14 : CellCertificate 13183 (873671681546847 / 10000000000000000 : ℝ) (1593277378341313 / 1000000000000000000 : ℝ) (321556071838237 / 10000000000000000 : ℝ)
    (cell13183 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · have h := gap_lower (n := 13183) (a := (8358275965501 / 10000000000000 : ℝ)) (b := (39044623553 / 25000000000000 : ℝ)) (q := (21955198173 / 1000000000000 : ℝ))
      (E := (cell13183 ⟨14, by decide⟩).energy) (xi := (321556071838237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13183 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13183]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13183])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13183) (a := (8358275965501 / 10000000000000 : ℝ)) (b := (39044623553 / 25000000000000 : ℝ)) (q := (21955198173 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13183])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13183])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13183]

theorem cert13183_15 : CellCertificate 13183 (873671681546847 / 10000000000000000 : ℝ) (1593277378341313 / 1000000000000000000 : ℝ) (321556071838237 / 10000000000000000 : ℝ)
    (cell13183 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · have h := gap_lower (n := 13183) (a := (41774107745949 / 50000000000000 : ℝ)) (b := (39044623553 / 25000000000000 : ℝ)) (q := (2195523860183 / 100000000000000 : ℝ))
      (E := (cell13183 ⟨15, by decide⟩).energy) (xi := (321556071838237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13183 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13183]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13183])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13183) (a := (41774107745949 / 50000000000000 : ℝ)) (b := (39044623553 / 25000000000000 : ℝ)) (q := (2195523860183 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13183])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13183])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13183]

theorem cert13183_16 : CellCertificate 13183 (873671681546847 / 10000000000000000 : ℝ) (1593277378341313 / 1000000000000000000 : ℝ) (321556071838237 / 10000000000000000 : ℝ)
    (cell13183 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · have h := gap_lower (n := 13183) (a := (83513695650921 / 100000000000000 : ℝ)) (b := (39044623553 / 25000000000000 : ℝ)) (q := (439105577237 / 20000000000000 : ℝ))
      (E := (cell13183 ⟨16, by decide⟩).energy) (xi := (321556071838237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13183 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13183]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13183])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13183) (a := (83513695650921 / 100000000000000 : ℝ)) (b := (39044623553 / 25000000000000 : ℝ)) (q := (439105577237 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13183])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13183])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13183]

theorem cert13183_17 : CellCertificate 13183 (873671681546847 / 10000000000000000 : ℝ) (1593277378341313 / 1000000000000000000 : ℝ) (321556071838237 / 10000000000000000 : ℝ)
    (cell13183 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · have h := gap_lower (n := 13183) (a := (16695840019681 / 20000000000000 : ℝ)) (b := (39044623553 / 25000000000000 : ℝ)) (q := (137220743753 / 6250000000000 : ℝ))
      (E := (cell13183 ⟨17, by decide⟩).energy) (xi := (321556071838237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13183 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13183]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13183])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13183) (a := (16695840019681 / 20000000000000 : ℝ)) (b := (39044623553 / 25000000000000 : ℝ)) (q := (137220743753 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13183])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13183])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13183]

theorem cert13183_18 : CellCertificate 13183 (873671681546847 / 10000000000000000 : ℝ) (1593277378341313 / 1000000000000000000 : ℝ) (321556071838237 / 10000000000000000 : ℝ)
    (cell13183 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · have h := gap_lower (n := 13183) (a := (5215295550053 / 6250000000000 : ℝ)) (b := (39044623553 / 25000000000000 : ℝ)) (q := (87821436251 / 4000000000000 : ℝ))
      (E := (cell13183 ⟨18, by decide⟩).energy) (xi := (321556071838237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13183 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13183]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13183])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13183) (a := (5215295550053 / 6250000000000 : ℝ)) (b := (39044623553 / 25000000000000 : ℝ)) (q := (87821436251 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13183])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13183])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13183]

theorem cert13183_19 : CellCertificate 13183 (873671681546847 / 10000000000000000 : ℝ) (1593277378341313 / 1000000000000000000 : ℝ) (321556071838237 / 10000000000000000 : ℝ)
    (cell13183 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · have h := gap_lower (n := 13183) (a := (20852570431231 / 25000000000000 : ℝ)) (b := (39044623553 / 25000000000000 : ℝ)) (q := (17564319273 / 800000000000 : ℝ))
      (E := (cell13183 ⟨19, by decide⟩).energy) (xi := (321556071838237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13183 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13183]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13183])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13183) (a := (20852570431231 / 25000000000000 : ℝ)) (b := (39044623553 / 25000000000000 : ℝ)) (q := (17564319273 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13183])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13183])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13183]

theorem cert13184_0 : CellCertificate 13184 (2730142736391 / 31250000000000 : ℝ) (49786140335931 / 31250000000000000 : ℝ) (321531127446711 / 10000000000000000 : ℝ)
    (cell13184 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · have h := gap_lower (n := 13184) (a := (21017234251413 / 25000000000000 : ℝ)) (b := (31233302697 / 20000000000000 : ℝ)) (q := (2195353295207 / 100000000000000 : ℝ))
      (E := (cell13184 ⟨0, by decide⟩).energy) (xi := (321531127446711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13184 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13184]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13184])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13184) (a := (21017234251413 / 25000000000000 : ℝ)) (b := (31233302697 / 20000000000000 : ℝ)) (q := (2195353295207 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13184])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13184])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13184]

theorem cert13184_1 : CellCertificate 13184 (2730142736391 / 31250000000000 : ℝ) (49786140335931 / 31250000000000000 : ℝ) (321531127446711 / 10000000000000000 : ℝ)
    (cell13184 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · have h := gap_lower (n := 13184) (a := (42017024351467 / 50000000000000 : ℝ)) (b := (31233302697 / 20000000000000 : ℝ)) (q := (68604916893 / 3125000000000 : ℝ))
      (E := (cell13184 ⟨1, by decide⟩).energy) (xi := (321531127446711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13184 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13184]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13184])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13184) (a := (42017024351467 / 50000000000000 : ℝ)) (b := (31233302697 / 20000000000000 : ℝ)) (q := (68604916893 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13184])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13184])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13184]

theorem cert13184_2 : CellCertificate 13184 (2730142736391 / 31250000000000 : ℝ) (49786140335931 / 31250000000000000 : ℝ) (321531127446711 / 10000000000000000 : ℝ)
    (cell13184 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · have h := gap_lower (n := 13184) (a := (16799837042539 / 20000000000000 : ℝ)) (b := (31233302697 / 20000000000000 : ℝ)) (q := (2195361333991 / 100000000000000 : ℝ))
      (E := (cell13184 ⟨2, by decide⟩).energy) (xi := (321531127446711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13184 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13184]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13184])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13184) (a := (16799837042539 / 20000000000000 : ℝ)) (b := (31233302697 / 20000000000000 : ℝ)) (q := (2195361333991 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13184])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13184])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13184]

theorem cert13184_3 : CellCertificate 13184 (2730142736391 / 31250000000000 : ℝ) (49786140335931 / 31250000000000000 : ℝ) (321531127446711 / 10000000000000000 : ℝ)
    (cell13184 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · have h := gap_lower (n := 13184) (a := (5247771656169 / 6250000000000 : ℝ)) (b := (31233302697 / 20000000000000 : ℝ)) (q := (27442066771 / 1250000000000 : ℝ))
      (E := (cell13184 ⟨3, by decide⟩).energy) (xi := (321531127446711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13184 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13184]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13184])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13184) (a := (5247771656169 / 6250000000000 : ℝ)) (b := (31233302697 / 20000000000000 : ℝ)) (q := (27442066771 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13184])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13184])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13184]

theorem cert13184_4 : CellCertificate 13184 (2730142736391 / 31250000000000 : ℝ) (49786140335931 / 31250000000000000 : ℝ) (321531127446711 / 10000000000000000 : ℝ)
    (cell13184 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · have h := gap_lower (n := 13184) (a := (2098238313123 / 2500000000000 : ℝ)) (b := (31233302697 / 20000000000000 : ℝ)) (q := (1097684685881 / 50000000000000 : ℝ))
      (E := (cell13184 ⟨4, by decide⟩).energy) (xi := (321531127446711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13184 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13184]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13184])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13184) (a := (2098238313123 / 2500000000000 : ℝ)) (b := (31233302697 / 20000000000000 : ℝ)) (q := (1097684685881 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13184])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13184])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13184]

theorem cert13184_5 : CellCertificate 13184 (2730142736391 / 31250000000000 : ℝ) (49786140335931 / 31250000000000000 : ℝ) (321531127446711 / 10000000000000000 : ℝ)
    (cell13184 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · have h := gap_lower (n := 13184) (a := (83894743255491 / 100000000000000 : ℝ)) (b := (31233302697 / 20000000000000 : ℝ)) (q := (17562986993 / 800000000000 : ℝ))
      (E := (cell13184 ⟨5, by decide⟩).energy) (xi := (321531127446711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13184 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13184]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13184])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13184) (a := (83894743255491 / 100000000000000 : ℝ)) (b := (31233302697 / 20000000000000 : ℝ)) (q := (17562986993 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13184])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13184])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13184]

theorem cert13184_6 : CellCertificate 13184 (2730142736391 / 31250000000000 : ℝ) (49786140335931 / 31250000000000000 : ℝ) (321531127446711 / 10000000000000000 : ℝ)
    (cell13184 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · have h := gap_lower (n := 13184) (a := (83859978654753 / 100000000000000 : ℝ)) (b := (31233302697 / 20000000000000 : ℝ)) (q := (2195377414303 / 100000000000000 : ℝ))
      (E := (cell13184 ⟨6, by decide⟩).energy) (xi := (321531127446711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13184 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13184]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13184])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13184) (a := (83859978654753 / 100000000000000 : ℝ)) (b := (31233302697 / 20000000000000 : ℝ)) (q := (2195377414303 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13184])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13184])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13184]

theorem cert13184_7 : CellCertificate 13184 (2730142736391 / 31250000000000 : ℝ) (49786140335931 / 31250000000000000 : ℝ) (321531127446711 / 10000000000000000 : ℝ)
    (cell13184 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · have h := gap_lower (n := 13184) (a := (83825238687231 / 100000000000000 : ℝ)) (b := (31233302697 / 20000000000000 : ℝ)) (q := (2195381441627 / 100000000000000 : ℝ))
      (E := (cell13184 ⟨7, by decide⟩).energy) (xi := (321531127446711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13184 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13184]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13184])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13184) (a := (83825238687231 / 100000000000000 : ℝ)) (b := (31233302697 / 20000000000000 : ℝ)) (q := (2195381441627 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13184])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13184])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13184]

theorem cert13184_8 : CellCertificate 13184 (2730142736391 / 31250000000000 : ℝ) (49786140335931 / 31250000000000000 : ℝ) (321531127446711 / 10000000000000000 : ℝ)
    (cell13184 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · have h := gap_lower (n := 13184) (a := (83790523317631 / 100000000000000 : ℝ)) (b := (31233302697 / 20000000000000 : ℝ)) (q := (68605793909 / 3125000000000 : ℝ))
      (E := (cell13184 ⟨8, by decide⟩).energy) (xi := (321531127446711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13184 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13184]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13184])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13184) (a := (83790523317631 / 100000000000000 : ℝ)) (b := (31233302697 / 20000000000000 : ℝ)) (q := (68605793909 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13184])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13184])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13184]

theorem cert13184_9 : CellCertificate 13184 (2730142736391 / 31250000000000 : ℝ) (49786140335931 / 31250000000000000 : ℝ) (321531127446711 / 10000000000000000 : ℝ)
    (cell13184 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · have h := gap_lower (n := 13184) (a := (83755832510849 / 100000000000000 : ℝ)) (b := (31233302697 / 20000000000000 : ℝ)) (q := (274423678441 / 12500000000000 : ℝ))
      (E := (cell13184 ⟨9, by decide⟩).energy) (xi := (321531127446711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13184 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13184]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13184])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13184) (a := (83755832510849 / 100000000000000 : ℝ)) (b := (31233302697 / 20000000000000 : ℝ)) (q := (274423678441 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13184])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13184])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13184]

theorem cert13184_10 : CellCertificate 13184 (2730142736391 / 31250000000000 : ℝ) (49786140335931 / 31250000000000000 : ℝ) (321531127446711 / 10000000000000000 : ℝ)
    (cell13184 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · have h := gap_lower (n := 13184) (a := (83721166231959 / 100000000000000 : ℝ)) (b := (31233302697 / 20000000000000 : ℝ)) (q := (2195393457459 / 100000000000000 : ℝ))
      (E := (cell13184 ⟨10, by decide⟩).energy) (xi := (321531127446711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13184 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13184]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13184])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13184) (a := (83721166231959 / 100000000000000 : ℝ)) (b := (31233302697 / 20000000000000 : ℝ)) (q := (2195393457459 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13184])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13184])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13184]

theorem cert13184_11 : CellCertificate 13184 (2730142736391 / 31250000000000 : ℝ) (49786140335931 / 31250000000000000 : ℝ) (321531127446711 / 10000000000000000 : ℝ)
    (cell13184 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · have h := gap_lower (n := 13184) (a := (4184326222311 / 5000000000000 : ℝ)) (b := (31233302697 / 20000000000000 : ℝ)) (q := (1097698750581 / 50000000000000 : ℝ))
      (E := (cell13184 ⟨11, by decide⟩).energy) (xi := (321531127446711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13184 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13184]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13184])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13184) (a := (4184326222311 / 5000000000000 : ℝ)) (b := (31233302697 / 20000000000000 : ℝ)) (q := (1097698750581 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13184])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13184])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13184]

theorem cert13184_12 : CellCertificate 13184 (2730142736391 / 31250000000000 : ℝ) (49786140335931 / 31250000000000000 : ℝ) (321531127446711 / 10000000000000000 : ℝ)
    (cell13184 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · have h := gap_lower (n := 13184) (a := (83651907119071 / 100000000000000 : ℝ)) (b := (31233302697 / 20000000000000 : ℝ)) (q := (2195401506533 / 100000000000000 : ℝ))
      (E := (cell13184 ⟨12, by decide⟩).energy) (xi := (321531127446711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13184 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13184]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13184])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13184) (a := (83651907119071 / 100000000000000 : ℝ)) (b := (31233302697 / 20000000000000 : ℝ)) (q := (2195401506533 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13184])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13184])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13184]

theorem cert13184_13 : CellCertificate 13184 (2730142736391 / 31250000000000 : ℝ) (49786140335931 / 31250000000000000 : ℝ) (321531127446711 / 10000000000000000 : ℝ)
    (cell13184 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · have h := gap_lower (n := 13184) (a := (8361731421613 / 10000000000000 : ℝ)) (b := (31233302697 / 20000000000000 : ℝ)) (q := (2195405479291 / 100000000000000 : ℝ))
      (E := (cell13184 ⟨13, by decide⟩).energy) (xi := (321531127446711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13184 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13184]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13184])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13184) (a := (8361731421613 / 10000000000000 : ℝ)) (b := (31233302697 / 20000000000000 : ℝ)) (q := (2195405479291 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13184])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13184])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13184]

theorem cert13184_14 : CellCertificate 13184 (2730142736391 / 31250000000000 : ℝ) (49786140335931 / 31250000000000000 : ℝ) (321531127446711 / 10000000000000000 : ℝ)
    (cell13184 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · have h := gap_lower (n := 13184) (a := (41791372851597 / 50000000000000 : ℝ)) (b := (31233302697 / 20000000000000 : ℝ)) (q := (2195409541277 / 100000000000000 : ℝ))
      (E := (cell13184 ⟨14, by decide⟩).energy) (xi := (321531127446711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13184 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13184]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13184])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13184) (a := (41791372851597 / 50000000000000 : ℝ)) (b := (31233302697 / 20000000000000 : ℝ)) (q := (2195409541277 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13184])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13184])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13184]

theorem cert13184_15 : CellCertificate 13184 (2730142736391 / 31250000000000 : ℝ) (49786140335931 / 31250000000000000 : ℝ) (321531127446711 / 10000000000000000 : ℝ)
    (cell13184 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · have h := gap_lower (n := 13184) (a := (83548201546237 / 100000000000000 : ℝ)) (b := (31233302697 / 20000000000000 : ℝ)) (q := (548853380809 / 25000000000000 : ℝ))
      (E := (cell13184 ⟨15, by decide⟩).energy) (xi := (321531127446711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13184 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13184]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13184])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13184) (a := (83548201546237 / 100000000000000 : ℝ)) (b := (31233302697 / 20000000000000 : ℝ)) (q := (548853380809 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13184])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13184])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13184]

theorem cert13184_16 : CellCertificate 13184 (2730142736391 / 31250000000000 : ℝ) (49786140335931 / 31250000000000000 : ℝ) (321531127446711 / 10000000000000000 : ℝ)
    (cell13184 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · have h := gap_lower (n := 13184) (a := (8351368171141 / 10000000000000 : ℝ)) (b := (31233302697 / 20000000000000 : ℝ)) (q := (137213596659 / 6250000000000 : ℝ))
      (E := (cell13184 ⟨16, by decide⟩).energy) (xi := (321531127446711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13184 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13184]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13184])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13184) (a := (8351368171141 / 10000000000000 : ℝ)) (b := (31233302697 / 20000000000000 : ℝ)) (q := (137213596659 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13184])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13184])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13184]

theorem cert13184_17 : CellCertificate 13184 (2730142736391 / 31250000000000 : ℝ) (49786140335931 / 31250000000000000 : ℝ) (321531127446711 / 10000000000000000 : ℝ)
    (cell13184 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · have h := gap_lower (n := 13184) (a := (41739593082519 / 50000000000000 : ℝ)) (b := (31233302697 / 20000000000000 : ℝ)) (q := (2195421557761 / 100000000000000 : ℝ))
      (E := (cell13184 ⟨17, by decide⟩).energy) (xi := (321531127446711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13184 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13184]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13184])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13184) (a := (41739593082519 / 50000000000000 : ℝ)) (b := (31233302697 / 20000000000000 : ℝ)) (q := (2195421557761 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13184])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13184])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13184]

theorem cert13184_18 : CellCertificate 13184 (2730142736391 / 31250000000000 : ℝ) (49786140335931 / 31250000000000000 : ℝ) (321531127446711 / 10000000000000000 : ℝ)
    (cell13184 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · have h := gap_lower (n := 13184) (a := (83444714873621 / 100000000000000 : ℝ)) (b := (31233302697 / 20000000000000 : ℝ)) (q := (1097712780693 / 50000000000000 : ℝ))
      (E := (cell13184 ⟨18, by decide⟩).energy) (xi := (321531127446711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13184 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13184]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13184])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13184) (a := (83444714873621 / 100000000000000 : ℝ)) (b := (31233302697 / 20000000000000 : ℝ)) (q := (1097712780693 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13184])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13184])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13184]

theorem cert13184_19 : CellCertificate 13184 (2730142736391 / 31250000000000 : ℝ) (49786140335931 / 31250000000000000 : ℝ) (321531127446711 / 10000000000000000 : ℝ)
    (cell13184 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · have h := gap_lower (n := 13184) (a := (8341026780383 / 10000000000000 : ℝ)) (b := (31233302697 / 20000000000000 : ℝ)) (q := (439085923997 / 20000000000000 : ℝ))
      (E := (cell13184 ⟨19, by decide⟩).energy) (xi := (321531127446711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13184 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13184]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13184])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13184) (a := (8341026780383 / 10000000000000 : ℝ)) (b := (31233302697 / 20000000000000 : ℝ)) (q := (439085923997 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13184])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13184])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13184]

theorem cert13185_0 : CellCertificate 13185 (174723934703423 / 2000000000000000 : ℝ) (49782363171913 / 31250000000000000 : ℝ) (160753093474563 / 5000000000000000 : ℝ)
    (cell13185 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · have h := gap_lower (n := 13185) (a := (84068922969223 / 100000000000000 : ℝ)) (b := (78077267301 / 50000000000000 : ℝ)) (q := (2195243000093 / 100000000000000 : ℝ))
      (E := (cell13185 ⟨0, by decide⟩).energy) (xi := (160753093474563 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13185 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13185]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13185])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13185) (a := (84068922969223 / 100000000000000 : ℝ)) (b := (78077267301 / 50000000000000 : ℝ)) (q := (2195243000093 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13185])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13185])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13185]

theorem cert13185_1 : CellCertificate 13185 (174723934703423 / 2000000000000000 : ℝ) (49782363171913 / 31250000000000000 : ℝ) (160753093474563 / 5000000000000000 : ℝ)
    (cell13185 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · have h := gap_lower (n := 13185) (a := (84034034672737 / 100000000000000 : ℝ)) (b := (78077267301 / 50000000000000 : ℝ)) (q := (439049408413 / 20000000000000 : ℝ))
      (E := (cell13185 ⟨1, by decide⟩).energy) (xi := (160753093474563 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13185 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13185]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13185])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13185) (a := (84034034672737 / 100000000000000 : ℝ)) (b := (78077267301 / 50000000000000 : ℝ)) (q := (439049408413 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13185])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13185])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13185]

theorem cert13185_2 : CellCertificate 13185 (174723934703423 / 2000000000000000 : ℝ) (49782363171913 / 31250000000000000 : ℝ) (160753093474563 / 5000000000000000 : ℝ)
    (cell13185 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · have h := gap_lower (n := 13185) (a := (83999171188723 / 100000000000000 : ℝ)) (b := (78077267301 / 50000000000000 : ℝ)) (q := (2195251032131 / 100000000000000 : ℝ))
      (E := (cell13185 ⟨2, by decide⟩).energy) (xi := (160753093474563 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13185 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13185]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13185])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13185) (a := (83999171188723 / 100000000000000 : ℝ)) (b := (78077267301 / 50000000000000 : ℝ)) (q := (2195251032131 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13185])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13185])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13185]

theorem cert13185_3 : CellCertificate 13185 (174723934703423 / 2000000000000000 : ℝ) (49782363171913 / 31250000000000000 : ℝ) (160753093474563 / 5000000000000000 : ℝ)
    (cell13185 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · have h := gap_lower (n := 13185) (a := (10495541560119 / 12500000000000 : ℝ)) (b := (78077267301 / 50000000000000 : ℝ)) (q := (1097627518259 / 50000000000000 : ℝ))
      (E := (cell13185 ⟨3, by decide⟩).energy) (xi := (160753093474563 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13185 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13185]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13185])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13185) (a := (10495541560119 / 12500000000000 : ℝ)) (b := (78077267301 / 50000000000000 : ℝ)) (q := (1097627518259 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13185])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13185])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13185]

theorem cert13185_4 : CellCertificate 13185 (174723934703423 / 2000000000000000 : ℝ) (49782363171913 / 31250000000000000 : ℝ) (160753093474563 / 5000000000000000 : ℝ)
    (cell13185 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · have h := gap_lower (n := 13185) (a := (41964759256691 / 50000000000000 : ℝ)) (b := (78077267301 / 50000000000000 : ℝ)) (q := (1097629531673 / 50000000000000 : ℝ))
      (E := (cell13185 ⟨4, by decide⟩).energy) (xi := (160753093474563 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13185 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13185]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13185])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13185) (a := (41964759256691 / 50000000000000 : ℝ)) (b := (78077267301 / 50000000000000 : ℝ)) (q := (1097629531673 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13185])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13185])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13185]

theorem cert13185_5 : CellCertificate 13185 (174723934703423 / 2000000000000000 : ℝ) (49782363171913 / 31250000000000000 : ℝ) (160753093474563 / 5000000000000000 : ℝ)
    (cell13185 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · have h := gap_lower (n := 13185) (a := (41947364625081 / 50000000000000 : ℝ)) (b := (78077267301 / 50000000000000 : ℝ)) (q := (2195263062501 / 100000000000000 : ℝ))
      (E := (cell13185 ⟨5, by decide⟩).energy) (xi := (160753093474563 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13185 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13185]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13185])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13185) (a := (41947364625081 / 50000000000000 : ℝ)) (b := (78077267301 / 50000000000000 : ℝ)) (q := (2195263062501 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13185])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13185])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13185]

theorem cert13185_6 : CellCertificate 13185 (174723934703423 / 2000000000000000 : ℝ) (49782363171913 / 31250000000000000 : ℝ) (160753093474563 / 5000000000000000 : ℝ)
    (cell13185 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · have h := gap_lower (n := 13185) (a := (20964991163907 / 25000000000000 : ℝ)) (b := (78077267301 / 50000000000000 : ℝ)) (q := (2195267099517 / 100000000000000 : ℝ))
      (E := (cell13185 ⟨6, by decide⟩).energy) (xi := (160753093474563 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13185 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13185]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13185])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13185) (a := (20964991163907 / 25000000000000 : ℝ)) (b := (78077267301 / 50000000000000 : ℝ)) (q := (2195267099517 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13185])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13185])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13185]

theorem cert13185_7 : CellCertificate 13185 (174723934703423 / 2000000000000000 : ℝ) (49782363171913 / 31250000000000000 : ℝ) (160753093474563 / 5000000000000000 : ℝ)
    (cell13185 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · have h := gap_lower (n := 13185) (a := (83825224694303 / 100000000000000 : ℝ)) (b := (78077267301 / 50000000000000 : ℝ)) (q := (137204445233 / 6250000000000 : ℝ))
      (E := (cell13185 ⟨7, by decide⟩).energy) (xi := (160753093474563 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13185 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13185]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13185])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13185) (a := (83825224694303 / 100000000000000 : ℝ)) (b := (78077267301 / 50000000000000 : ℝ)) (q := (137204445233 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13185])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13185])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13185]

theorem cert13185_8 : CellCertificate 13185 (174723934703423 / 2000000000000000 : ℝ) (49782363171913 / 31250000000000000 : ℝ) (160753093474563 / 5000000000000000 : ℝ)
    (cell13185 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · have h := gap_lower (n := 13185) (a := (5236906833181 / 6250000000000 : ℝ)) (b := (78077267301 / 50000000000000 : ℝ)) (q := (439055028433 / 20000000000000 : ℝ))
      (E := (cell13185 ⟨8, by decide⟩).energy) (xi := (160753093474563 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13185 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13185]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13185])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13185) (a := (5236906833181 / 6250000000000 : ℝ)) (b := (78077267301 / 50000000000000 : ℝ)) (q := (439055028433 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13185])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13185])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13185]

theorem cert13185_9 : CellCertificate 13185 (174723934703423 / 2000000000000000 : ℝ) (49782363171913 / 31250000000000000 : ℝ) (160753093474563 / 5000000000000000 : ℝ)
    (cell13185 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · have h := gap_lower (n := 13185) (a := (83755818530301 / 100000000000000 : ℝ)) (b := (78077267301 / 50000000000000 : ℝ)) (q := (274409895201 / 12500000000000 : ℝ))
      (E := (cell13185 ⟨9, by decide⟩).energy) (xi := (160753093474563 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13185 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13185]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13185])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13185) (a := (83755818530301 / 100000000000000 : ℝ)) (b := (78077267301 / 50000000000000 : ℝ)) (q := (274409895201 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13185])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13185])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13185]

theorem cert13185_10 : CellCertificate 13185 (174723934703423 / 2000000000000000 : ℝ) (49782363171913 / 31250000000000000 : ℝ) (160753093474563 / 5000000000000000 : ℝ)
    (cell13185 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · have h := gap_lower (n := 13185) (a := (10465144032199 / 12500000000000 : ℝ)) (b := (78077267301 / 50000000000000 : ℝ)) (q := (1097641565249 / 50000000000000 : ℝ))
      (E := (cell13185 ⟨10, by decide⟩).energy) (xi := (160753093474563 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13185 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13185]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13185])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13185) (a := (10465144032199 / 12500000000000 : ℝ)) (b := (78077267301 / 50000000000000 : ℝ)) (q := (1097641565249 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13185])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13185])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13185]

theorem cert13185_11 : CellCertificate 13185 (174723934703423 / 2000000000000000 : ℝ) (49782363171913 / 31250000000000000 : ℝ) (160753093474563 / 5000000000000000 : ℝ)
    (cell13185 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · have h := gap_lower (n := 13185) (a := (83686510478029 / 100000000000000 : ℝ)) (b := (78077267301 / 50000000000000 : ℝ)) (q := (1097643585637 / 50000000000000 : ℝ))
      (E := (cell13185 ⟨11, by decide⟩).energy) (xi := (160753093474563 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13185 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13185]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13185])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13185) (a := (83686510478029 / 100000000000000 : ℝ)) (b := (78077267301 / 50000000000000 : ℝ)) (q := (1097643585637 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13185])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13185])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13185]

theorem cert13185_12 : CellCertificate 13185 (174723934703423 / 2000000000000000 : ℝ) (49782363171913 / 31250000000000000 : ℝ) (160753093474563 / 5000000000000000 : ℝ)
    (cell13185 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · have h := gap_lower (n := 13185) (a := (1673037863141 / 2000000000000 : ℝ)) (b := (78077267301 / 50000000000000 : ℝ)) (q := (1097645586883 / 50000000000000 : ℝ))
      (E := (cell13185 ⟨12, by decide⟩).energy) (xi := (160753093474563 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13185 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13185]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13185])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13185) (a := (1673037863141 / 2000000000000 : ℝ)) (b := (78077267301 / 50000000000000 : ℝ)) (q := (1097645586883 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13185])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13185])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13185]

theorem cert13185_13 : CellCertificate 13185 (174723934703423 / 2000000000000000 : ℝ) (49782363171913 / 31250000000000000 : ℝ) (160753093474563 / 5000000000000000 : ℝ)
    (cell13185 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · have h := gap_lower (n := 13185) (a := (41808650130137 / 50000000000000 : ℝ)) (b := (78077267301 / 50000000000000 : ℝ)) (q := (548823800463 / 25000000000000 : ℝ))
      (E := (cell13185 ⟨13, by decide⟩).energy) (xi := (160753093474563 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13185 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13185]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13185])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13185) (a := (41808650130137 / 50000000000000 : ℝ)) (b := (78077267301 / 50000000000000 : ℝ)) (q := (548823800463 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13185])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13185])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13185]

theorem cert13185_14 : CellCertificate 13185 (174723934703423 / 2000000000000000 : ℝ) (49782363171913 / 31250000000000000 : ℝ) (160753093474563 / 5000000000000000 : ℝ)
    (cell13185 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · have h := gap_lower (n := 13185) (a := (83582731753497 / 100000000000000 : ℝ)) (b := (78077267301 / 50000000000000 : ℝ)) (q := (2195299202891 / 100000000000000 : ℝ))
      (E := (cell13185 ⟨14, by decide⟩).energy) (xi := (160753093474563 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13185 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13185]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13185])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13185) (a := (83582731753497 / 100000000000000 : ℝ)) (b := (78077267301 / 50000000000000 : ℝ)) (q := (2195299202891 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13185])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13185])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13185]

theorem cert13185_15 : CellCertificate 13185 (174723934703423 / 2000000000000000 : ℝ) (49782363171913 / 31250000000000000 : ℝ) (160753093474563 / 5000000000000000 : ℝ)
    (cell13185 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · have h := gap_lower (n := 13185) (a := (16709637520539 / 20000000000000 : ℝ)) (b := (78077267301 / 50000000000000 : ℝ)) (q := (2195303240317 / 100000000000000 : ℝ))
      (E := (cell13185 ⟨15, by decide⟩).energy) (xi := (160753093474563 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13185 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13185]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13185])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13185) (a := (16709637520539 / 20000000000000 : ℝ)) (b := (78077267301 / 50000000000000 : ℝ)) (q := (2195303240317 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13185])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13185])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13185]

theorem cert13185_16 : CellCertificate 13185 (174723934703423 / 2000000000000000 : ℝ) (49782363171913 / 31250000000000000 : ℝ) (160753093474563 / 5000000000000000 : ℝ)
    (cell13185 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · have h := gap_lower (n := 13185) (a := (1304901058969 / 1562500000000 : ℝ)) (b := (78077267301 / 50000000000000 : ℝ)) (q := (2195307260957 / 100000000000000 : ℝ))
      (E := (cell13185 ⟨16, by decide⟩).energy) (xi := (160753093474563 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13185 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13185]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13185])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13185) (a := (1304901058969 / 1562500000000 : ℝ)) (b := (78077267301 / 50000000000000 : ℝ)) (q := (2195307260957 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13185])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13185])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13185]

theorem cert13185_17 : CellCertificate 13185 (174723934703423 / 2000000000000000 : ℝ) (49782363171913 / 31250000000000000 : ℝ) (160753093474563 / 5000000000000000 : ℝ)
    (cell13185 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · have h := gap_lower (n := 13185) (a := (20869793058447 / 25000000000000 : ℝ)) (b := (78077267301 / 50000000000000 : ℝ)) (q := (43906225391 / 2000000000000 : ℝ))
      (E := (cell13185 ⟨17, by decide⟩).energy) (xi := (160753093474563 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13185 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13185]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13185])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13185) (a := (20869793058447 / 25000000000000 : ℝ)) (b := (78077267301 / 50000000000000 : ℝ)) (q := (43906225391 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13185])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13185])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13185]

theorem cert13185_18 : CellCertificate 13185 (174723934703423 / 2000000000000000 : ℝ) (49782363171913 / 31250000000000000 : ℝ) (160753093474563 / 5000000000000000 : ℝ)
    (cell13185 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · have h := gap_lower (n := 13185) (a := (20861175237127 / 25000000000000 : ℝ)) (b := (78077267301 / 50000000000000 : ℝ)) (q := (2195315270601 / 100000000000000 : ℝ))
      (E := (cell13185 ⟨18, by decide⟩).energy) (xi := (160753093474563 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13185 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13185]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13185])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13185) (a := (20861175237127 / 25000000000000 : ℝ)) (b := (78077267301 / 50000000000000 : ℝ)) (q := (2195315270601 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13185])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13185])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13185]

theorem cert13185_19 : CellCertificate 13185 (174723934703423 / 2000000000000000 : ℝ) (49782363171913 / 31250000000000000 : ℝ) (160753093474563 / 5000000000000000 : ℝ)
    (cell13185 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · have h := gap_lower (n := 13185) (a := (1668205077697 / 2000000000000 : ℝ)) (b := (78077267301 / 50000000000000 : ℝ)) (q := (2195319268369 / 100000000000000 : ℝ))
      (E := (cell13185 ⟨19, by decide⟩).energy) (xi := (160753093474563 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13185 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13185]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13185])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13185) (a := (1668205077697 / 2000000000000 : ℝ)) (b := (78077267301 / 50000000000000 : ℝ)) (q := (2195319268369 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13185])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13185])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13185]

theorem cert13186_0 : CellCertificate 13186 (87359367516197 / 1000000000000000 : ℝ) (1592914770591411 / 1000000000000000000 : ℝ) (160740625172261 / 5000000000000000 : ℝ)
    (cell13186 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · have h := gap_lower (n := 13186) (a := (42034454467463 / 50000000000000 : ℝ)) (b := (78071278781 / 50000000000000 : ℝ)) (q := (1097566379323 / 50000000000000 : ℝ))
      (E := (cell13186 ⟨0, by decide⟩).energy) (xi := (160740625172261 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13186 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13186]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13186])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13186) (a := (42034454467463 / 50000000000000 : ℝ)) (b := (78071278781 / 50000000000000 : ℝ)) (q := (1097566379323 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13186])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13186])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13186]

theorem cert13186_1 : CellCertificate 13186 (87359367516197 / 1000000000000000 : ℝ) (1592914770591411 / 1000000000000000000 : ℝ) (160740625172261 / 5000000000000000 : ℝ)
    (cell13186 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · have h := gap_lower (n := 13186) (a := (8403402064467 / 10000000000000 : ℝ)) (b := (78071278781 / 50000000000000 : ℝ)) (q := (1097568369683 / 50000000000000 : ℝ))
      (E := (cell13186 ⟨1, by decide⟩).energy) (xi := (160740625172261 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13186 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13186]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13186])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13186) (a := (8403402064467 / 10000000000000 : ℝ)) (b := (78071278781 / 50000000000000 : ℝ)) (q := (1097568369683 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13186])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13186])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13186]

theorem cert13186_2 : CellCertificate 13186 (87359367516197 / 1000000000000000 : ℝ) (1592914770591411 / 1000000000000000000 : ℝ) (160740625172261 / 5000000000000000 : ℝ)
    (cell13186 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · have h := gap_lower (n := 13186) (a := (83999157166881 / 100000000000000 : ℝ)) (b := (78071278781 / 50000000000000 : ℝ)) (q := (2195140783987 / 100000000000000 : ℝ))
      (E := (cell13186 ⟨2, by decide⟩).energy) (xi := (160740625172261 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13186 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13186]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13186])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13186) (a := (83999157166881 / 100000000000000 : ℝ)) (b := (78071278781 / 50000000000000 : ℝ)) (q := (2195140783987 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13186])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13186])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13186]

theorem cert13186_3 : CellCertificate 13186 (87359367516197 / 1000000000000000 : ℝ) (1592914770591411 / 1000000000000000000 : ℝ) (160740625172261 / 5000000000000000 : ℝ)
    (cell13186 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · have h := gap_lower (n := 13186) (a := (83964318465329 / 100000000000000 : ℝ)) (b := (78071278781 / 50000000000000 : ℝ)) (q := (2195144785097 / 100000000000000 : ℝ))
      (E := (cell13186 ⟨3, by decide⟩).energy) (xi := (160740625172261 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13186 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13186]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13186])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13186) (a := (83964318465329 / 100000000000000 : ℝ)) (b := (78071278781 / 50000000000000 : ℝ)) (q := (2195144785097 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13186])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13186])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13186]

theorem cert13186_4 : CellCertificate 13186 (87359367516197 / 1000000000000000 : ℝ) (1592914770591411 / 1000000000000000000 : ℝ) (160740625172261 / 5000000000000000 : ℝ)
    (cell13186 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · have h := gap_lower (n := 13186) (a := (83929504503973 / 100000000000000 : ℝ)) (b := (78071278781 / 50000000000000 : ℝ)) (q := (2195148808693 / 100000000000000 : ℝ))
      (E := (cell13186 ⟨4, by decide⟩).energy) (xi := (160740625172261 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13186 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13186]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13186])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13186) (a := (83929504503973 / 100000000000000 : ℝ)) (b := (78071278781 / 50000000000000 : ℝ)) (q := (2195148808693 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13186])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13186])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13186]

theorem cert13186_5 : CellCertificate 13186 (87359367516197 / 1000000000000000 : ℝ) (1592914770591411 / 1000000000000000000 : ℝ) (160740625172261 / 5000000000000000 : ℝ)
    (cell13186 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · have h := gap_lower (n := 13186) (a := (1048683940587 / 1250000000000 : ℝ)) (b := (78071278781 / 50000000000000 : ℝ)) (q := (439030560933 / 20000000000000 : ℝ))
      (E := (cell13186 ⟨5, by decide⟩).energy) (xi := (160740625172261 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13186 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13186]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13186])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13186) (a := (1048683940587 / 1250000000000 : ℝ)) (b := (78071278781 / 50000000000000 : ℝ)) (q := (439030560933 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13186])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13186])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13186]

theorem cert13186_6 : CellCertificate 13186 (87359367516197 / 1000000000000000 : ℝ) (1592914770591411 / 1000000000000000000 : ℝ) (160740625172261 / 5000000000000000 : ℝ)
    (cell13186 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · have h := gap_lower (n := 13186) (a := (83859950658629 / 100000000000000 : ℝ)) (b := (78071278781 / 50000000000000 : ℝ)) (q := (2195156838543 / 100000000000000 : ℝ))
      (E := (cell13186 ⟨6, by decide⟩).energy) (xi := (160740625172261 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13186 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13186]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13186])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13186) (a := (83859950658629 / 100000000000000 : ℝ)) (b := (78071278781 / 50000000000000 : ℝ)) (q := (2195156838543 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13186])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13186])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13186]

theorem cert13186_7 : CellCertificate 13186 (87359367516197 / 1000000000000000 : ℝ) (1592914770591411 / 1000000000000000000 : ℝ) (160740625172261 / 5000000000000000 : ℝ)
    (cell13186 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · have h := gap_lower (n := 13186) (a := (83825210703501 / 100000000000000 : ℝ)) (b := (78071278781 / 50000000000000 : ℝ)) (q := (137197553729 / 6250000000000 : ℝ))
      (E := (cell13186 ⟨7, by decide⟩).energy) (xi := (160740625172261 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13186 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13186]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13186])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13186) (a := (83825210703501 / 100000000000000 : ℝ)) (b := (78071278781 / 50000000000000 : ℝ)) (q := (137197553729 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13186])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13186])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13186]

theorem cert13186_8 : CellCertificate 13186 (87359367516197 / 1000000000000000 : ℝ) (1592914770591411 / 1000000000000000000 : ℝ) (160740625172261 / 5000000000000000 : ℝ)
    (cell13186 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · have h := gap_lower (n := 13186) (a := (16758099069257 / 20000000000000 : ℝ)) (b := (78071278781 / 50000000000000 : ℝ)) (q := (2195164875059 / 100000000000000 : ℝ))
      (E := (cell13186 ⟨8, by decide⟩).energy) (xi := (160740625172261 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13186 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13186]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13186])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13186) (a := (16758099069257 / 20000000000000 : ℝ)) (b := (78071278781 / 50000000000000 : ℝ)) (q := (2195164875059 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13186])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13186])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13186]

theorem cert13186_9 : CellCertificate 13186 (87359367516197 / 1000000000000000 : ℝ) (1592914770591411 / 1000000000000000000 : ℝ) (160740625172261 / 5000000000000000 : ℝ)
    (cell13186 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · have h := gap_lower (n := 13186) (a := (134009287283 / 160000000000 : ℝ)) (b := (78071278781 / 50000000000000 : ℝ)) (q := (1097584445753 / 50000000000000 : ℝ))
      (E := (cell13186 ⟨9, by decide⟩).energy) (xi := (160740625172261 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13186 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13186]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13186])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13186) (a := (134009287283 / 160000000000 : ℝ)) (b := (78071278781 / 50000000000000 : ℝ)) (q := (1097584445753 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13186])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13186])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13186]

theorem cert13186_10 : CellCertificate 13186 (87359367516197 / 1000000000000000 : ℝ) (1592914770591411 / 1000000000000000000 : ℝ) (160740625172261 / 5000000000000000 : ℝ)
    (cell13186 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · have h := gap_lower (n := 13186) (a := (83721138285347 / 100000000000000 : ℝ)) (b := (78071278781 / 50000000000000 : ℝ)) (q := (2195172857447 / 100000000000000 : ℝ))
      (E := (cell13186 ⟨10, by decide⟩).energy) (xi := (160740625172261 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13186 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13186]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13186])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13186) (a := (83721138285347 / 100000000000000 : ℝ)) (b := (78071278781 / 50000000000000 : ℝ)) (q := (2195172857447 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13186])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13186])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13186]

theorem cert13186_11 : CellCertificate 13186 (87359367516197 / 1000000000000000 : ℝ) (1592914770591411 / 1000000000000000000 : ℝ) (160740625172261 / 5000000000000000 : ℝ)
    (cell13186 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · have h := gap_lower (n := 13186) (a := (83686496511959 / 100000000000000 : ℝ)) (b := (78071278781 / 50000000000000 : ℝ)) (q := (54879422383 / 2500000000000 : ℝ))
      (E := (cell13186 ⟨11, by decide⟩).energy) (xi := (160740625172261 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13186 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13186]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13186])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13186) (a := (83686496511959 / 100000000000000 : ℝ)) (b := (78071278781 / 50000000000000 : ℝ)) (q := (54879422383 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13186])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13186])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13186]

theorem cert13186_12 : CellCertificate 13186 (87359367516197 / 1000000000000000 : ℝ) (1592914770591411 / 1000000000000000000 : ℝ) (160740625172261 / 5000000000000000 : ℝ)
    (cell13186 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · have h := gap_lower (n := 13186) (a := (83651879197149 / 100000000000000 : ℝ)) (b := (78071278781 / 50000000000000 : ℝ)) (q := (2195180894957 / 100000000000000 : ℝ))
      (E := (cell13186 ⟨12, by decide⟩).energy) (xi := (160740625172261 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13186 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13186]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13186])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13186) (a := (83651879197149 / 100000000000000 : ℝ)) (b := (78071278781 / 50000000000000 : ℝ)) (q := (2195180894957 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13186])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13186])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13186]

theorem cert13186_13 : CellCertificate 13186 (87359367516197 / 1000000000000000 : ℝ) (1592914770591411 / 1000000000000000000 : ℝ) (160740625172261 / 5000000000000000 : ℝ)
    (cell13186 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · have h := gap_lower (n := 13186) (a := (83617286306537 / 100000000000000 : ℝ)) (b := (78071278781 / 50000000000000 : ℝ)) (q := (439036984047 / 20000000000000 : ℝ))
      (E := (cell13186 ⟨13, by decide⟩).energy) (xi := (160740625172261 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13186 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13186]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13186])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13186) (a := (83617286306537 / 100000000000000 : ℝ)) (b := (78071278781 / 50000000000000 : ℝ)) (q := (439036984047 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13186])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13186])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13186]

theorem cert13186_14 : CellCertificate 13186 (87359367516197 / 1000000000000000 : ℝ) (1592914770591411 / 1000000000000000000 : ℝ) (160740625172261 / 5000000000000000 : ℝ)
    (cell13186 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · have h := gap_lower (n := 13186) (a := (83582717805919 / 100000000000000 : ℝ)) (b := (78071278781 / 50000000000000 : ℝ)) (q := (2195188918511 / 100000000000000 : ℝ))
      (E := (cell13186 ⟨14, by decide⟩).energy) (xi := (160740625172261 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13186 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13186]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13186])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13186) (a := (83582717805919 / 100000000000000 : ℝ)) (b := (78071278781 / 50000000000000 : ℝ)) (q := (2195188918511 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13186])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13186])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13186]

theorem cert13186_15 : CellCertificate 13186 (87359367516197 / 1000000000000000 : ℝ) (1592914770591411 / 1000000000000000000 : ℝ) (160740625172261 / 5000000000000000 : ℝ)
    (cell13186 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · have h := gap_lower (n := 13186) (a := (8354817366127 / 10000000000000 : ℝ)) (b := (78071278781 / 50000000000000 : ℝ)) (q := (2195192953223 / 100000000000000 : ℝ))
      (E := (cell13186 ⟨15, by decide⟩).energy) (xi := (160740625172261 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13186 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13186]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13186])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13186) (a := (8354817366127 / 10000000000000 : ℝ)) (b := (78071278781 / 50000000000000 : ℝ)) (q := (2195192953223 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13186])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13186])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13186]

theorem cert13186_16 : CellCertificate 13186 (87359367516197 / 1000000000000000 : ℝ) (1592914770591411 / 1000000000000000000 : ℝ) (160740625172261 / 5000000000000000 : ℝ)
    (cell13186 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · have h := gap_lower (n := 13186) (a := (83513653838739 / 100000000000000 : ℝ)) (b := (78071278781 / 50000000000000 : ℝ)) (q := (1097598485597 / 50000000000000 : ℝ))
      (E := (cell13186 ⟨16, by decide⟩).energy) (xi := (160740625172261 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13186 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13186]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13186])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13186) (a := (83513653838739 / 100000000000000 : ℝ)) (b := (78071278781 / 50000000000000 : ℝ)) (q := (1097598485597 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13186])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13186])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13186]

theorem cert13186_17 : CellCertificate 13186 (87359367516197 / 1000000000000000 : ℝ) (1592914770591411 / 1000000000000000000 : ℝ) (160740625172261 / 5000000000000000 : ℝ)
    (cell13186 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · have h := gap_lower (n := 13186) (a := (83479158304653 / 100000000000000 : ℝ)) (b := (78071278781 / 50000000000000 : ℝ)) (q := (1097600488583 / 50000000000000 : ℝ))
      (E := (cell13186 ⟨17, by decide⟩).energy) (xi := (160740625172261 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13186 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13186]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13186])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13186) (a := (83479158304653 / 100000000000000 : ℝ)) (b := (78071278781 / 50000000000000 : ℝ)) (q := (1097600488583 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13186])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13186])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13186]

theorem cert13186_18 : CellCertificate 13186 (87359367516197 / 1000000000000000 : ℝ) (1592914770591411 / 1000000000000000000 : ℝ) (160740625172261 / 5000000000000000 : ℝ)
    (cell13186 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · have h := gap_lower (n := 13186) (a := (83444687025511 / 100000000000000 : ℝ)) (b := (78071278781 / 50000000000000 : ℝ)) (q := (54880124391 / 2500000000000 : ℝ))
      (E := (cell13186 ⟨18, by decide⟩).energy) (xi := (160740625172261 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13186 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13186]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13186])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13186) (a := (83444687025511 / 100000000000000 : ℝ)) (b := (78071278781 / 50000000000000 : ℝ)) (q := (54880124391 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13186])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13186])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13186]

theorem cert13186_19 : CellCertificate 13186 (87359367516197 / 1000000000000000 : ℝ) (1592914770591411 / 1000000000000000000 : ℝ) (160740625172261 / 5000000000000000 : ℝ)
    (cell13186 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · have h := gap_lower (n := 13186) (a := (5213139997999 / 6250000000000 : ℝ)) (b := (78071278781 / 50000000000000 : ℝ)) (q := (1097604514591 / 50000000000000 : ℝ))
      (E := (cell13186 ⟨19, by decide⟩).energy) (xi := (160740625172261 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13186 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13186]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13186])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13186) (a := (5213139997999 / 6250000000000 : ℝ)) (b := (78071278781 / 50000000000000 : ℝ)) (q := (1097604514591 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13186])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13186])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13186]

theorem cert13187_0 : CellCertificate 13187 (34942707223153 / 400000000000000 : ℝ) (1592793938016203 / 1000000000000000000 : ℝ) (321456317631941 / 10000000000000000 : ℝ)
    (cell13187 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · have h := gap_lower (n := 13187) (a := (2101722372569 / 2500000000000 : ℝ)) (b := (78065291183 / 50000000000000 : ℝ)) (q := (137188903447 / 6250000000000 : ℝ))
      (E := (cell13187 ⟨0, by decide⟩).energy) (xi := (321456317631941 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13187 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13187]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13187])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13187) (a := (2101722372569 / 2500000000000 : ℝ)) (b := (78065291183 / 50000000000000 : ℝ)) (q := (137188903447 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13187])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13187])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13187]

theorem cert13187_1 : CellCertificate 13187 (34942707223153 / 400000000000000 : ℝ) (1592793938016203 / 1000000000000000000 : ℝ) (321456317631941 / 10000000000000000 : ℝ)
    (cell13187 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · have h := gap_lower (n := 13187) (a := (84034006618733 / 100000000000000 : ℝ)) (b := (78065291183 / 50000000000000 : ℝ)) (q := (2195026490359 / 100000000000000 : ℝ))
      (E := (cell13187 ⟨1, by decide⟩).energy) (xi := (321456317631941 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13187 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13187]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13187])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13187) (a := (84034006618733 / 100000000000000 : ℝ)) (b := (78065291183 / 50000000000000 : ℝ)) (q := (2195026490359 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13187])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13187])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13187]

theorem cert13187_2 : CellCertificate 13187 (34942707223153 / 400000000000000 : ℝ) (1592793938016203 / 1000000000000000000 : ℝ) (321456317631941 / 10000000000000000 : ℝ)
    (cell13187 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · have h := gap_lower (n := 13187) (a := (2624973223349 / 3125000000000 : ℝ)) (b := (78065291183 / 50000000000000 : ℝ)) (q := (2195030473751 / 100000000000000 : ℝ))
      (E := (cell13187 ⟨2, by decide⟩).energy) (xi := (321456317631941 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13187 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13187]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13187])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13187) (a := (2624973223349 / 3125000000000 : ℝ)) (b := (78065291183 / 50000000000000 : ℝ)) (q := (2195030473751 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13187])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13187])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13187]

theorem cert13187_3 : CellCertificate 13187 (34942707223153 / 400000000000000 : ℝ) (1592793938016203 / 1000000000000000000 : ℝ) (321456317631941 / 10000000000000000 : ℝ)
    (cell13187 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · have h := gap_lower (n := 13187) (a := (41982152225917 / 50000000000000 : ℝ)) (b := (78065291183 / 50000000000000 : ℝ)) (q := (137189658093 / 6250000000000 : ℝ))
      (E := (cell13187 ⟨3, by decide⟩).energy) (xi := (321456317631941 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13187 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13187]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13187])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13187) (a := (41982152225917 / 50000000000000 : ℝ)) (b := (78065291183 / 50000000000000 : ℝ)) (q := (137189658093 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13187])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13187])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13187]

theorem cert13187_4 : CellCertificate 13187 (34942707223153 / 400000000000000 : ℝ) (1592793938016203 / 1000000000000000000 : ℝ) (321456317631941 / 10000000000000000 : ℝ)
    (cell13187 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · have h := gap_lower (n := 13187) (a := (8392949049669 / 10000000000000 : ℝ)) (b := (78065291183 / 50000000000000 : ℝ)) (q := (439007709971 / 20000000000000 : ℝ))
      (E := (cell13187 ⟨4, by decide⟩).energy) (xi := (321456317631941 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13187 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13187]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13187])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13187) (a := (8392949049669 / 10000000000000 : ℝ)) (b := (78065291183 / 50000000000000 : ℝ)) (q := (439007709971 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13187])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13187])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13187]

theorem cert13187_5 : CellCertificate 13187 (34942707223153 / 400000000000000 : ℝ) (1592793938016203 / 1000000000000000000 : ℝ) (321456317631941 / 10000000000000000 : ℝ)
    (cell13187 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · have h := gap_lower (n := 13187) (a := (16778940249177 / 20000000000000 : ℝ)) (b := (78065291183 / 50000000000000 : ℝ)) (q := (1097521271321 / 50000000000000 : ℝ))
      (E := (cell13187 ⟨5, by decide⟩).energy) (xi := (321456317631941 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13187 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13187]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13187])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13187) (a := (16778940249177 / 20000000000000 : ℝ)) (b := (78065291183 / 50000000000000 : ℝ)) (q := (1097521271321 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13187])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13187])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13187]

theorem cert13187_6 : CellCertificate 13187 (34942707223153 / 400000000000000 : ℝ) (1592793938016203 / 1000000000000000000 : ℝ) (321456317631941 / 10000000000000000 : ℝ)
    (cell13187 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · have h := gap_lower (n := 13187) (a := (16771987332751 / 20000000000000 : ℝ)) (b := (78065291183 / 50000000000000 : ℝ)) (q := (1097523286693 / 50000000000000 : ℝ))
      (E := (cell13187 ⟨6, by decide⟩).energy) (xi := (321456317631941 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13187 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13187]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13187])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13187) (a := (16771987332751 / 20000000000000 : ℝ)) (b := (78065291183 / 50000000000000 : ℝ)) (q := (1097523286693 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13187])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13187])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13187]

theorem cert13187_7 : CellCertificate 13187 (34942707223153 / 400000000000000 : ℝ) (1592793938016203 / 1000000000000000000 : ℝ) (321456317631941 / 10000000000000000 : ℝ)
    (cell13187 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · have h := gap_lower (n := 13187) (a := (83825196714823 / 100000000000000 : ℝ)) (b := (78065291183 / 50000000000000 : ℝ)) (q := (1097525295709 / 50000000000000 : ℝ))
      (E := (cell13187 ⟨7, by decide⟩).energy) (xi := (321456317631941 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13187 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13187]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13187])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13187) (a := (83825196714823 / 100000000000000 : ℝ)) (b := (78065291183 / 50000000000000 : ℝ)) (q := (1097525295709 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13187])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13187])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13187]

theorem cert13187_8 : CellCertificate 13187 (34942707223153 / 400000000000000 : ℝ) (1592793938016203 / 1000000000000000000 : ℝ) (321456317631941 / 10000000000000000 : ℝ)
    (cell13187 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · have h := gap_lower (n := 13187) (a := (41895240681899 / 50000000000000 : ℝ)) (b := (78065291183 / 50000000000000 : ℝ)) (q := (2195054603769 / 100000000000000 : ℝ))
      (E := (cell13187 ⟨8, by decide⟩).energy) (xi := (321456317631941 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13187 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13187]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13187])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13187) (a := (41895240681899 / 50000000000000 : ℝ)) (b := (78065291183 / 50000000000000 : ℝ)) (q := (2195054603769 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13187])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13187])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13187]

theorem cert13187_9 : CellCertificate 13187 (34942707223153 / 400000000000000 : ℝ) (1592793938016203 / 1000000000000000000 : ℝ) (321456317631941 / 10000000000000000 : ℝ)
    (cell13187 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · have h := gap_lower (n := 13187) (a := (83755790575573 / 100000000000000 : ℝ)) (b := (78065291183 / 50000000000000 : ℝ)) (q := (1097529308611 / 50000000000000 : ℝ))
      (E := (cell13187 ⟨9, by decide⟩).energy) (xi := (321456317631941 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13187 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13187]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13187])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13187) (a := (83755790575573 / 100000000000000 : ℝ)) (b := (78065291183 / 50000000000000 : ℝ)) (q := (1097529308611 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13187])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13187])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13187]

theorem cert13187_10 : CellCertificate 13187 (34942707223153 / 400000000000000 : ℝ) (1592793938016203 / 1000000000000000000 : ℝ) (321456317631941 / 10000000000000000 : ℝ)
    (cell13187 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · have h := gap_lower (n := 13187) (a := (10465140539403 / 12500000000000 : ℝ)) (b := (78065291183 / 50000000000000 : ℝ)) (q := (439012527661 / 20000000000000 : ℝ))
      (E := (cell13187 ⟨10, by decide⟩).energy) (xi := (321456317631941 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13187 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13187]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13187])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13187) (a := (10465140539403 / 12500000000000 : ℝ)) (b := (78065291183 / 50000000000000 : ℝ)) (q := (439012527661 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13187])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13187])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13187]

theorem cert13187_11 : CellCertificate 13187 (34942707223153 / 400000000000000 : ℝ) (1592793938016203 / 1000000000000000000 : ℝ) (321456317631941 / 10000000000000000 : ℝ)
    (cell13187 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · have h := gap_lower (n := 13187) (a := (83686482548009 / 100000000000000 : ℝ)) (b := (78065291183 / 50000000000000 : ℝ)) (q := (2195066615187 / 100000000000000 : ℝ))
      (E := (cell13187 ⟨11, by decide⟩).energy) (xi := (321456317631941 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13187 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13187]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13187])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13187) (a := (83686482548009 / 100000000000000 : ℝ)) (b := (78065291183 / 50000000000000 : ℝ)) (q := (2195066615187 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13187])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13187])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13187]

theorem cert13187_12 : CellCertificate 13187 (34942707223153 / 400000000000000 : ℝ) (1592793938016203 / 1000000000000000000 : ℝ) (321456317631941 / 10000000000000000 : ℝ)
    (cell13187 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · have h := gap_lower (n := 13187) (a := (10456483154921 / 12500000000000 : ℝ)) (b := (78065291183 / 50000000000000 : ℝ)) (q := (1097535335053 / 50000000000000 : ℝ))
      (E := (cell13187 ⟨12, by decide⟩).energy) (xi := (321456317631941 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13187 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13187]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13187])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13187) (a := (10456483154921 / 12500000000000 : ℝ)) (b := (78065291183 / 50000000000000 : ℝ)) (q := (1097535335053 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13187])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13187])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13187]

theorem cert13187_13 : CellCertificate 13187 (34942707223153 / 400000000000000 : ℝ) (1592793938016203 / 1000000000000000000 : ℝ) (321456317631941 / 10000000000000000 : ℝ)
    (cell13187 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · have h := gap_lower (n := 13187) (a := (83617272354919 / 100000000000000 : ℝ)) (b := (78065291183 / 50000000000000 : ℝ)) (q := (1097537317219 / 50000000000000 : ℝ))
      (E := (cell13187 ⟨13, by decide⟩).energy) (xi := (321456317631941 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13187 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13187]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13187])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13187) (a := (83617272354919 / 100000000000000 : ℝ)) (b := (78065291183 / 50000000000000 : ℝ)) (q := (1097537317219 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13187])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13187])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13187]

theorem cert13187_14 : CellCertificate 13187 (34942707223153 / 400000000000000 : ℝ) (1592793938016203 / 1000000000000000000 : ℝ) (321456317631941 / 10000000000000000 : ℝ)
    (cell13187 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · have h := gap_lower (n := 13187) (a := (83582703860459 / 100000000000000 : ℝ)) (b := (78065291183 / 50000000000000 : ℝ)) (q := (1097539344069 / 50000000000000 : ℝ))
      (E := (cell13187 ⟨14, by decide⟩).energy) (xi := (321456317631941 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13187 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13187]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13187])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13187) (a := (83582703860459 / 100000000000000 : ℝ)) (b := (78065291183 / 50000000000000 : ℝ)) (q := (1097539344069 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13187])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13187])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13187]

theorem cert13187_15 : CellCertificate 13187 (34942707223153 / 400000000000000 : ℝ) (1592793938016203 / 1000000000000000000 : ℝ) (321456317631941 / 10000000000000000 : ℝ)
    (cell13187 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · have h := gap_lower (n := 13187) (a := (41774079860981 / 50000000000000 : ℝ)) (b := (78065291183 / 50000000000000 : ℝ)) (q := (2195082720159 / 100000000000000 : ℝ))
      (E := (cell13187 ⟨15, by decide⟩).energy) (xi := (321456317631941 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13187 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13187]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13187])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13187) (a := (41774079860981 / 50000000000000 : ℝ)) (b := (78065291183 / 50000000000000 : ℝ)) (q := (2195082720159 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13187])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13187])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13187]

theorem cert13187_16 : CellCertificate 13187 (34942707223153 / 400000000000000 : ℝ) (1592793938016203 / 1000000000000000000 : ℝ) (321456317631941 / 10000000000000000 : ℝ)
    (cell13187 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · have h := gap_lower (n := 13187) (a := (41756819952789 / 50000000000000 : ℝ)) (b := (78065291183 / 50000000000000 : ℝ)) (q := (439017347097 / 20000000000000 : ℝ))
      (E := (cell13187 ⟨16, by decide⟩).energy) (xi := (321456317631941 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13187 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13187]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13187])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13187) (a := (41756819952789 / 50000000000000 : ℝ)) (b := (78065291183 / 50000000000000 : ℝ)) (q := (439017347097 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13187])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13187])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13187]

theorem cert13187_17 : CellCertificate 13187 (34942707223153 / 400000000000000 : ℝ) (1592793938016203 / 1000000000000000000 : ℝ) (321456317631941 / 10000000000000000 : ℝ)
    (cell13187 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · have h := gap_lower (n := 13187) (a := (83479144377633 / 100000000000000 : ℝ)) (b := (78065291183 / 50000000000000 : ℝ)) (q := (109754536943 / 5000000000000 : ℝ))
      (E := (cell13187 ⟨17, by decide⟩).energy) (xi := (321456317631941 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13187 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13187]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13187])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13187) (a := (83479144377633 / 100000000000000 : ℝ)) (b := (78065291183 / 50000000000000 : ℝ)) (q := (109754536943 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13187])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13187])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13187]

theorem cert13187_18 : CellCertificate 13187 (34942707223153 / 400000000000000 : ℝ) (1592793938016203 / 1000000000000000000 : ℝ) (321456317631941 / 10000000000000000 : ℝ)
    (cell13187 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · have h := gap_lower (n := 13187) (a := (83444673104627 / 100000000000000 : ℝ)) (b := (78065291183 / 50000000000000 : ℝ)) (q := (34298355231 / 1562500000000 : ℝ))
      (E := (cell13187 ⟨18, by decide⟩).energy) (xi := (321456317631941 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13187 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13187]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13187])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13187) (a := (83444673104627 / 100000000000000 : ℝ)) (b := (78065291183 / 50000000000000 : ℝ)) (q := (34298355231 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13187])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13187])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13187]

theorem cert13187_19 : CellCertificate 13187 (34942707223153 / 400000000000000 : ℝ) (1592793938016203 / 1000000000000000000 : ℝ) (321456317631941 / 10000000000000000 : ℝ)
    (cell13187 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · have h := gap_lower (n := 13187) (a := (5213139128327 / 6250000000000 : ℝ)) (b := (78065291183 / 50000000000000 : ℝ)) (q := (2195098727519 / 100000000000000 : ℝ))
      (E := (cell13187 ⟨19, by decide⟩).energy) (xi := (321456317631941 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13187 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13187]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13187])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13187) (a := (5213139128327 / 6250000000000 : ℝ)) (b := (78065291183 / 50000000000000 : ℝ)) (q := (2195098727519 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13187])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13187])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13187]

theorem cert13188_0 : CellCertificate 13188 (873541689766817 / 10000000000000000 : ℝ) (79633656188571 / 50000000000000000 : ℝ) (321431388810423 / 10000000000000000 : ℝ)
    (cell13188 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · have h := gap_lower (n := 13188) (a := (3362755234909 / 4000000000000 : ℝ)) (b := (39029652253 / 25000000000000 : ℝ)) (q := (2194912205327 / 100000000000000 : ℝ))
      (E := (cell13188 ⟨0, by decide⟩).energy) (xi := (321431388810423 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13188 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13188]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13188])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13188) (a := (3362755234909 / 4000000000000 : ℝ)) (b := (39029652253 / 25000000000000 : ℝ)) (q := (2194912205327 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13188])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13188])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13188]

theorem cert13188_1 : CellCertificate 13188 (873541689766817 / 10000000000000000 : ℝ) (79633656188571 / 50000000000000000 : ℝ) (321431388810423 / 10000000000000000 : ℝ)
    (cell13188 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · have h := gap_lower (n := 13188) (a := (42016996297463 / 50000000000000 : ℝ)) (b := (39029652253 / 25000000000000 : ℝ)) (q := (548729059291 / 25000000000000 : ℝ))
      (E := (cell13188 ⟨1, by decide⟩).energy) (xi := (321431388810423 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13188 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13188]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13188])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13188) (a := (42016996297463 / 50000000000000 : ℝ)) (b := (39029652253 / 25000000000000 : ℝ)) (q := (548729059291 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13188])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13188])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13188]

theorem cert13188_2 : CellCertificate 13188 (873541689766817 / 10000000000000000 : ℝ) (79633656188571 / 50000000000000000 : ℝ) (321431388810423 / 10000000000000000 : ℝ)
    (cell13188 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · have h := gap_lower (n := 13188) (a := (5249945570599 / 6250000000000 : ℝ)) (b := (39029652253 / 25000000000000 : ℝ)) (q := (2194920275137 / 100000000000000 : ℝ))
      (E := (cell13188 ⟨2, by decide⟩).energy) (xi := (321431388810423 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13188 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13188]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13188])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13188) (a := (5249945570599 / 6250000000000 : ℝ)) (b := (39029652253 / 25000000000000 : ℝ)) (q := (2194920275137 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13188])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13188])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13188]

theorem cert13188_3 : CellCertificate 13188 (873541689766817 / 10000000000000000 : ℝ) (79633656188571 / 50000000000000000 : ℝ) (321431388810423 / 10000000000000000 : ℝ)
    (cell13188 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · have h := gap_lower (n := 13188) (a := (20991072610117 / 25000000000000 : ℝ)) (b := (39029652253 / 25000000000000 : ℝ)) (q := (2194924269693 / 100000000000000 : ℝ))
      (E := (cell13188 ⟨3, by decide⟩).energy) (xi := (321431388810423 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13188 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13188]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13188])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13188) (a := (20991072610117 / 25000000000000 : ℝ)) (b := (39029652253 / 25000000000000 : ℝ)) (q := (2194924269693 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13188])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13188])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13188]

theorem cert13188_4 : CellCertificate 13188 (873541689766817 / 10000000000000000 : ℝ) (79633656188571 / 50000000000000000 : ℝ) (321431388810423 / 10000000000000000 : ℝ)
    (cell13188 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · have h := gap_lower (n := 13188) (a := (16785895298307 / 20000000000000 : ℝ)) (b := (39029652253 / 25000000000000 : ℝ)) (q := (2194928286831 / 100000000000000 : ℝ))
      (E := (cell13188 ⟨4, by decide⟩).energy) (xi := (321431388810423 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13188 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13188]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13188])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13188) (a := (16785895298307 / 20000000000000 : ℝ)) (b := (39029652253 / 25000000000000 : ℝ)) (q := (2194928286831 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13188])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13188])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13188]

theorem cert13188_5 : CellCertificate 13188 (873541689766817 / 10000000000000000 : ℝ) (79633656188571 / 50000000000000000 : ℝ) (321431388810423 / 10000000000000000 : ℝ)
    (cell13188 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · have h := gap_lower (n := 13188) (a := (10486835905867 / 12500000000000 : ℝ)) (b := (39029652253 / 25000000000000 : ℝ)) (q := (2194932276437 / 100000000000000 : ℝ))
      (E := (cell13188 ⟨5, by decide⟩).energy) (xi := (321431388810423 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13188 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13188]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13188])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13188) (a := (10486835905867 / 12500000000000 : ℝ)) (b := (39029652253 / 25000000000000 : ℝ)) (q := (2194932276437 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13188])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13188])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13188]

theorem cert13188_6 : CellCertificate 13188 (873541689766817 / 10000000000000000 : ℝ) (79633656188571 / 50000000000000000 : ℝ) (321431388810423 / 10000000000000000 : ℝ)
    (cell13188 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · have h := gap_lower (n := 13188) (a := (41929961335503 / 50000000000000 : ℝ)) (b := (39029652253 / 25000000000000 : ℝ)) (q := (1097468152023 / 50000000000000 : ℝ))
      (E := (cell13188 ⟨6, by decide⟩).energy) (xi := (321431388810423 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13188 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13188]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13188])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13188) (a := (41929961335503 / 50000000000000 : ℝ)) (b := (39029652253 / 25000000000000 : ℝ)) (q := (1097468152023 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13188])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13188])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13188]

theorem cert13188_7 : CellCertificate 13188 (873541689766817 / 10000000000000000 : ℝ) (79633656188571 / 50000000000000000 : ℝ) (321431388810423 / 10000000000000000 : ℝ)
    (cell13188 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · have h := gap_lower (n := 13188) (a := (83825182728269 / 100000000000000 : ℝ)) (b := (39029652253 / 25000000000000 : ℝ)) (q := (2194940318989 / 100000000000000 : ℝ))
      (E := (cell13188 ⟨7, by decide⟩).energy) (xi := (321431388810423 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13188 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13188]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13188])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13188) (a := (83825182728269 / 100000000000000 : ℝ)) (b := (39029652253 / 25000000000000 : ℝ)) (q := (2194940318989 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13188])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13188])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13188]

theorem cert13188_8 : CellCertificate 13188 (873541689766817 / 10000000000000000 : ℝ) (79633656188571 / 50000000000000000 : ℝ) (321431388810423 / 10000000000000000 : ℝ)
    (cell13188 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · have h := gap_lower (n := 13188) (a := (83790467383433 / 100000000000000 : ℝ)) (b := (39029652253 / 25000000000000 : ℝ)) (q := (21949443283 / 1000000000000 : ℝ))
      (E := (cell13188 ⟨8, by decide⟩).energy) (xi := (321431388810423 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13188 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13188]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13188])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13188) (a := (83790467383433 / 100000000000000 : ℝ)) (b := (39029652253 / 25000000000000 : ℝ)) (q := (21949443283 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13188])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13188])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13188]

theorem cert13188_9 : CellCertificate 13188 (873541689766817 / 10000000000000000 : ℝ) (79633656188571 / 50000000000000000 : ℝ) (321431388810423 / 10000000000000000 : ℝ)
    (cell13188 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · have h := gap_lower (n := 13188) (a := (5234736037587 / 6250000000000 : ℝ)) (b := (39029652253 / 25000000000000 : ℝ)) (q := (1097474169379 / 50000000000000 : ℝ))
      (E := (cell13188 ⟨9, by decide⟩).energy) (xi := (321431388810423 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13188 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13188]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13188])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13188) (a := (5234736037587 / 6250000000000 : ℝ)) (b := (39029652253 / 25000000000000 : ℝ)) (q := (1097474169379 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13188])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13188])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13188]

theorem cert13188_10 : CellCertificate 13188 (873541689766817 / 10000000000000000 : ℝ) (79633656188571 / 50000000000000000 : ℝ) (321431388810423 / 10000000000000000 : ℝ)
    (cell13188 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · have h := gap_lower (n := 13188) (a := (41860555173611 / 50000000000000 : ℝ)) (b := (39029652253 / 25000000000000 : ℝ)) (q := (1097476178447 / 50000000000000 : ℝ))
      (E := (cell13188 ⟨10, by decide⟩).energy) (xi := (321431388810423 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13188 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13188]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13188])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13188) (a := (41860555173611 / 50000000000000 : ℝ)) (b := (39029652253 / 25000000000000 : ℝ)) (q := (1097476178447 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13188])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13188])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13188]

theorem cert13188_11 : CellCertificate 13188 (873541689766817 / 10000000000000000 : ℝ) (79633656188571 / 50000000000000000 : ℝ) (321431388810423 / 10000000000000000 : ℝ)
    (cell13188 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · have h := gap_lower (n := 13188) (a := (4184323429309 / 5000000000000 : ℝ)) (b := (39029652253 / 25000000000000 : ℝ)) (q := (2194956388989 / 100000000000000 : ℝ))
      (E := (cell13188 ⟨11, by decide⟩).energy) (xi := (321431388810423 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13188 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13188]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13188])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13188) (a := (4184323429309 / 5000000000000 : ℝ)) (b := (39029652253 / 25000000000000 : ℝ)) (q := (2194956388989 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13188])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13188])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13188]

theorem cert13188_12 : CellCertificate 13188 (873541689766817 / 10000000000000000 : ℝ) (79633656188571 / 50000000000000000 : ℝ) (321431388810423 / 10000000000000000 : ℝ)
    (cell13188 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · have h := gap_lower (n := 13188) (a := (83651851283707 / 100000000000000 : ℝ)) (b := (39029652253 / 25000000000000 : ℝ)) (q := (109748019147 / 5000000000000 : ℝ))
      (E := (cell13188 ⟨12, by decide⟩).energy) (xi := (321431388810423 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13188 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13188]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13188])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13188) (a := (83651851283707 / 100000000000000 : ℝ)) (b := (39029652253 / 25000000000000 : ℝ)) (q := (109748019147 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13188])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13188])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13188]

theorem cert13188_13 : CellCertificate 13188 (873541689766817 / 10000000000000000 : ℝ) (79633656188571 / 50000000000000000 : ℝ) (321431388810423 / 10000000000000000 : ℝ)
    (cell13188 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · have h := gap_lower (n := 13188) (a := (4180862920271 / 5000000000000 : ℝ)) (b := (39029652253 / 25000000000000 : ℝ)) (q := (1097482201313 / 50000000000000 : ℝ))
      (E := (cell13188 ⟨13, by decide⟩).energy) (xi := (321431388810423 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13188 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13188]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13188])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13188) (a := (4180862920271 / 5000000000000 : ℝ)) (b := (39029652253 / 25000000000000 : ℝ)) (q := (1097482201313 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13188])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13188])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13188]

theorem cert13188_14 : CellCertificate 13188 (873541689766817 / 10000000000000000 : ℝ) (79633656188571 / 50000000000000000 : ℝ) (321431388810423 / 10000000000000000 : ℝ)
    (cell13188 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · have h := gap_lower (n := 13188) (a := (20895672479279 / 25000000000000 : ℝ)) (b := (39029652253 / 25000000000000 : ℝ)) (q := (219496845359 / 10000000000000 : ℝ))
      (E := (cell13188 ⟨14, by decide⟩).energy) (xi := (321431388810423 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13188 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13188]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13188])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13188) (a := (20895672479279 / 25000000000000 : ℝ)) (b := (39029652253 / 25000000000000 : ℝ)) (q := (219496845359 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13188])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13188])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13188]

theorem cert13188_15 : CellCertificate 13188 (873541689766817 / 10000000000000000 : ℝ) (79633656188571 / 50000000000000000 : ℝ) (321431388810423 / 10000000000000000 : ℝ)
    (cell13188 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · have h := gap_lower (n := 13188) (a := (8354814578477 / 10000000000000 : ℝ)) (b := (39029652253 / 25000000000000 : ℝ)) (q := (2194972424713 / 100000000000000 : ℝ))
      (E := (cell13188 ⟨15, by decide⟩).energy) (xi := (321431388810423 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13188 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13188]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13188])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13188) (a := (8354814578477 / 10000000000000 : ℝ)) (b := (39029652253 / 25000000000000 : ℝ)) (q := (2194972424713 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13188])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13188])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13188]

theorem cert13188_16 : CellCertificate 13188 (873541689766817 / 10000000000000000 : ℝ) (79633656188571 / 50000000000000000 : ℝ) (321431388810423 / 10000000000000000 : ℝ)
    (cell13188 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · have h := gap_lower (n := 13188) (a := (83513625974533 / 100000000000000 : ℝ)) (b := (39029652253 / 25000000000000 : ℝ)) (q := (548744109343 / 25000000000000 : ℝ))
      (E := (cell13188 ⟨16, by decide⟩).energy) (xi := (321431388810423 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13188 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13188]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13188])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13188) (a := (83513625974533 / 100000000000000 : ℝ)) (b := (39029652253 / 25000000000000 : ℝ)) (q := (548744109343 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13188])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13188])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13188]

theorem cert13188_17 : CellCertificate 13188 (873541689766817 / 10000000000000000 : ℝ) (79633656188571 / 50000000000000000 : ℝ) (321431388810423 / 10000000000000000 : ℝ)
    (cell13188 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · have h := gap_lower (n := 13188) (a := (83479130452729 / 100000000000000 : ℝ)) (b := (39029652253 / 25000000000000 : ℝ)) (q := (2194980496381 / 100000000000000 : ℝ))
      (E := (cell13188 ⟨17, by decide⟩).energy) (xi := (321431388810423 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13188 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13188]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13188])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13188) (a := (83479130452729 / 100000000000000 : ℝ)) (b := (39029652253 / 25000000000000 : ℝ)) (q := (2194980496381 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13188])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13188])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13188]

theorem cert13188_18 : CellCertificate 13188 (873541689766817 / 10000000000000000 : ℝ) (79633656188571 / 50000000000000000 : ℝ) (321431388810423 / 10000000000000000 : ℝ)
    (cell13188 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · have h := gap_lower (n := 13188) (a := (41722329592929 / 50000000000000 : ℝ)) (b := (39029652253 / 25000000000000 : ℝ)) (q := (438996897951 / 20000000000000 : ℝ))
      (E := (cell13188 ⟨18, by decide⟩).energy) (xi := (321431388810423 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13188 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13188]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13188])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13188) (a := (41722329592929 / 50000000000000 : ℝ)) (b := (39029652253 / 25000000000000 : ℝ)) (q := (438996897951 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13188])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13188])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13188]

theorem cert13188_19 : CellCertificate 13188 (873541689766817 / 10000000000000000 : ℝ) (79633656188571 / 50000000000000000 : ℝ) (321431388810423 / 10000000000000000 : ℝ)
    (cell13188 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · have h := gap_lower (n := 13188) (a := (5213138258787 / 6250000000000 : ℝ)) (b := (39029652253 / 25000000000000 : ℝ)) (q := (2194988538289 / 100000000000000 : ℝ))
      (E := (cell13188 ⟨19, by decide⟩).energy) (xi := (321431388810423 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13188 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13188]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13188])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13188) (a := (5213138258787 / 6250000000000 : ℝ)) (b := (39029652253 / 25000000000000 : ℝ)) (q := (2194988538289 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13188])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13188])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13188]

theorem cert13189_0 : CellCertificate 13189 (873515702725087 / 10000000000000000 : ℝ) (1592552327852891 / 1000000000000000000 : ℝ) (80351615969753 / 2500000000000000 : ℝ)
    (cell13189 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · have h := gap_lower (n := 13189) (a := (84068866844819 / 100000000000000 : ℝ)) (b := (12488531 / 8000000000 : ℝ)) (q := (2194802009173 / 100000000000000 : ℝ))
      (E := (cell13189 ⟨0, by decide⟩).energy) (xi := (80351615969753 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13189 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13189]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13189])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13189) (a := (84068866844819 / 100000000000000 : ℝ)) (b := (12488531 / 8000000000 : ℝ)) (q := (2194802009173 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13189])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13189])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13189]

theorem cert13189_1 : CellCertificate 13189 (873515702725087 / 10000000000000000 : ℝ) (1592552327852891 / 1000000000000000000 : ℝ) (80351615969753 / 2500000000000000 : ℝ)
    (cell13189 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · have h := gap_lower (n := 13189) (a := (84033978573249 / 100000000000000 : ℝ)) (b := (12488531 / 8000000000 : ℝ)) (q := (2194806037663 / 100000000000000 : ℝ))
      (E := (cell13189 ⟨1, by decide⟩).energy) (xi := (80351615969753 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13189 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13189]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13189])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13189) (a := (84033978573249 / 100000000000000 : ℝ)) (b := (12488531 / 8000000000 : ℝ)) (q := (2194806037663 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13189])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13189])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13189]

theorem cert13189_2 : CellCertificate 13189 (873515702725087 / 10000000000000000 : ℝ) (1592552327852891 / 1000000000000000000 : ℝ) (80351615969753 / 2500000000000000 : ℝ)
    (cell13189 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · have h := gap_lower (n := 13189) (a := (5249944694633 / 6250000000000 : ℝ)) (b := (12488531 / 8000000000 : ℝ)) (q := (1097405007217 / 50000000000000 : ℝ))
      (E := (cell13189 ⟨2, by decide⟩).energy) (xi := (80351615969753 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13189 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13189]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13189])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13189) (a := (5249944694633 / 6250000000000 : ℝ)) (b := (12488531 / 8000000000 : ℝ)) (q := (1097405007217 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13189])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13189])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13189]

theorem cert13189_3 : CellCertificate 13189 (873515702725087 / 10000000000000000 : ℝ) (1592552327852891 / 1000000000000000000 : ℝ) (80351615969753 / 2500000000000000 : ℝ)
    (cell13189 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · have h := gap_lower (n := 13189) (a := (20991069107807 / 25000000000000 : ℝ)) (b := (12488531 / 8000000000 : ℝ)) (q := (1097407031821 / 50000000000000 : ℝ))
      (E := (cell13189 ⟨3, by decide⟩).energy) (xi := (80351615969753 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13189 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13189]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13189])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13189) (a := (20991069107807 / 25000000000000 : ℝ)) (b := (12488531 / 8000000000 : ℝ)) (q := (1097407031821 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13189])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13189])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13189]

theorem cert13189_4 : CellCertificate 13189 (873515702725087 / 10000000000000000 : ℝ) (1592552327852891 / 1000000000000000000 : ℝ) (80351615969753 / 2500000000000000 : ℝ)
    (cell13189 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · have h := gap_lower (n := 13189) (a := (41964731244253 / 50000000000000 : ℝ)) (b := (12488531 / 8000000000 : ℝ)) (q := (87792723103 / 4000000000000 : ℝ))
      (E := (cell13189 ⟨4, by decide⟩).energy) (xi := (80351615969753 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13189 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13189]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13189])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13189) (a := (41964731244253 / 50000000000000 : ℝ)) (b := (12488531 / 8000000000 : ℝ)) (q := (87792723103 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13189])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13189])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13189]

theorem cert13189_5 : CellCertificate 13189 (873515702725087 / 10000000000000000 : ℝ) (1592552327852891 / 1000000000000000000 : ℝ) (80351615969753 / 2500000000000000 : ℝ)
    (cell13189 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · have h := gap_lower (n := 13189) (a := (1310854269533 / 1562500000000 : ℝ)) (b := (12488531 / 8000000000 : ℝ)) (q := (2194822064023 / 100000000000000 : ℝ))
      (E := (cell13189 ⟨5, by decide⟩).energy) (xi := (80351615969753 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13189 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13189]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13189])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13189) (a := (1310854269533 / 1562500000000 : ℝ)) (b := (12488531 / 8000000000 : ℝ)) (q := (2194822064023 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13189])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13189])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13189]

theorem cert13189_6 : CellCertificate 13189 (873515702725087 / 10000000000000000 : ℝ) (1592552327852891 / 1000000000000000000 : ℝ) (80351615969753 / 2500000000000000 : ℝ)
    (cell13189 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · have h := gap_lower (n := 13189) (a := (41929954340191 / 50000000000000 : ℝ)) (b := (12488531 / 8000000000 : ℝ)) (q := (2194826088521 / 100000000000000 : ℝ))
      (E := (cell13189 ⟨6, by decide⟩).energy) (xi := (80351615969753 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13189 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13189]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13189])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13189) (a := (41929954340191 / 50000000000000 : ℝ)) (b := (12488531 / 8000000000 : ℝ)) (q := (2194826088521 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13189])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13189])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13189]

theorem cert13189_7 : CellCertificate 13189 (873515702725087 / 10000000000000000 : ℝ) (1592552327852891 / 1000000000000000000 : ℝ) (80351615969753 / 2500000000000000 : ℝ)
    (cell13189 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · have h := gap_lower (n := 13189) (a := (83825168743839 / 100000000000000 : ℝ)) (b := (12488531 / 8000000000 : ℝ)) (q := (2194830100401 / 100000000000000 : ℝ))
      (E := (cell13189 ⟨7, by decide⟩).energy) (xi := (80351615969753 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13189 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13189]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13189])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13189) (a := (83825168743839 / 100000000000000 : ℝ)) (b := (12488531 / 8000000000 : ℝ)) (q := (2194830100401 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13189])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13189])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13189]

theorem cert13189_8 : CellCertificate 13189 (873515702725087 / 10000000000000000 : ℝ) (1592552327852891 / 1000000000000000000 : ℝ) (80351615969753 / 2500000000000000 : ℝ)
    (cell13189 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · have h := gap_lower (n := 13189) (a := (83790453405191 / 100000000000000 : ℝ)) (b := (12488531 / 8000000000 : ℝ)) (q := (438966821339 / 20000000000000 : ℝ))
      (E := (cell13189 ⟨8, by decide⟩).energy) (xi := (80351615969753 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13189 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13189]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13189])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13189) (a := (83790453405191 / 100000000000000 : ℝ)) (b := (12488531 / 8000000000 : ℝ)) (q := (438966821339 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13189])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13189])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13189]

theorem cert13189_9 : CellCertificate 13189 (873515702725087 / 10000000000000000 : ℝ) (1592552327852891 / 1000000000000000000 : ℝ) (80351615969753 / 2500000000000000 : ℝ)
    (cell13189 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · have h := gap_lower (n := 13189) (a := (83755762629333 / 100000000000000 : ℝ)) (b := (12488531 / 8000000000 : ℝ)) (q := (2194838114183 / 100000000000000 : ℝ))
      (E := (cell13189 ⟨9, by decide⟩).energy) (xi := (80351615969753 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13189 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13189]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13189])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13189) (a := (83755762629333 / 100000000000000 : ℝ)) (b := (12488531 / 8000000000 : ℝ)) (q := (2194838114183 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13189])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13189])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13189]

theorem cert13189_10 : CellCertificate 13189 (873515702725087 / 10000000000000000 : ℝ) (1592552327852891 / 1000000000000000000 : ℝ) (80351615969753 / 2500000000000000 : ℝ)
    (cell13189 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · have h := gap_lower (n := 13189) (a := (4186054819067 / 5000000000000 : ℝ)) (b := (12488531 / 8000000000 : ℝ)) (q := (548710532349 / 25000000000000 : ℝ))
      (E := (cell13189 ⟨10, by decide⟩).energy) (xi := (80351615969753 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13189 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13189]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13189])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13189) (a := (4186054819067 / 5000000000000 : ℝ)) (b := (12488531 / 8000000000 : ℝ)) (q := (548710532349 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13189])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13189])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13189]

theorem cert13189_11 : CellCertificate 13189 (873515702725087 / 10000000000000000 : ℝ) (1592552327852891 / 1000000000000000000 : ℝ) (80351615969753 / 2500000000000000 : ℝ)
    (cell13189 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · have h := gap_lower (n := 13189) (a := (83686454626471 / 100000000000000 : ℝ)) (b := (12488531 / 8000000000 : ℝ)) (q := (1097423079307 / 50000000000000 : ℝ))
      (E := (cell13189 ⟨11, by decide⟩).energy) (xi := (80351615969753 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13189 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13189]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13189])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13189) (a := (83686454626471 / 100000000000000 : ℝ)) (b := (12488531 / 8000000000 : ℝ)) (q := (1097423079307 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13189])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13189])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13189]

theorem cert13189_12 : CellCertificate 13189 (873515702725087 / 10000000000000000 : ℝ) (1592552327852891 / 1000000000000000000 : ℝ) (80351615969753 / 2500000000000000 : ℝ)
    (cell13189 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · have h := gap_lower (n := 13189) (a := (20912959332541 / 25000000000000 : ℝ)) (b := (12488531 / 8000000000 : ℝ)) (q := (1097425103937 / 50000000000000 : ℝ))
      (E := (cell13189 ⟨12, by decide⟩).energy) (xi := (80351615969753 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13189 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13189]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13189])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13189) (a := (20912959332541 / 25000000000000 : ℝ)) (b := (12488531 / 8000000000 : ℝ)) (q := (1097425103937 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13189])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13189])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13189]

theorem cert13189_13 : CellCertificate 13189 (873515702725087 / 10000000000000000 : ℝ) (1592552327852891 / 1000000000000000000 : ℝ) (80351615969753 / 2500000000000000 : ℝ)
    (cell13189 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · have h := gap_lower (n := 13189) (a := (41808622229019 / 50000000000000 : ℝ)) (b := (12488531 / 8000000000 : ℝ)) (q := (2194854224801 / 100000000000000 : ℝ))
      (E := (cell13189 ⟨13, by decide⟩).energy) (xi := (80351615969753 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13189 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13189]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13189])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13189) (a := (41808622229019 / 50000000000000 : ℝ)) (b := (12488531 / 8000000000 : ℝ)) (q := (2194854224801 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13189])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13189])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13189]

theorem cert13189_14 : CellCertificate 13189 (873515702725087 / 10000000000000000 : ℝ) (1592552327852891 / 1000000000000000000 : ℝ) (80351615969753 / 2500000000000000 : ℝ)
    (cell13189 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · have h := gap_lower (n := 13189) (a := (83582675975891 / 100000000000000 : ℝ)) (b := (12488531 / 8000000000 : ℝ)) (q := (1097429107433 / 50000000000000 : ℝ))
      (E := (cell13189 ⟨14, by decide⟩).energy) (xi := (80351615969753 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13189 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13189]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13189])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13189) (a := (83582675975891 / 100000000000000 : ℝ)) (b := (12488531 / 8000000000 : ℝ)) (q := (1097429107433 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13189])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13189])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13189]

theorem cert13189_15 : CellCertificate 13189 (873515702725087 / 10000000000000000 : ℝ) (1592552327852891 / 1000000000000000000 : ℝ) (80351615969753 / 2500000000000000 : ℝ)
    (cell13189 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · have h := gap_lower (n := 13189) (a := (16709626369939 / 20000000000000 : ℝ)) (b := (12488531 / 8000000000 : ℝ)) (q := (548715560377 / 25000000000000 : ℝ))
      (E := (cell13189 ⟨15, by decide⟩).energy) (xi := (80351615969753 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13189 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13189]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13189])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13189) (a := (16709626369939 / 20000000000000 : ℝ)) (b := (12488531 / 8000000000 : ℝ)) (q := (548715560377 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13189])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13189])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13189]

theorem cert13189_16 : CellCertificate 13189 (873515702725087 / 10000000000000000 : ℝ) (1592552327852891 / 1000000000000000000 : ℝ) (80351615969753 / 2500000000000000 : ℝ)
    (cell13189 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · have h := gap_lower (n := 13189) (a := (41756806022801 / 50000000000000 : ℝ)) (b := (12488531 / 8000000000 : ℝ)) (q := (2194866251549 / 100000000000000 : ℝ))
      (E := (cell13189 ⟨16, by decide⟩).energy) (xi := (80351615969753 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13189 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13189]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13189])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13189) (a := (41756806022801 / 50000000000000 : ℝ)) (b := (12488531 / 8000000000 : ℝ)) (q := (2194866251549 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13189])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13189])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13189]

theorem cert13189_17 : CellCertificate 13189 (873515702725087 / 10000000000000000 : ℝ) (1592552327852891 / 1000000000000000000 : ℝ) (80351615969753 / 2500000000000000 : ℝ)
    (cell13189 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · have h := gap_lower (n := 13189) (a := (41739558264969 / 50000000000000 : ℝ)) (b := (12488531 / 8000000000 : ℝ)) (q := (2194870249731 / 100000000000000 : ℝ))
      (E := (cell13189 ⟨17, by decide⟩).energy) (xi := (80351615969753 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13189 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13189]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13189])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13189) (a := (41739558264969 / 50000000000000 : ℝ)) (b := (12488531 / 8000000000 : ℝ)) (q := (2194870249731 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13189])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13189])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13189]

theorem cert13189_18 : CellCertificate 13189 (873515702725087 / 10000000000000000 : ℝ) (1592552327852891 / 1000000000000000000 : ℝ) (80351615969753 / 2500000000000000 : ℝ)
    (cell13189 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · have h := gap_lower (n := 13189) (a := (83444645269201 / 100000000000000 : ℝ)) (b := (12488531 / 8000000000 : ℝ)) (q := (1097437149417 / 50000000000000 : ℝ))
      (E := (cell13189 ⟨18, by decide⟩).energy) (xi := (80351615969753 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13189 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13189]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13189])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13189) (a := (83444645269201 / 100000000000000 : ℝ)) (b := (12488531 / 8000000000 : ℝ)) (q := (1097437149417 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13189])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13189])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13189]

theorem cert13189_19 : CellCertificate 13189 (873515702725087 / 10000000000000000 : ℝ) (1592552327852891 / 1000000000000000000 : ℝ) (80351615969753 / 2500000000000000 : ℝ)
    (cell13189 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · have h := gap_lower (n := 13189) (a := (16682039646013 / 20000000000000 : ℝ)) (b := (12488531 / 8000000000 : ℝ)) (q := (1097439143293 / 50000000000000 : ℝ))
      (E := (cell13189 ⟨19, by decide⟩).energy) (xi := (80351615969753 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13189 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13189]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13189])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13189) (a := (16682039646013 / 20000000000000 : ℝ)) (b := (12488531 / 8000000000 : ℝ)) (q := (1097439143293 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13189])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13189])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13189]

theorem cert13190_0 : CellCertificate 13190 (218372429863193 / 2500000000000000 : ℝ) (24881742972757 / 15625000000000000 : ℝ) (1285526171347 / 40000000000000 : ℝ)
    (cell13190 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · have h := gap_lower (n := 13190) (a := (21017213204761 / 25000000000000 : ℝ)) (b := (156094667831 / 100000000000000 : ℝ)) (q := (2194691808831 / 100000000000000 : ℝ))
      (E := (cell13190 ⟨0, by decide⟩).energy) (xi := (1285526171347 / 40000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13190 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13190]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13190])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13190) (a := (21017213204761 / 25000000000000 : ℝ)) (b := (156094667831 / 100000000000000 : ℝ)) (q := (2194691808831 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13190])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13190])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13190]

theorem cert13190_1 : CellCertificate 13190 (218372429863193 / 2500000000000000 : ℝ) (24881742972757 / 15625000000000000 : ℝ) (1285526171347 / 40000000000000 : ℝ)
    (cell13190 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · have h := gap_lower (n := 13190) (a := (840339645537 / 1000000000000 : ℝ)) (b := (156094667831 / 100000000000000 : ℝ)) (q := (274336979247 / 12500000000000 : ℝ))
      (E := (cell13190 ⟨1, by decide⟩).energy) (xi := (1285526171347 / 40000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13190 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13190]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13190])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13190) (a := (840339645537 / 1000000000000 : ℝ)) (b := (156094667831 / 100000000000000 : ℝ)) (q := (274336979247 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13190])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13190])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13190]

theorem cert13190_2 : CellCertificate 13190 (218372429863193 / 2500000000000000 : ℝ) (24881742972757 / 15625000000000000 : ℝ) (1285526171347 / 40000000000000 : ℝ)
    (cell13190 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · have h := gap_lower (n := 13190) (a := (83999101100801 / 100000000000000 : ℝ)) (b := (156094667831 / 100000000000000 : ℝ)) (q := (274337475931 / 12500000000000 : ℝ))
      (E := (cell13190 ⟨2, by decide⟩).energy) (xi := (1285526171347 / 40000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13190 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13190]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13190])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13190) (a := (83999101100801 / 100000000000000 : ℝ)) (b := (156094667831 / 100000000000000 : ℝ)) (q := (274337475931 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13190])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13190])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13190]

theorem cert13190_3 : CellCertificate 13190 (218372429863193 / 2500000000000000 : ℝ) (24881742972757 / 15625000000000000 : ℝ) (1285526171347 / 40000000000000 : ℝ)
    (cell13190 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · have h := gap_lower (n := 13190) (a := (16792852484823 / 20000000000000 : ℝ)) (b := (156094667831 / 100000000000000 : ℝ)) (q := (1097351926703 / 50000000000000 : ℝ))
      (E := (cell13190 ⟨3, by decide⟩).energy) (xi := (1285526171347 / 40000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13190 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13190]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13190])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13190) (a := (16792852484823 / 20000000000000 : ℝ)) (b := (156094667831 / 100000000000000 : ℝ)) (q := (1097351926703 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13190])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13190])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13190]

theorem cert13190_4 : CellCertificate 13190 (218372429863193 / 2500000000000000 : ℝ) (24881742972757 / 15625000000000000 : ℝ) (1285526171347 / 40000000000000 : ℝ)
    (cell13190 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · have h := gap_lower (n := 13190) (a := (83929448487603 / 100000000000000 : ℝ)) (b := (156094667831 / 100000000000000 : ℝ)) (q := (438941572827 / 20000000000000 : ℝ))
      (E := (cell13190 ⟨4, by decide⟩).energy) (xi := (1285526171347 / 40000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13190 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13190]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13190])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13190) (a := (83929448487603 / 100000000000000 : ℝ)) (b := (156094667831 / 100000000000000 : ℝ)) (q := (438941572827 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13190])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13190])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13190]

theorem cert13190_5 : CellCertificate 13190 (218372429863193 / 2500000000000000 : ℝ) (24881742972757 / 15625000000000000 : ℝ) (1285526171347 / 40000000000000 : ℝ)
    (cell13190 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · have h := gap_lower (n := 13190) (a := (83894659255413 / 100000000000000 : ℝ)) (b := (156094667831 / 100000000000000 : ℝ)) (q := (2194711847427 / 100000000000000 : ℝ))
      (E := (cell13190 ⟨5, by decide⟩).energy) (xi := (1285526171347 / 40000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13190 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13190]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13190])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13190) (a := (83894659255413 / 100000000000000 : ℝ)) (b := (156094667831 / 100000000000000 : ℝ)) (q := (2194711847427 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13190])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13190])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13190]

theorem cert13190_6 : CellCertificate 13190 (218372429863193 / 2500000000000000 : ℝ) (24881742972757 / 15625000000000000 : ℝ) (1285526171347 / 40000000000000 : ℝ)
    (cell13190 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · have h := gap_lower (n := 13190) (a := (41929947345941 / 50000000000000 : ℝ)) (b := (156094667831 / 100000000000000 : ℝ)) (q := (1097357934407 / 50000000000000 : ℝ))
      (E := (cell13190 ⟨6, by decide⟩).energy) (xi := (1285526171347 / 40000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13190 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13190]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13190])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13190) (a := (41929947345941 / 50000000000000 : ℝ)) (b := (156094667831 / 100000000000000 : ℝ)) (q := (1097357934407 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13190])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13190])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13190]

theorem cert13190_7 : CellCertificate 13190 (218372429863193 / 2500000000000000 : ℝ) (24881742972757 / 15625000000000000 : ℝ) (1285526171347 / 40000000000000 : ℝ)
    (cell13190 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · have h := gap_lower (n := 13190) (a := (20956288690383 / 25000000000000 : ℝ)) (b := (156094667831 / 100000000000000 : ℝ)) (q := (2194719877631 / 100000000000000 : ℝ))
      (E := (cell13190 ⟨7, by decide⟩).energy) (xi := (1285526171347 / 40000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13190 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13190]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13190])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13190) (a := (20956288690383 / 25000000000000 : ℝ)) (b := (156094667831 / 100000000000000 : ℝ)) (q := (2194719877631 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13190])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13190])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13190]

theorem cert13190_8 : CellCertificate 13190 (218372429863193 / 2500000000000000 : ℝ) (24881742972757 / 15625000000000000 : ℝ) (1285526171347 / 40000000000000 : ℝ)
    (cell13190 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · have h := gap_lower (n := 13190) (a := (5236902464317 / 6250000000000 : ℝ)) (b := (156094667831 / 100000000000000 : ℝ)) (q := (2194723938953 / 100000000000000 : ℝ))
      (E := (cell13190 ⟨8, by decide⟩).energy) (xi := (1285526171347 / 40000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13190 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13190]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13190])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13190) (a := (5236902464317 / 6250000000000 : ℝ)) (b := (156094667831 / 100000000000000 : ℝ)) (q := (2194723938953 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13190])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13190])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13190]

theorem cert13190_9 : CellCertificate 13190 (218372429863193 / 2500000000000000 : ℝ) (24881742972757 / 15625000000000000 : ℝ) (1285526171347 / 40000000000000 : ℝ)
    (cell13190 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · have h := gap_lower (n := 13190) (a := (20938937164849 / 25000000000000 : ℝ)) (b := (156094667831 / 100000000000000 : ℝ)) (q := (438945588699 / 20000000000000 : ℝ))
      (E := (cell13190 ⟨9, by decide⟩).energy) (xi := (1285526171347 / 40000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13190 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13190]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13190])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13190) (a := (20938937164849 / 25000000000000 : ℝ)) (b := (156094667831 / 100000000000000 : ℝ)) (q := (438945588699 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13190])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13190])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13190]

theorem cert13190_10 : CellCertificate 13190 (218372429863193 / 2500000000000000 : ℝ) (24881742972757 / 15625000000000000 : ℝ) (1285526171347 / 40000000000000 : ℝ)
    (cell13190 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · have h := gap_lower (n := 13190) (a := (4186054120879 / 5000000000000 : ℝ)) (b := (156094667831 / 100000000000000 : ℝ)) (q := (68585373619 / 3125000000000 : ℝ))
      (E := (cell13190 ⟨10, by decide⟩).energy) (xi := (1285526171347 / 40000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13190 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13190]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13190])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13190) (a := (4186054120879 / 5000000000000 : ℝ)) (b := (156094667831 / 100000000000000 : ℝ)) (q := (68585373619 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13190])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13190])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13190]

theorem cert13190_11 : CellCertificate 13190 (218372429863193 / 2500000000000000 : ℝ) (24881742972757 / 15625000000000000 : ℝ) (1285526171347 / 40000000000000 : ℝ)
    (cell13190 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · have h := gap_lower (n := 13190) (a := (83686440668881 / 100000000000000 : ℝ)) (b := (156094667831 / 100000000000000 : ℝ)) (q := (68585499443 / 3125000000000 : ℝ))
      (E := (cell13190 ⟨11, by decide⟩).energy) (xi := (1285526171347 / 40000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13190 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13190]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13190])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13190) (a := (83686440668881 / 100000000000000 : ℝ)) (b := (156094667831 / 100000000000000 : ℝ)) (q := (68585499443 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13190])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13190])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13190]

theorem cert13190_12 : CellCertificate 13190 (218372429863193 / 2500000000000000 : ℝ) (24881742972757 / 15625000000000000 : ℝ) (1285526171347 / 40000000000000 : ℝ)
    (cell13190 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · have h := gap_lower (n := 13190) (a := (4182591168937 / 5000000000000 : ℝ)) (b := (156094667831 / 100000000000000 : ℝ)) (q := (548684992623 / 25000000000000 : ℝ))
      (E := (cell13190 ⟨12, by decide⟩).energy) (xi := (1285526171347 / 40000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13190 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13190]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13190])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13190) (a := (4182591168937 / 5000000000000 : ℝ)) (b := (156094667831 / 100000000000000 : ℝ)) (q := (548684992623 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13190])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13190])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13190]

theorem cert13190_13 : CellCertificate 13190 (218372429863193 / 2500000000000000 : ℝ) (24881742972757 / 15625000000000000 : ℝ) (1285526171347 / 40000000000000 : ℝ)
    (cell13190 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · have h := gap_lower (n := 13190) (a := (41808615256387 / 50000000000000 : ℝ)) (b := (156094667831 / 100000000000000 : ℝ)) (q := (2194743984637 / 100000000000000 : ℝ))
      (E := (cell13190 ⟨13, by decide⟩).energy) (xi := (1285526171347 / 40000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13190 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13190]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13190])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13190) (a := (41808615256387 / 50000000000000 : ℝ)) (b := (156094667831 / 100000000000000 : ℝ)) (q := (2194743984637 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13190])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13190])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13190]

theorem cert13190_14 : CellCertificate 13190 (218372429863193 / 2500000000000000 : ℝ) (24881742972757 / 15625000000000000 : ℝ) (1285526171347 / 40000000000000 : ℝ)
    (cell13190 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · have h := gap_lower (n := 13190) (a := (83582662036781 / 100000000000000 : ℝ)) (b := (156094667831 / 100000000000000 : ℝ)) (q := (2194748030153 / 100000000000000 : ℝ))
      (E := (cell13190 ⟨14, by decide⟩).energy) (xi := (1285526171347 / 40000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13190 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13190]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13190])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13190) (a := (83582662036781 / 100000000000000 : ℝ)) (b := (156094667831 / 100000000000000 : ℝ)) (q := (2194748030153 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13190])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13190])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13190]

theorem cert13190_15 : CellCertificate 13190 (218372429863193 / 2500000000000000 : ℝ) (24881742972757 / 15625000000000000 : ℝ) (1285526171347 / 40000000000000 : ℝ)
    (cell13190 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · have h := gap_lower (n := 13190) (a := (16709623583347 / 20000000000000 : ℝ)) (b := (156094667831 / 100000000000000 : ℝ)) (q := (1097375997961 / 50000000000000 : ℝ))
      (E := (cell13190 ⟨15, by decide⟩).energy) (xi := (1285526171347 / 40000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13190 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13190]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13190])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13190) (a := (16709623583347 / 20000000000000 : ℝ)) (b := (156094667831 / 100000000000000 : ℝ)) (q := (1097375997961 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13190])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13190])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13190]

theorem cert13190_16 : CellCertificate 13190 (218372429863193 / 2500000000000000 : ℝ) (24881742972757 / 15625000000000000 : ℝ) (1285526171347 / 40000000000000 : ℝ)
    (cell13190 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · have h := gap_lower (n := 13190) (a := (83513598118787 / 100000000000000 : ℝ)) (b := (156094667831 / 100000000000000 : ℝ)) (q := (2194756061551 / 100000000000000 : ℝ))
      (E := (cell13190 ⟨16, by decide⟩).energy) (xi := (1285526171347 / 40000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13190 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13190]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13190])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13190) (a := (83513598118787 / 100000000000000 : ℝ)) (b := (156094667831 / 100000000000000 : ℝ)) (q := (2194756061551 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13190])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13190])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13190]

theorem cert13190_17 : CellCertificate 13190 (218372429863193 / 2500000000000000 : ℝ) (24881742972757 / 15625000000000000 : ℝ) (1285526171347 / 40000000000000 : ℝ)
    (cell13190 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · have h := gap_lower (n := 13190) (a := (83479102609261 / 100000000000000 : ℝ)) (b := (156094667831 / 100000000000000 : ℝ)) (q := (1097380028581 / 50000000000000 : ℝ))
      (E := (cell13190 ⟨17, by decide⟩).energy) (xi := (1285526171347 / 40000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13190 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13190]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13190])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13190) (a := (83479102609261 / 100000000000000 : ℝ)) (b := (156094667831 / 100000000000000 : ℝ)) (q := (1097380028581 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13190])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13190])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13190]

theorem cert13190_18 : CellCertificate 13190 (218372429863193 / 2500000000000000 : ℝ) (24881742972757 / 15625000000000000 : ℝ) (1285526171347 / 40000000000000 : ℝ)
    (cell13190 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · have h := gap_lower (n := 13190) (a := (41722315677329 / 50000000000000 : ℝ)) (b := (156094667831 / 100000000000000 : ℝ)) (q := (1097382022731 / 50000000000000 : ℝ))
      (E := (cell13190 ⟨18, by decide⟩).energy) (xi := (1285526171347 / 40000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13190 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13190]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13190])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13190) (a := (41722315677329 / 50000000000000 : ℝ)) (b := (156094667831 / 100000000000000 : ℝ)) (q := (1097382022731 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13190])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13190])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13190]

theorem cert13190_19 : CellCertificate 13190 (218372429863193 / 2500000000000000 : ℝ) (24881742972757 / 15625000000000000 : ℝ) (1285526171347 / 40000000000000 : ℝ)
    (cell13190 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · have h := gap_lower (n := 13190) (a := (1668203686433 / 2000000000000 : ℝ)) (b := (156094667831 / 100000000000000 : ℝ)) (q := (1097384044507 / 50000000000000 : ℝ))
      (E := (cell13190 ⟨19, by decide⟩).energy) (xi := (1285526171347 / 40000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13190 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13190]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13190])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13190) (a := (1668203686433 / 2000000000000 : ℝ)) (b := (156094667831 / 100000000000000 : ℝ)) (q := (1097384044507 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13190])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13190])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13190]

theorem cert13191_0 : CellCertificate 13191 (436731869974507 / 5000000000000000 : ℝ) (1592310790977921 / 1000000000000000000 : ℝ) (321356625682679 / 10000000000000000 : ℝ)
    (cell13191 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · have h := gap_lower (n := 13191) (a := (42034419397699 / 50000000000000 : ℝ)) (b := (78041350001 / 50000000000000 : ℝ)) (q := (438916320861 / 20000000000000 : ℝ))
      (E := (cell13191 ⟨0, by decide⟩).energy) (xi := (321356625682679 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13191 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13191]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13191])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13191) (a := (42034419397699 / 50000000000000 : ℝ)) (b := (78041350001 / 50000000000000 : ℝ)) (q := (438916320861 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13191])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13191])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13191]

theorem cert13191_1 : CellCertificate 13191 (436731869974507 / 5000000000000000 : ℝ) (1592310790977921 / 1000000000000000000 : ℝ) (321356625682679 / 10000000000000000 : ℝ)
    (cell13191 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · have h := gap_lower (n := 13191) (a := (84033950536279 / 100000000000000 : ℝ)) (b := (78041350001 / 50000000000000 : ℝ)) (q := (1097292813053 / 50000000000000 : ℝ))
      (E := (cell13191 ⟨1, by decide⟩).energy) (xi := (321356625682679 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13191 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13191]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13191])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13191) (a := (84033950536279 / 100000000000000 : ℝ)) (b := (78041350001 / 50000000000000 : ℝ)) (q := (1097292813053 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13191])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13191])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13191]

theorem cert13191_2 : CellCertificate 13191 (436731869974507 / 5000000000000000 : ℝ) (1592310790977921 / 1000000000000000000 : ℝ) (321356625682679 / 10000000000000000 : ℝ)
    (cell13191 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · have h := gap_lower (n := 13191) (a := (52499429431 / 62500000000 : ℝ)) (b := (78041350001 / 50000000000000 : ℝ)) (q := (438917930837 / 20000000000000 : ℝ))
      (E := (cell13191 ⟨2, by decide⟩).energy) (xi := (321356625682679 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13191 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13191]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13191])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13191) (a := (52499429431 / 62500000000 : ℝ)) (b := (78041350001 / 50000000000000 : ℝ)) (q := (438917930837 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13191])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13191])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13191]

theorem cert13191_3 : CellCertificate 13191 (436731869974507 / 5000000000000000 : ℝ) (1592310790977921 / 1000000000000000000 : ℝ) (321356625682679 / 10000000000000000 : ℝ)
    (cell13191 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · have h := gap_lower (n := 13191) (a := (83964248419129 / 100000000000000 : ℝ)) (b := (78041350001 / 50000000000000 : ℝ)) (q := (2194593638989 / 100000000000000 : ℝ))
      (E := (cell13191 ⟨3, by decide⟩).energy) (xi := (321356625682679 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13191 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13191]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13191])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13191) (a := (83964248419129 / 100000000000000 : ℝ)) (b := (78041350001 / 50000000000000 : ℝ)) (q := (2194593638989 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13191])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13191])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13191]

theorem cert13191_4 : CellCertificate 13191 (436731869974507 / 5000000000000000 : ℝ) (1592310790977921 / 1000000000000000000 : ℝ) (321356625682679 / 10000000000000000 : ℝ)
    (cell13191 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · have h := gap_lower (n := 13191) (a := (41964717244413 / 50000000000000 : ℝ)) (b := (78041350001 / 50000000000000 : ℝ)) (q := (438919540893 / 20000000000000 : ℝ))
      (E := (cell13191 ⟨4, by decide⟩).energy) (xi := (321356625682679 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13191 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13191]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13191])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13191) (a := (41964717244413 / 50000000000000 : ℝ)) (b := (78041350001 / 50000000000000 : ℝ)) (q := (438919540893 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13191])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13191])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13191]

theorem cert13191_5 : CellCertificate 13191 (436731869974507 / 5000000000000000 : ℝ) (1592310790977921 / 1000000000000000000 : ℝ) (321356625682679 / 10000000000000000 : ℝ)
    (cell13191 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · have h := gap_lower (n := 13191) (a := (83894645262839 / 100000000000000 : ℝ)) (b := (78041350001 / 50000000000000 : ℝ)) (q := (137162605289 / 6250000000000 : ℝ))
      (E := (cell13191 ⟨5, by decide⟩).energy) (xi := (321356625682679 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13191 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13191]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13191])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13191) (a := (83894645262839 / 100000000000000 : ℝ)) (b := (78041350001 / 50000000000000 : ℝ)) (q := (137162605289 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13191])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13191])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13191]

theorem cert13191_6 : CellCertificate 13191 (436731869974507 / 5000000000000000 : ℝ) (1592310790977921 / 1000000000000000000 : ℝ) (321356625682679 / 10000000000000000 : ℝ)
    (cell13191 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · have h := gap_lower (n := 13191) (a := (16771976141101 / 20000000000000 : ℝ)) (b := (78041350001 / 50000000000000 : ℝ)) (q := (1097302851463 / 50000000000000 : ℝ))
      (E := (cell13191 ⟨6, by decide⟩).energy) (xi := (321356625682679 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13191 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13191]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13191])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13191) (a := (16771976141101 / 20000000000000 : ℝ)) (b := (78041350001 / 50000000000000 : ℝ)) (q := (1097302851463 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13191])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13191])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13191]

theorem cert13191_7 : CellCertificate 13191 (436731869974507 / 5000000000000000 : ℝ) (1592310790977921 / 1000000000000000000 : ℝ) (321356625682679 / 10000000000000000 : ℝ)
    (cell13191 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · have h := gap_lower (n := 13191) (a := (83825140781347 / 100000000000000 : ℝ)) (b := (78041350001 / 50000000000000 : ℝ)) (q := (68581553397 / 3125000000000 : ℝ))
      (E := (cell13191 ⟨7, by decide⟩).energy) (xi := (321356625682679 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13191 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13191]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13191])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13191) (a := (83825140781347 / 100000000000000 : ℝ)) (b := (78041350001 / 50000000000000 : ℝ)) (q := (68581553397 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13191])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13191])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13191]

theorem cert13191_8 : CellCertificate 13191 (436731869974507 / 5000000000000000 : ℝ) (1592310790977921 / 1000000000000000000 : ℝ) (321356625682679 / 10000000000000000 : ℝ)
    (cell13191 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · have h := gap_lower (n := 13191) (a := (41895212727537 / 50000000000000 : ℝ)) (b := (78041350001 / 50000000000000 : ℝ)) (q := (219461370899 / 10000000000000 : ℝ))
      (E := (cell13191 ⟨8, by decide⟩).energy) (xi := (321356625682679 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13191 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13191]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13191])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13191) (a := (41895212727537 / 50000000000000 : ℝ)) (b := (78041350001 / 50000000000000 : ℝ)) (q := (219461370899 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13191])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13191])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13191]

theorem cert13191_9 : CellCertificate 13191 (436731869974507 / 5000000000000000 : ℝ) (1592310790977921 / 1000000000000000000 : ℝ) (321356625682679 / 10000000000000000 : ℝ)
    (cell13191 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · have h := gap_lower (n := 13191) (a := (83755734691579 / 100000000000000 : ℝ)) (b := (78041350001 / 50000000000000 : ℝ)) (q := (274327221079 / 12500000000000 : ℝ))
      (E := (cell13191 ⟨9, by decide⟩).energy) (xi := (321356625682679 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13191 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13191]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13191])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13191) (a := (83755734691579 / 100000000000000 : ℝ)) (b := (78041350001 / 50000000000000 : ℝ)) (q := (274327221079 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13191])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13191])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13191]

theorem cert13191_10 : CellCertificate 13191 (436731869974507 / 5000000000000000 : ℝ) (1592310790977921 / 1000000000000000000 : ℝ) (321356625682679 / 10000000000000000 : ℝ)
    (cell13191 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · have h := gap_lower (n := 13191) (a := (41860534227969 / 50000000000000 : ℝ)) (b := (78041350001 / 50000000000000 : ℝ)) (q := (17145482641 / 781250000000 : ℝ))
      (E := (cell13191 ⟨10, by decide⟩).energy) (xi := (321356625682679 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13191 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13191]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13191])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13191) (a := (41860534227969 / 50000000000000 : ℝ)) (b := (78041350001 / 50000000000000 : ℝ)) (q := (17145482641 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13191])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13191])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13191]

theorem cert13191_11 : CellCertificate 13191 (436731869974507 / 5000000000000000 : ℝ) (1592310790977921 / 1000000000000000000 : ℝ) (321356625682679 / 10000000000000000 : ℝ)
    (cell13191 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · have h := gap_lower (n := 13191) (a := (8368642671341 / 10000000000000 : ℝ)) (b := (78041350001 / 50000000000000 : ℝ)) (q := (2194625801563 / 100000000000000 : ℝ))
      (E := (cell13191 ⟨11, by decide⟩).energy) (xi := (321356625682679 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13191 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13191]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13191])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13191) (a := (8368642671341 / 10000000000000 : ℝ)) (b := (78041350001 / 50000000000000 : ℝ)) (q := (2194625801563 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13191])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13191])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13191]

theorem cert13191_12 : CellCertificate 13191 (436731869974507 / 5000000000000000 : ℝ) (1592310790977921 / 1000000000000000000 : ℝ) (321356625682679 / 10000000000000000 : ℝ)
    (cell13191 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · have h := gap_lower (n := 13191) (a := (41825904714717 / 50000000000000 : ℝ)) (b := (78041350001 / 50000000000000 : ℝ)) (q := (87785191483 / 4000000000000 : ℝ))
      (E := (cell13191 ⟨12, by decide⟩).energy) (xi := (321356625682679 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13191 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13191]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13191])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13191) (a := (41825904714717 / 50000000000000 : ℝ)) (b := (78041350001 / 50000000000000 : ℝ)) (q := (87785191483 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13191])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13191])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13191]

theorem cert13191_13 : CellCertificate 13191 (436731869974507 / 5000000000000000 : ℝ) (1592310790977921 / 1000000000000000000 : ℝ) (321356625682679 / 10000000000000000 : ℝ)
    (cell13191 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · have h := gap_lower (n := 13191) (a := (20904304142407 / 25000000000000 : ℝ)) (b := (78041350001 / 50000000000000 : ℝ)) (q := (1097316899231 / 50000000000000 : ℝ))
      (E := (cell13191 ⟨13, by decide⟩).energy) (xi := (321356625682679 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13191 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13191]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13191])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13191) (a := (20904304142407 / 25000000000000 : ℝ)) (b := (78041350001 / 50000000000000 : ℝ)) (q := (1097316899231 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13191])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13191])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13191]

theorem cert13191_14 : CellCertificate 13191 (436731869974507 / 5000000000000000 : ℝ) (1592310790977921 / 1000000000000000000 : ℝ) (321356625682679 / 10000000000000000 : ℝ)
    (cell13191 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · have h := gap_lower (n := 13191) (a := (20895662024947 / 25000000000000 : ℝ)) (b := (78041350001 / 50000000000000 : ℝ)) (q := (548659460317 / 25000000000000 : ℝ))
      (E := (cell13191 ⟨14, by decide⟩).energy) (xi := (321356625682679 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13191 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13191]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13191])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13191) (a := (20895662024947 / 25000000000000 : ℝ)) (b := (78041350001 / 50000000000000 : ℝ)) (q := (548659460317 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13191])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13191])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13191]

theorem cert13191_15 : CellCertificate 13191 (436731869974507 / 5000000000000000 : ℝ) (1592310790977921 / 1000000000000000000 : ℝ) (321356625682679 / 10000000000000000 : ℝ)
    (cell13191 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · have h := gap_lower (n := 13191) (a := (83548103985891 / 100000000000000 : ℝ)) (b := (78041350001 / 50000000000000 : ℝ)) (q := (109732093129 / 5000000000000 : ℝ))
      (E := (cell13191 ⟨15, by decide⟩).energy) (xi := (321356625682679 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13191 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13191]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13191])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13191) (a := (83548103985891 / 100000000000000 : ℝ)) (b := (78041350001 / 50000000000000 : ℝ)) (q := (109732093129 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13191])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13191])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13191]

theorem cert13191_16 : CellCertificate 13191 (436731869974507 / 5000000000000000 : ℝ) (1592310790977921 / 1000000000000000000 : ℝ) (321356625682679 / 10000000000000000 : ℝ)
    (cell13191 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · have h := gap_lower (n := 13191) (a := (16702716838817 / 20000000000000 : ℝ)) (b := (78041350001 / 50000000000000 : ℝ)) (q := (438929173477 / 20000000000000 : ℝ))
      (E := (cell13191 ⟨16, by decide⟩).energy) (xi := (321356625682679 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13191 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13191]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13191])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13191) (a := (16702716838817 / 20000000000000 : ℝ)) (b := (78041350001 / 50000000000000 : ℝ)) (q := (438929173477 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13191])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13191])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13191]

theorem cert13191_17 : CellCertificate 13191 (436731869974507 / 5000000000000000 : ℝ) (1592310790977921 / 1000000000000000000 : ℝ) (321356625682679 / 10000000000000000 : ℝ)
    (cell13191 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · have h := gap_lower (n := 13191) (a := (41739544345349 / 50000000000000 : ℝ)) (b := (78041350001 / 50000000000000 : ℝ)) (q := (274331232553 / 12500000000000 : ℝ))
      (E := (cell13191 ⟨17, by decide⟩).energy) (xi := (321356625682679 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13191 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13191]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13191])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13191) (a := (41739544345349 / 50000000000000 : ℝ)) (b := (78041350001 / 50000000000000 : ℝ)) (q := (274331232553 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13191])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13191])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13191]

theorem cert13191_18 : CellCertificate 13191 (436731869974507 / 5000000000000000 : ℝ) (1592310790977921 / 1000000000000000000 : ℝ) (321356625682679 / 10000000000000000 : ℝ)
    (cell13191 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · have h := gap_lower (n := 13191) (a := (83444617442227 / 100000000000000 : ℝ)) (b := (78041350001 / 50000000000000 : ℝ)) (q := (2194653904479 / 100000000000000 : ℝ))
      (E := (cell13191 ⟨18, by decide⟩).energy) (xi := (321356625682679 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13191 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13191]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13191])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13191) (a := (83444617442227 / 100000000000000 : ℝ)) (b := (78041350001 / 50000000000000 : ℝ)) (q := (2194653904479 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13191])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13191])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13191]

theorem cert13191_19 : CellCertificate 13191 (436731869974507 / 5000000000000000 : ℝ) (1592310790977921 / 1000000000000000000 : ℝ) (321356625682679 / 10000000000000000 : ℝ)
    (cell13191 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · have h := gap_lower (n := 13191) (a := (41705085207673 / 50000000000000 : ℝ)) (b := (78041350001 / 50000000000000 : ℝ)) (q := (548664471819 / 25000000000000 : ℝ))
      (E := (cell13191 ⟨19, by decide⟩).energy) (xi := (321356625682679 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13191 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13191]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13191])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13191) (a := (41705085207673 / 50000000000000 : ℝ)) (b := (78041350001 / 50000000000000 : ℝ)) (q := (548664471819 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13191])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13191])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13191]

theorem cert13192_0 : CellCertificate 13192 (873437764212951 / 10000000000000000 : ℝ) (1592190050013143 / 1000000000000000000 : ℝ) (321331712415843 / 10000000000000000 : ℝ)
    (cell13192 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · have h := gap_lower (n := 13192) (a := (2101720619347 / 2500000000000 : ℝ)) (b := (31214146803 / 20000000000000 : ℝ)) (q := (548617863363 / 25000000000000 : ℝ))
      (E := (cell13192 ⟨0, by decide⟩).energy) (xi := (321331712415843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13192 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13192]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13192])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13192) (a := (2101720619347 / 2500000000000 : ℝ)) (b := (31214146803 / 20000000000000 : ℝ)) (q := (548617863363 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13192])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13192])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13192]

theorem cert13192_1 : CellCertificate 13192 (873437764212951 / 10000000000000000 : ℝ) (1592190050013143 / 1000000000000000000 : ℝ) (321331712415843 / 10000000000000000 : ℝ)
    (cell13192 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · have h := gap_lower (n := 13192) (a := (42016968260493 / 50000000000000 : ℝ)) (b := (31214146803 / 20000000000000 : ℝ)) (q := (2194475471933 / 100000000000000 : ℝ))
      (E := (cell13192 ⟨1, by decide⟩).energy) (xi := (321331712415843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13192 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13192]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13192])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13192) (a := (42016968260493 / 50000000000000 : ℝ)) (b := (31214146803 / 20000000000000 : ℝ)) (q := (2194475471933 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13192])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13192])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13192]

theorem cert13192_2 : CellCertificate 13192 (873437764212951 / 10000000000000000 : ℝ) (1592190050013143 / 1000000000000000000 : ℝ) (321331712415843 / 10000000000000000 : ℝ)
    (cell13192 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · have h := gap_lower (n := 13192) (a := (41999536540263 / 50000000000000 : ℝ)) (b := (31214146803 / 20000000000000 : ℝ)) (q := (2194479496739 / 100000000000000 : ℝ))
      (E := (cell13192 ⟨2, by decide⟩).energy) (xi := (321331712415843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13192 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13192]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13192])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13192) (a := (41999536540263 / 50000000000000 : ℝ)) (b := (31214146803 / 20000000000000 : ℝ)) (q := (2194479496739 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13192])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13192])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13192]

theorem cert13192_3 : CellCertificate 13192 (873437764212951 / 10000000000000000 : ℝ) (1592190050013143 / 1000000000000000000 : ℝ) (321331712415843 / 10000000000000000 : ℝ)
    (cell13192 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · have h := gap_lower (n := 13192) (a := (83964234416269 / 100000000000000 : ℝ)) (b := (31214146803 / 20000000000000 : ℝ)) (q := (548620869579 / 25000000000000 : ℝ))
      (E := (cell13192 ⟨3, by decide⟩).energy) (xi := (321331712415843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13192 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13192]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13192])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13192) (a := (83964234416269 / 100000000000000 : ℝ)) (b := (31214146803 / 20000000000000 : ℝ)) (q := (548620869579 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13192])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13192])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13192]

theorem cert13192_4 : CellCertificate 13192 (873437764212951 / 10000000000000000 : ℝ) (1592190050013143 / 1000000000000000000 : ℝ) (321331712415843 / 10000000000000000 : ℝ)
    (cell13192 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · have h := gap_lower (n := 13192) (a := (41964710246087 / 50000000000000 : ℝ)) (b := (31214146803 / 20000000000000 : ℝ)) (q := (1097243770307 / 50000000000000 : ℝ))
      (E := (cell13192 ⟨4, by decide⟩).energy) (xi := (321331712415843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13192 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13192]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13192])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13192) (a := (41964710246087 / 50000000000000 : ℝ)) (b := (31214146803 / 20000000000000 : ℝ)) (q := (1097243770307 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13192])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13192])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13192]

theorem cert13192_5 : CellCertificate 13192 (873437764212951 / 10000000000000000 : ℝ) (1592190050013143 / 1000000000000000000 : ℝ) (321331712415843 / 10000000000000000 : ℝ)
    (cell13192 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · have h := gap_lower (n := 13192) (a := (83894631272389 / 100000000000000 : ℝ)) (b := (31214146803 / 20000000000000 : ℝ)) (q := (2194491517641 / 100000000000000 : ℝ))
      (E := (cell13192 ⟨5, by decide⟩).energy) (xi := (321331712415843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13192 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13192]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13192])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13192) (a := (83894631272389 / 100000000000000 : ℝ)) (b := (31214146803 / 20000000000000 : ℝ)) (q := (2194491517641 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13192])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13192])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13192]

theorem cert13192_6 : CellCertificate 13192 (873437764212951 / 10000000000000000 : ℝ) (1592190050013143 / 1000000000000000000 : ℝ) (321331712415843 / 10000000000000000 : ℝ)
    (cell13192 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · have h := gap_lower (n := 13192) (a := (20964966680313 / 25000000000000 : ℝ)) (b := (31214146803 / 20000000000000 : ℝ)) (q := (1097247766429 / 50000000000000 : ℝ))
      (E := (cell13192 ⟨6, by decide⟩).energy) (xi := (321331712415843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13192 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13192]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13192])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13192) (a := (20964966680313 / 25000000000000 : ℝ)) (b := (31214146803 / 20000000000000 : ℝ)) (q := (1097247766429 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13192])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13192])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13192]

theorem cert13192_7 : CellCertificate 13192 (873437764212951 / 10000000000000000 : ℝ) (1592190050013143 / 1000000000000000000 : ℝ) (321331712415843 / 10000000000000000 : ℝ)
    (cell13192 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · have h := gap_lower (n := 13192) (a := (16765025360657 / 20000000000000 : ℝ)) (b := (31214146803 / 20000000000000 : ℝ)) (q := (1097249767799 / 50000000000000 : ℝ))
      (E := (cell13192 ⟨7, by decide⟩).energy) (xi := (321331712415843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13192 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13192]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13192])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13192) (a := (16765025360657 / 20000000000000 : ℝ)) (b := (31214146803 / 20000000000000 : ℝ)) (q := (1097249767799 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13192])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13192])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13192]

theorem cert13192_8 : CellCertificate 13192 (873437764212951 / 10000000000000000 : ℝ) (1592190050013143 / 1000000000000000000 : ℝ) (321331712415843 / 10000000000000000 : ℝ)
    (cell13192 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · have h := gap_lower (n := 13192) (a := (83790411483197 / 100000000000000 : ℝ)) (b := (31214146803 / 20000000000000 : ℝ)) (q := (1097251795469 / 50000000000000 : ℝ))
      (E := (cell13192 ⟨8, by decide⟩).energy) (xi := (321331712415843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13192 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13192]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13192])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13192) (a := (83790411483197 / 100000000000000 : ℝ)) (b := (31214146803 / 20000000000000 : ℝ)) (q := (1097251795469 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13192])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13192])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13192]

theorem cert13192_9 : CellCertificate 13192 (873437764212951 / 10000000000000000 : ℝ) (1592190050013143 / 1000000000000000000 : ℝ) (321331712415843 / 10000000000000000 : ℝ)
    (cell13192 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · have h := gap_lower (n := 13192) (a := (83755720725883 / 100000000000000 : ℝ)) (b := (31214146803 / 20000000000000 : ℝ)) (q := (219450758959 / 10000000000000 : ℝ))
      (E := (cell13192 ⟨9, by decide⟩).energy) (xi := (321331712415843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13192 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13192]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13192])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13192) (a := (83755720725883 / 100000000000000 : ℝ)) (b := (31214146803 / 20000000000000 : ℝ)) (q := (219450758959 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13192])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13192])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13192]

theorem cert13192_10 : CellCertificate 13192 (873437764212951 / 10000000000000000 : ℝ) (1592190050013143 / 1000000000000000000 : ℝ) (321331712415843 / 10000000000000000 : ℝ)
    (cell13192 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · have h := gap_lower (n := 13192) (a := (83721054496417 / 100000000000000 : ℝ)) (b := (31214146803 / 20000000000000 : ℝ)) (q := (2194511596109 / 100000000000000 : ℝ))
      (E := (cell13192 ⟨10, by decide⟩).energy) (xi := (321331712415843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13192 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13192]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13192])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13192) (a := (83721054496417 / 100000000000000 : ℝ)) (b := (31214146803 / 20000000000000 : ℝ)) (q := (2194511596109 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13192])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13192])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13192]

theorem cert13192_11 : CellCertificate 13192 (873437764212951 / 10000000000000000 : ℝ) (1592190050013143 / 1000000000000000000 : ℝ) (321331712415843 / 10000000000000000 : ℝ)
    (cell13192 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · have h := gap_lower (n := 13192) (a := (41843206380029 / 50000000000000 : ℝ)) (b := (31214146803 / 20000000000000 : ℝ)) (q := (1097257808387 / 50000000000000 : ℝ))
      (E := (cell13192 ⟨11, by decide⟩).energy) (xi := (321331712415843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13192 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13192]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13192])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13192) (a := (41843206380029 / 50000000000000 : ℝ)) (b := (31214146803 / 20000000000000 : ℝ)) (q := (1097257808387 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13192])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13192])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13192]

theorem cert13192_12 : CellCertificate 13192 (873437764212951 / 10000000000000000 : ℝ) (1592190050013143 / 1000000000000000000 : ℝ) (321331712415843 / 10000000000000000 : ℝ)
    (cell13192 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · have h := gap_lower (n := 13192) (a := (16730359096449 / 20000000000000 : ℝ)) (b := (31214146803 / 20000000000000 : ℝ)) (q := (2194519657621 / 100000000000000 : ℝ))
      (E := (cell13192 ⟨12, by decide⟩).energy) (xi := (321331712415843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13192 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13192]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13192])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13192) (a := (16730359096449 / 20000000000000 : ℝ)) (b := (31214146803 / 20000000000000 : ℝ)) (q := (2194519657621 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13192])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13192])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13192]

theorem cert13192_13 : CellCertificate 13192 (873437764212951 / 10000000000000000 : ℝ) (1592190050013143 / 1000000000000000000 : ℝ) (321331712415843 / 10000000000000000 : ℝ)
    (cell13192 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · have h := gap_lower (n := 13192) (a := (83617202628597 / 100000000000000 : ℝ)) (b := (31214146803 / 20000000000000 : ℝ)) (q := (87780946651 / 4000000000000 : ℝ))
      (E := (cell13192 ⟨13, by decide⟩).energy) (xi := (321331712415843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13192 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13192]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13192])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13192) (a := (83617202628597 / 100000000000000 : ℝ)) (b := (31214146803 / 20000000000000 : ℝ)) (q := (87780946651 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13192])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13192])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13192]

theorem cert13192_14 : CellCertificate 13192 (873437764212951 / 10000000000000000 : ℝ) (1592190050013143 / 1000000000000000000 : ℝ) (321331712415843 / 10000000000000000 : ℝ)
    (cell13192 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · have h := gap_lower (n := 13192) (a := (83582634164911 / 100000000000000 : ℝ)) (b := (31214146803 / 20000000000000 : ℝ)) (q := (2194527648209 / 100000000000000 : ℝ))
      (E := (cell13192 ⟨14, by decide⟩).energy) (xi := (321331712415843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13192 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13192]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13192])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13192) (a := (83582634164911 / 100000000000000 : ℝ)) (b := (31214146803 / 20000000000000 : ℝ)) (q := (2194527648209 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13192])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13192])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13192]

theorem cert13192_15 : CellCertificate 13192 (873437764212951 / 10000000000000000 : ℝ) (1592190050013143 / 1000000000000000000 : ℝ) (321331712415843 / 10000000000000000 : ℝ)
    (cell13192 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · have h := gap_lower (n := 13192) (a := (83548090057161 / 100000000000000 : ℝ)) (b := (31214146803 / 20000000000000 : ℝ)) (q := (1097265833429 / 50000000000000 : ℝ))
      (E := (cell13192 ⟨15, by decide⟩).energy) (xi := (321331712415843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13192 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13192]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13192])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13192) (a := (83548090057161 / 100000000000000 : ℝ)) (b := (31214146803 / 20000000000000 : ℝ)) (q := (1097265833429 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13192])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13192])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13192]

theorem cert13192_16 : CellCertificate 13192 (873437764212951 / 10000000000000000 : ℝ) (1592190050013143 / 1000000000000000000 : ℝ) (321331712415843 / 10000000000000000 : ℝ)
    (cell13192 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · have h := gap_lower (n := 13192) (a := (41756785135749 / 50000000000000 : ℝ)) (b := (31214146803 / 20000000000000 : ℝ)) (q := (1097267834523 / 50000000000000 : ℝ))
      (E := (cell13192 ⟨16, by decide⟩).energy) (xi := (321331712415843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13192 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13192]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13192])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13192) (a := (41756785135749 / 50000000000000 : ℝ)) (b := (31214146803 / 20000000000000 : ℝ)) (q := (1097267834523 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13192])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13192])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13192]

theorem cert13192_17 : CellCertificate 13192 (873437764212951 / 10000000000000000 : ℝ) (1592190050013143 / 1000000000000000000 : ℝ) (321331712415843 / 10000000000000000 : ℝ)
    (cell13192 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · have h := gap_lower (n := 13192) (a := (83479074774247 / 100000000000000 : ℝ)) (b := (31214146803 / 20000000000000 : ℝ)) (q := (2194539717771 / 100000000000000 : ℝ))
      (E := (cell13192 ⟨17, by decide⟩).energy) (xi := (321331712415843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13192 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13192]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13192])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13192) (a := (83479074774247 / 100000000000000 : ℝ)) (b := (31214146803 / 20000000000000 : ℝ)) (q := (2194539717771 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13192])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13192])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13192]

theorem cert13192_18 : CellCertificate 13192 (873437764212951 / 10000000000000000 : ℝ) (1592190050013143 / 1000000000000000000 : ℝ) (321331712415843 / 10000000000000000 : ℝ)
    (cell13192 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · have h := gap_lower (n := 13192) (a := (20861150882977 / 25000000000000 : ℝ)) (b := (31214146803 / 20000000000000 : ℝ)) (q := (2194543701047 / 100000000000000 : ℝ))
      (E := (cell13192 ⟨18, by decide⟩).energy) (xi := (321331712415843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13192 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13192]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13192])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13192) (a := (20861150882977 / 25000000000000 : ℝ)) (b := (31214146803 / 20000000000000 : ℝ)) (q := (2194543701047 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13192])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13192])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13192]

theorem cert13192_19 : CellCertificate 13192 (873437764212951 / 10000000000000000 : ℝ) (1592190050013143 / 1000000000000000000 : ℝ) (321331712415843 / 10000000000000000 : ℝ)
    (cell13192 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · have h := gap_lower (n := 13192) (a := (83410156511153 / 100000000000000 : ℝ)) (b := (31214146803 / 20000000000000 : ℝ)) (q := (2194547739669 / 100000000000000 : ℝ))
      (E := (cell13192 ⟨19, by decide⟩).energy) (xi := (321331712415843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13192 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13192]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13192])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13192) (a := (83410156511153 / 100000000000000 : ℝ)) (b := (31214146803 / 20000000000000 : ℝ)) (q := (2194547739669 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13192])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13192])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13192]

theorem cert13193_0 : CellCertificate 13193 (34936471689749 / 400000000000000 : ℝ) (31841386547159 / 20000000000000000 : ℝ) (64261360607057 / 2000000000000000 : ℝ)
    (cell13193 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · have h := gap_lower (n := 13193) (a := (84068810754491 / 100000000000000 : ℝ)) (b := (39014692467 / 25000000000000 : ℝ)) (q := (438872259683 / 20000000000000 : ℝ))
      (E := (cell13193 ⟨0, by decide⟩).energy) (xi := (64261360607057 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13193 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13193]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13193])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13193) (a := (84068810754491 / 100000000000000 : ℝ)) (b := (39014692467 / 25000000000000 : ℝ)) (q := (438872259683 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13193])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13193])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13193]

theorem cert13193_1 : CellCertificate 13193 (34936471689749 / 400000000000000 : ℝ) (31841386547159 / 20000000000000000 : ℝ) (64261360607057 / 2000000000000000 : ℝ)
    (cell13193 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · have h := gap_lower (n := 13193) (a := (84033922507821 / 100000000000000 : ℝ)) (b := (39014692467 / 25000000000000 : ℝ)) (q := (2194365313577 / 100000000000000 : ℝ))
      (E := (cell13193 ⟨1, by decide⟩).energy) (xi := (64261360607057 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13193 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13193]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13193])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13193) (a := (84033922507821 / 100000000000000 : ℝ)) (b := (39014692467 / 25000000000000 : ℝ)) (q := (2194365313577 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13193])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13193])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13193]

theorem cert13193_2 : CellCertificate 13193 (34936471689749 / 400000000000000 : ℝ) (31841386547159 / 20000000000000000 : ℝ) (64261360607057 / 2000000000000000 : ℝ)
    (cell13193 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · have h := gap_lower (n := 13193) (a := (83999059073579 / 100000000000000 : ℝ)) (b := (39014692467 / 25000000000000 : ℝ)) (q := (2194369335111 / 100000000000000 : ℝ))
      (E := (cell13193 ⟨2, by decide⟩).energy) (xi := (64261360607057 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13193 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13193]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13193])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13193) (a := (83999059073579 / 100000000000000 : ℝ)) (b := (39014692467 / 25000000000000 : ℝ)) (q := (2194369335111 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13193])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13193])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13193]

theorem cert13193_3 : CellCertificate 13193 (34936471689749 / 400000000000000 : ℝ) (31841386547159 / 20000000000000000 : ℝ) (64261360607057 / 2000000000000000 : ℝ)
    (cell13193 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · have h := gap_lower (n := 13193) (a := (41982110207767 / 50000000000000 : ℝ)) (b := (39014692467 / 25000000000000 : ℝ)) (q := (2194373371391 / 100000000000000 : ℝ))
      (E := (cell13193 ⟨3, by decide⟩).energy) (xi := (64261360607057 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13193 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13193]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13193])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13193) (a := (41982110207767 / 50000000000000 : ℝ)) (b := (39014692467 / 25000000000000 : ℝ)) (q := (2194373371391 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13193])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13193])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13193]

theorem cert13193_4 : CellCertificate 13193 (34936471689749 / 400000000000000 : ℝ) (31841386547159 / 20000000000000000 : ℝ) (64261360607057 / 2000000000000000 : ℝ)
    (cell13193 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · have h := gap_lower (n := 13193) (a := (41964703248823 / 50000000000000 : ℝ)) (b := (39014692467 / 25000000000000 : ℝ)) (q := (2194377372583 / 100000000000000 : ℝ))
      (E := (cell13193 ⟨4, by decide⟩).energy) (xi := (64261360607057 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13193 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13193]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13193])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13193) (a := (41964703248823 / 50000000000000 : ℝ)) (b := (39014692467 / 25000000000000 : ℝ)) (q := (2194377372583 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13193])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13193])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13193]

theorem cert13193_5 : CellCertificate 13193 (34936471689749 / 400000000000000 : ℝ) (31841386547159 / 20000000000000000 : ℝ) (64261360607057 / 2000000000000000 : ℝ)
    (cell13193 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · have h := gap_lower (n := 13193) (a := (41947308642031 / 50000000000000 : ℝ)) (b := (39014692467 / 25000000000000 : ℝ)) (q := (1097190702227 / 50000000000000 : ℝ))
      (E := (cell13193 ⟨5, by decide⟩).energy) (xi := (64261360607057 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13193 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13193]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13193])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13193) (a := (41947308642031 / 50000000000000 : ℝ)) (b := (39014692467 / 25000000000000 : ℝ)) (q := (1097190702227 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13193])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13193])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13193]

theorem cert13193_6 : CellCertificate 13193 (34936471689749 / 400000000000000 : ℝ) (31841386547159 / 20000000000000000 : ℝ) (64261360607057 / 2000000000000000 : ℝ)
    (cell13193 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · have h := gap_lower (n := 13193) (a := (83859852739121 / 100000000000000 : ℝ)) (b := (39014692467 / 25000000000000 : ℝ)) (q := (219438541661 / 10000000000000 : ℝ))
      (E := (cell13193 ⟨6, by decide⟩).energy) (xi := (64261360607057 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13193 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13193]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13193])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13193) (a := (83859852739121 / 100000000000000 : ℝ)) (b := (39014692467 / 25000000000000 : ℝ)) (q := (219438541661 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13193])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13193])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13193]

theorem cert13193_7 : CellCertificate 13193 (34936471689749 / 400000000000000 : ℝ) (31841386547159 / 20000000000000000 : ℝ) (64261360607057 / 2000000000000000 : ℝ)
    (cell13193 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · have h := gap_lower (n := 13193) (a := (5239069551709 / 6250000000000 : ℝ)) (b := (39014692467 / 25000000000000 : ℝ)) (q := (2194389416337 / 100000000000000 : ℝ))
      (E := (cell13193 ⟨7, by decide⟩).energy) (xi := (64261360607057 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13193 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13193]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13193])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13193) (a := (5239069551709 / 6250000000000 : ℝ)) (b := (39014692467 / 25000000000000 : ℝ)) (q := (2194389416337 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13193])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13193])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13193]

theorem cert13193_8 : CellCertificate 13193 (34936471689749 / 400000000000000 : ℝ) (31841386547159 / 20000000000000000 : ℝ) (64261360607057 / 2000000000000000 : ℝ)
    (cell13193 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · have h := gap_lower (n := 13193) (a := (41895198756721 / 50000000000000 : ℝ)) (b := (39014692467 / 25000000000000 : ℝ)) (q := (438878682133 / 20000000000000 : ℝ))
      (E := (cell13193 ⟨8, by decide⟩).energy) (xi := (64261360607057 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13193 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13193]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13193])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13193) (a := (41895198756721 / 50000000000000 : ℝ)) (b := (39014692467 / 25000000000000 : ℝ)) (q := (438878682133 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13193])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13193])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13193]

theorem cert13193_9 : CellCertificate 13193 (34936471689749 / 400000000000000 : ℝ) (31841386547159 / 20000000000000000 : ℝ) (64261360607057 / 2000000000000000 : ℝ)
    (cell13193 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · have h := gap_lower (n := 13193) (a := (41877853381153 / 50000000000000 : ℝ)) (b := (39014692467 / 25000000000000 : ℝ)) (q := (2194397464443 / 100000000000000 : ℝ))
      (E := (cell13193 ⟨9, by decide⟩).energy) (xi := (64261360607057 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13193 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13193]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13193])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13193) (a := (41877853381153 / 50000000000000 : ℝ)) (b := (39014692467 / 25000000000000 : ℝ)) (q := (2194397464443 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13193])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13193])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13193]

theorem cert13193_10 : CellCertificate 13193 (34936471689749 / 400000000000000 : ℝ) (31841386547159 / 20000000000000000 : ℝ) (64261360607057 / 2000000000000000 : ℝ)
    (cell13193 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · have h := gap_lower (n := 13193) (a := (41860520269507 / 50000000000000 : ℝ)) (b := (39014692467 / 25000000000000 : ℝ)) (q := (274300183511 / 12500000000000 : ℝ))
      (E := (cell13193 ⟨10, by decide⟩).energy) (xi := (64261360607057 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13193 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13193]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13193])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13193) (a := (41860520269507 / 50000000000000 : ℝ)) (b := (39014692467 / 25000000000000 : ℝ)) (q := (274300183511 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13193])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13193])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13193]

theorem cert13193_11 : CellCertificate 13193 (34936471689749 / 400000000000000 : ℝ) (31841386547159 / 20000000000000000 : ℝ) (64261360607057 / 2000000000000000 : ℝ)
    (cell13193 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · have h := gap_lower (n := 13193) (a := (83686398808823 / 100000000000000 : ℝ)) (b := (39014692467 / 25000000000000 : ℝ)) (q := (2194405485927 / 100000000000000 : ℝ))
      (E := (cell13193 ⟨11, by decide⟩).energy) (xi := (64261360607057 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13193 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13193]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13193])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13193) (a := (83686398808823 / 100000000000000 : ℝ)) (b := (39014692467 / 25000000000000 : ℝ)) (q := (2194405485927 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13193])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13193])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13193]

theorem cert13193_12 : CellCertificate 13193 (34936471689749 / 400000000000000 : ℝ) (31841386547159 / 20000000000000000 : ℝ) (64261360607057 / 2000000000000000 : ℝ)
    (cell13193 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · have h := gap_lower (n := 13193) (a := (83651781537173 / 100000000000000 : ℝ)) (b := (39014692467 / 25000000000000 : ℝ)) (q := (2194409465857 / 100000000000000 : ℝ))
      (E := (cell13193 ⟨12, by decide⟩).energy) (xi := (64261360607057 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13193 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13193]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13193])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13193) (a := (83651781537173 / 100000000000000 : ℝ)) (b := (39014692467 / 25000000000000 : ℝ)) (q := (2194409465857 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13193])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13193])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13193]

theorem cert13193_13 : CellCertificate 13193 (34936471689749 / 400000000000000 : ℝ) (31841386547159 / 20000000000000000 : ℝ) (64261360607057 / 2000000000000000 : ℝ)
    (cell13193 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · have h := gap_lower (n := 13193) (a := (83617188689683 / 100000000000000 : ℝ)) (b := (39014692467 / 25000000000000 : ℝ)) (q := (548603382479 / 25000000000000 : ℝ))
      (E := (cell13193 ⟨13, by decide⟩).energy) (xi := (64261360607057 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13193 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13193]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13193])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13193) (a := (83617188689683 / 100000000000000 : ℝ)) (b := (39014692467 / 25000000000000 : ℝ)) (q := (548603382479 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13193])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13193])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13193]

theorem cert13193_14 : CellCertificate 13193 (34936471689749 / 400000000000000 : ℝ) (31841386547159 / 20000000000000000 : ℝ) (64261360607057 / 2000000000000000 : ℝ)
    (cell13193 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · have h := gap_lower (n := 13193) (a := (83582620232149 / 100000000000000 : ℝ)) (b := (39014692467 / 25000000000000 : ℝ)) (q := (548604377291 / 25000000000000 : ℝ))
      (E := (cell13193 ⟨14, by decide⟩).energy) (xi := (64261360607057 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13193 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13193]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13193])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13193) (a := (83582620232149 / 100000000000000 : ℝ)) (b := (39014692467 / 25000000000000 : ℝ)) (q := (548604377291 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13193])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13193])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13193]

theorem cert13193_15 : CellCertificate 13193 (34936471689749 / 400000000000000 : ℝ) (31841386547159 / 20000000000000000 : ℝ) (64261360607057 / 2000000000000000 : ℝ)
    (cell13193 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · have h := gap_lower (n := 13193) (a := (16709615226109 / 20000000000000 : ℝ)) (b := (39014692467 / 25000000000000 : ℝ)) (q := (87776861007 / 4000000000000 : ℝ))
      (E := (cell13193 ⟨15, by decide⟩).energy) (xi := (64261360607057 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13193 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13193]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13193])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13193) (a := (16709615226109 / 20000000000000 : ℝ)) (b := (39014692467 / 25000000000000 : ℝ)) (q := (87776861007 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13193])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13193])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13193]

theorem cert13193_16 : CellCertificate 13193 (34936471689749 / 400000000000000 : ℝ) (31841386547159 / 20000000000000000 : ℝ) (64261360607057 / 2000000000000000 : ℝ)
    (cell13193 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · have h := gap_lower (n := 13193) (a := (83513556351023 / 100000000000000 : ℝ)) (b := (39014692467 / 25000000000000 : ℝ)) (q := (2194425524771 / 100000000000000 : ℝ))
      (E := (cell13193 ⟨16, by decide⟩).energy) (xi := (64261360607057 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13193 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13193]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13193])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13193) (a := (83513556351023 / 100000000000000 : ℝ)) (b := (39014692467 / 25000000000000 : ℝ)) (q := (2194425524771 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13193])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13193])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13193]

theorem cert13193_17 : CellCertificate 13193 (34936471689749 / 400000000000000 : ℝ) (31841386547159 / 20000000000000000 : ℝ) (64261360607057 / 2000000000000000 : ℝ)
    (cell13193 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · have h := gap_lower (n := 13193) (a := (20869765214977 / 25000000000000 : ℝ)) (b := (39014692467 / 25000000000000 : ℝ)) (q := (43888591419 / 2000000000000 : ℝ))
      (E := (cell13193 ⟨17, by decide⟩).energy) (xi := (64261360607057 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13193 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13193]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13193])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13193) (a := (20869765214977 / 25000000000000 : ℝ)) (b := (39014692467 / 25000000000000 : ℝ)) (q := (43888591419 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13193])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13193])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13193]

theorem cert13193_18 : CellCertificate 13193 (34936471689749 / 400000000000000 : ℝ) (31841386547159 / 20000000000000000 : ℝ) (64261360607057 / 2000000000000000 : ℝ)
    (cell13193 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · have h := gap_lower (n := 13193) (a := (834445896237 / 1000000000000 : ℝ)) (b := (39014692467 / 25000000000000 : ℝ)) (q := (1097216805003 / 50000000000000 : ℝ))
      (E := (cell13193 ⟨18, by decide⟩).energy) (xi := (64261360607057 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13193 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13193]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13193])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13193) (a := (834445896237 / 1000000000000 : ℝ)) (b := (39014692467 / 25000000000000 : ℝ)) (q := (1097216805003 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13193])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13193])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13193]

theorem cert13193_19 : CellCertificate 13193 (34936471689749 / 400000000000000 : ℝ) (31841386547159 / 20000000000000000 : ℝ) (64261360607057 / 2000000000000000 : ℝ)
    (cell13193 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · have h := gap_lower (n := 13193) (a := (8341014260907 / 10000000000000 : ℝ)) (b := (39014692467 / 25000000000000 : ℝ)) (q := (1097218793949 / 50000000000000 : ℝ))
      (E := (cell13193 ⟨19, by decide⟩).energy) (xi := (64261360607057 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13193 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13193]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13193])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13193) (a := (8341014260907 / 10000000000000 : ℝ)) (b := (39014692467 / 25000000000000 : ℝ)) (q := (1097218793949 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13193])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13193])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13193]

theorem cert13194_0 : CellCertificate 13194 (436692912020237 / 5000000000000000 : ℝ) (63677944920327 / 40000000000000000 : ℝ) (321281897540049 / 10000000000000000 : ℝ)
    (cell13194 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · have h := gap_lower (n := 13194) (a := (84068796737229 / 100000000000000 : ℝ)) (b := (156046807561 / 100000000000000 : ℝ)) (q := (438850239411 / 20000000000000 : ℝ))
      (E := (cell13194 ⟨0, by decide⟩).energy) (xi := (321281897540049 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13194 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13194]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13194])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13194) (a := (84068796737229 / 100000000000000 : ℝ)) (b := (156046807561 / 100000000000000 : ℝ)) (q := (438850239411 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13194])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13194])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13194]

theorem cert13194_1 : CellCertificate 13194 (436692912020237 / 5000000000000000 : ℝ) (63677944920327 / 40000000000000000 : ℝ) (321281897540049 / 10000000000000000 : ℝ)
    (cell13194 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · have h := gap_lower (n := 13194) (a := (42016954248391 / 50000000000000 : ℝ)) (b := (156046807561 / 100000000000000 : ℝ)) (q := (2194255208921 / 100000000000000 : ℝ))
      (E := (cell13194 ⟨1, by decide⟩).energy) (xi := (321281897540049 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13194 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13194]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13194])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13194) (a := (42016954248391 / 50000000000000 : ℝ)) (b := (156046807561 / 100000000000000 : ℝ)) (q := (2194255208921 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13194])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13194])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13194]

theorem cert13194_2 : CellCertificate 13194 (436692912020237 / 5000000000000000 : ℝ) (63677944920327 / 40000000000000000 : ℝ) (321281897540049 / 10000000000000000 : ℝ)
    (cell13194 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · have h := gap_lower (n := 13194) (a := (83999045068757 / 100000000000000 : ℝ)) (b := (156046807561 / 100000000000000 : ℝ)) (q := (2194259227207 / 100000000000000 : ℝ))
      (E := (cell13194 ⟨2, by decide⟩).energy) (xi := (321281897540049 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13194 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13194]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13194])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13194) (a := (83999045068757 / 100000000000000 : ℝ)) (b := (156046807561 / 100000000000000 : ℝ)) (q := (2194259227207 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13194])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13194])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13194]

theorem cert13194_3 : CellCertificate 13194 (436692912020237 / 5000000000000000 : ℝ) (63677944920327 / 40000000000000000 : ℝ) (321281897540049 / 10000000000000000 : ℝ)
    (cell13194 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · have h := gap_lower (n := 13194) (a := (20991051604231 / 25000000000000 : ℝ)) (b := (156046807561 / 100000000000000 : ℝ)) (q := (2194263202359 / 100000000000000 : ℝ))
      (E := (cell13194 ⟨3, by decide⟩).energy) (xi := (321281897540049 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13194 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13194]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13194])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13194) (a := (20991051604231 / 25000000000000 : ℝ)) (b := (156046807561 / 100000000000000 : ℝ)) (q := (2194263202359 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13194])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13194])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13194]

theorem cert13194_4 : CellCertificate 13194 (436692912020237 / 5000000000000000 : ℝ) (63677944920327 / 40000000000000000 : ℝ) (321281897540049 / 10000000000000000 : ℝ)
    (cell13194 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · have h := gap_lower (n := 13194) (a := (41964696252621 / 50000000000000 : ℝ)) (b := (156046807561 / 100000000000000 : ℝ)) (q := (87770690333 / 4000000000000 : ℝ))
      (E := (cell13194 ⟨4, by decide⟩).energy) (xi := (321281897540049 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13194 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13194]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13194])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13194) (a := (41964696252621 / 50000000000000 : ℝ)) (b := (156046807561 / 100000000000000 : ℝ)) (q := (87770690333 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13194])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13194])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13194]

theorem cert13194_5 : CellCertificate 13194 (436692912020237 / 5000000000000000 : ℝ) (63677944920327 / 40000000000000000 : ℝ) (321281897540049 / 10000000000000000 : ℝ)
    (cell13194 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · have h := gap_lower (n := 13194) (a := (83894603297859 / 100000000000000 : ℝ)) (b := (156046807561 / 100000000000000 : ℝ)) (q := (137141955443 / 6250000000000 : ℝ))
      (E := (cell13194 ⟨5, by decide⟩).energy) (xi := (321281897540049 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13194 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13194]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13194])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13194) (a := (83894603297859 / 100000000000000 : ℝ)) (b := (156046807561 / 100000000000000 : ℝ)) (q := (137141955443 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13194])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13194])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13194]

theorem cert13194_6 : CellCertificate 13194 (436692912020237 / 5000000000000000 : ℝ) (63677944920327 / 40000000000000000 : ℝ) (321281897540049 / 10000000000000000 : ℝ)
    (cell13194 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · have h := gap_lower (n := 13194) (a := (10482479844889 / 12500000000000 : ℝ)) (b := (156046807561 / 100000000000000 : ℝ)) (q := (438855059237 / 20000000000000 : ℝ))
      (E := (cell13194 ⟨6, by decide⟩).energy) (xi := (321281897540049 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13194 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13194]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13194])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13194) (a := (10482479844889 / 12500000000000 : ℝ)) (b := (156046807561 / 100000000000000 : ℝ)) (q := (438855059237 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13194])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13194])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13194]

theorem cert13194_7 : CellCertificate 13194 (436692912020237 / 5000000000000000 : ℝ) (63677944920327 / 40000000000000000 : ℝ) (321281897540049 / 10000000000000000 : ℝ)
    (cell13194 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · have h := gap_lower (n := 13194) (a := (3353003954141 / 4000000000000 : ℝ)) (b := (156046807561 / 100000000000000 : ℝ)) (q := (2194279292899 / 100000000000000 : ℝ))
      (E := (cell13194 ⟨7, by decide⟩).energy) (xi := (321281897540049 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13194 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13194]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13194])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13194) (a := (3353003954141 / 4000000000000 : ℝ)) (b := (156046807561 / 100000000000000 : ℝ)) (q := (2194279292899 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13194])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13194])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13194]

theorem cert13194_8 : CellCertificate 13194 (436692912020237 / 5000000000000000 : ℝ) (63677944920327 / 40000000000000000 : ℝ) (321281897540049 / 10000000000000000 : ℝ)
    (cell13194 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · have h := gap_lower (n := 13194) (a := (41895191772903 / 50000000000000 : ℝ)) (b := (156046807561 / 100000000000000 : ℝ)) (q := (2194283284261 / 100000000000000 : ℝ))
      (E := (cell13194 ⟨8, by decide⟩).energy) (xi := (321281897540049 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13194 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13194]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13194])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13194) (a := (41895191772903 / 50000000000000 : ℝ)) (b := (156046807561 / 100000000000000 : ℝ)) (q := (2194283284261 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13194])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13194])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13194]

theorem cert13194_9 : CellCertificate 13194 (436692912020237 / 5000000000000000 : ℝ) (63677944920327 / 40000000000000000 : ℝ) (321281897540049 / 10000000000000000 : ℝ)
    (cell13194 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · have h := gap_lower (n := 13194) (a := (83755692800849 / 100000000000000 : ℝ)) (b := (156046807561 / 100000000000000 : ℝ)) (q := (27428591689 / 1250000000000 : ℝ))
      (E := (cell13194 ⟨9, by decide⟩).energy) (xi := (321281897540049 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13194 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13194]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13194])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13194) (a := (83755692800849 / 100000000000000 : ℝ)) (b := (156046807561 / 100000000000000 : ℝ)) (q := (27428591689 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13194])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13194])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13194]

theorem cert13194_10 : CellCertificate 13194 (436692912020237 / 5000000000000000 : ℝ) (63677944920327 / 40000000000000000 : ℝ) (321281897540049 / 10000000000000000 : ℝ)
    (cell13194 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · have h := gap_lower (n := 13194) (a := (83721026583729 / 100000000000000 : ℝ)) (b := (156046807561 / 100000000000000 : ℝ)) (q := (1097145667947 / 50000000000000 : ℝ))
      (E := (cell13194 ⟨10, by decide⟩).energy) (xi := (321281897540049 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13194 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13194]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13194])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13194) (a := (83721026583729 / 100000000000000 : ℝ)) (b := (156046807561 / 100000000000000 : ℝ)) (q := (1097145667947 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13194])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13194])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13194]

theorem cert13194_11 : CellCertificate 13194 (436692912020237 / 5000000000000000 : ℝ) (63677944920327 / 40000000000000000 : ℝ) (321281897540049 / 10000000000000000 : ℝ)
    (cell13194 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · have h := gap_lower (n := 13194) (a := (41843192429853 / 50000000000000 : ℝ)) (b := (156046807561 / 100000000000000 : ℝ)) (q := (548573837727 / 25000000000000 : ℝ))
      (E := (cell13194 ⟨11, by decide⟩).energy) (xi := (321281897540049 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13194 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13194]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13194])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13194) (a := (41843192429853 / 50000000000000 : ℝ)) (b := (156046807561 / 100000000000000 : ℝ)) (q := (548573837727 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13194])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13194])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13194]

theorem cert13194_12 : CellCertificate 13194 (436692912020237 / 5000000000000000 : ℝ) (63677944920327 / 40000000000000000 : ℝ) (321281897540049 / 10000000000000000 : ℝ)
    (cell13194 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · have h := gap_lower (n := 13194) (a := (41825883797109 / 50000000000000 : ℝ)) (b := (156046807561 / 100000000000000 : ℝ)) (q := (2194299386197 / 100000000000000 : ℝ))
      (E := (cell13194 ⟨12, by decide⟩).energy) (xi := (321281897540049 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13194 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13194]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13194])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13194) (a := (41825883797109 / 50000000000000 : ℝ)) (b := (156046807561 / 100000000000000 : ℝ)) (q := (2194299386197 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13194])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13194])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13194]

theorem cert13194_13 : CellCertificate 13194 (436692912020237 / 5000000000000000 : ℝ) (63677944920327 / 40000000000000000 : ℝ) (321281897540049 / 10000000000000000 : ℝ)
    (cell13194 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · have h := gap_lower (n := 13194) (a := (20904293688221 / 25000000000000 : ℝ)) (b := (156046807561 / 100000000000000 : ℝ)) (q := (2194303389387 / 100000000000000 : ℝ))
      (E := (cell13194 ⟨13, by decide⟩).energy) (xi := (321281897540049 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13194 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13194]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13194])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13194) (a := (20904293688221 / 25000000000000 : ℝ)) (b := (156046807561 / 100000000000000 : ℝ)) (q := (2194303389387 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13194])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13194])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13194]

theorem cert13194_14 : CellCertificate 13194 (436692912020237 / 5000000000000000 : ℝ) (63677944920327 / 40000000000000000 : ℝ) (321281897540049 / 10000000000000000 : ℝ)
    (cell13194 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · have h := gap_lower (n := 13194) (a := (83582606301501 / 100000000000000 : ℝ)) (b := (156046807561 / 100000000000000 : ℝ)) (q := (438861484827 / 20000000000000 : ℝ))
      (E := (cell13194 ⟨14, by decide⟩).energy) (xi := (321281897540049 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13194 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13194]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13194])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13194) (a := (83582606301501 / 100000000000000 : ℝ)) (b := (156046807561 / 100000000000000 : ℝ)) (q := (438861484827 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13194])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13194])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13194]

theorem cert13194_15 : CellCertificate 13194 (436692912020237 / 5000000000000000 : ℝ) (63677944920327 / 40000000000000000 : ℝ) (321281897540049 / 10000000000000000 : ℝ)
    (cell13194 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · have h := gap_lower (n := 13194) (a := (83548062206043 / 100000000000000 : ℝ)) (b := (156046807561 / 100000000000000 : ℝ)) (q := (2194311437531 / 100000000000000 : ℝ))
      (E := (cell13194 ⟨15, by decide⟩).energy) (xi := (321281897540049 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13194 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13194]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13194])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13194) (a := (83548062206043 / 100000000000000 : ℝ)) (b := (156046807561 / 100000000000000 : ℝ)) (q := (2194311437531 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13194])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13194])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13194]

theorem cert13194_16 : CellCertificate 13194 (436692912020237 / 5000000000000000 : ℝ) (63677944920327 / 40000000000000000 : ℝ) (321281897540049 / 10000000000000000 : ℝ)
    (cell13194 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · have h := gap_lower (n := 13194) (a := (41756771216331 / 50000000000000 : ℝ)) (b := (156046807561 / 100000000000000 : ℝ)) (q := (1097157717279 / 50000000000000 : ℝ))
      (E := (cell13194 ⟨16, by decide⟩).energy) (xi := (321281897540049 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13194 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13194]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13194])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13194) (a := (41756771216331 / 50000000000000 : ℝ)) (b := (156046807561 / 100000000000000 : ℝ)) (q := (1097157717279 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13194])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13194])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13194]

theorem cert13194_17 : CellCertificate 13194 (436692912020237 / 5000000000000000 : ℝ) (63677944920327 / 40000000000000000 : ℝ) (321281897540049 / 10000000000000000 : ℝ)
    (cell13194 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · have h := gap_lower (n := 13194) (a := (41739523473841 / 50000000000000 : ℝ)) (b := (156046807561 / 100000000000000 : ℝ)) (q := (2194319419961 / 100000000000000 : ℝ))
      (E := (cell13194 ⟨17, by decide⟩).energy) (xi := (321281897540049 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13194 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13194]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13194])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13194) (a := (41739523473841 / 50000000000000 : ℝ)) (b := (156046807561 / 100000000000000 : ℝ)) (q := (2194319419961 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13194])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13194])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13194]

theorem cert13194_18 : CellCertificate 13194 (436692912020237 / 5000000000000000 : ℝ) (63677944920327 / 40000000000000000 : ℝ) (321281897540049 / 10000000000000000 : ℝ)
    (cell13194 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · have h := gap_lower (n := 13194) (a := (83444575717603 / 100000000000000 : ℝ)) (b := (156046807561 / 100000000000000 : ℝ)) (q := (2194323456519 / 100000000000000 : ℝ))
      (E := (cell13194 ⟨18, by decide⟩).energy) (xi := (321281897540049 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13194 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13194]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13194])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13194) (a := (83444575717603 / 100000000000000 : ℝ)) (b := (156046807561 / 100000000000000 : ℝ)) (q := (2194323456519 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13194])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13194])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13194]

theorem cert13194_19 : CellCertificate 13194 (436692912020237 / 5000000000000000 : ℝ) (63677944920327 / 40000000000000000 : ℝ) (321281897540049 / 10000000000000000 : ℝ)
    (cell13194 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · have h := gap_lower (n := 13194) (a := (41705064354549 / 50000000000000 : ℝ)) (b := (156046807561 / 100000000000000 : ℝ)) (q := (2194327490261 / 100000000000000 : ℝ))
      (E := (cell13194 ⟨19, by decide⟩).energy) (xi := (321281897540049 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13194 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13194]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13194])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13194) (a := (41705064354549 / 50000000000000 : ℝ)) (b := (156046807561 / 100000000000000 : ℝ)) (q := (2194327490261 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13194])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13194])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13194]

theorem cert13195_0 : CellCertificate 13195 (873359859602341 / 10000000000000000 : ℝ) (1591827936959657 / 1000000000000000000 : ℝ) (16062849796459 / 500000000000000 : ℝ)
    (cell13195 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · have h := gap_lower (n := 13195) (a := (16813756544419 / 20000000000000 : ℝ)) (b := (156034847093 / 100000000000000 : ℝ)) (q := (2194141091513 / 100000000000000 : ℝ))
      (E := (cell13195 ⟨0, by decide⟩).energy) (xi := (16062849796459 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13195 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13195]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13195])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13195) (a := (16813756544419 / 20000000000000 : ℝ)) (b := (156034847093 / 100000000000000 : ℝ)) (q := (2194141091513 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13195])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13195])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13195]

theorem cert13195_1 : CellCertificate 13195 (873359859602341 / 10000000000000000 : ℝ) (1591827936959657 / 1000000000000000000 : ℝ) (16062849796459 / 500000000000000 : ℝ)
    (cell13195 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · have h := gap_lower (n := 13195) (a := (8403389448787 / 10000000000000 : ℝ)) (b := (156034847093 / 100000000000000 : ℝ)) (q := (438829020017 / 20000000000000 : ℝ))
      (E := (cell13195 ⟨1, by decide⟩).energy) (xi := (16062849796459 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13195 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13195]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13195])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13195) (a := (8403389448787 / 10000000000000 : ℝ)) (b := (156034847093 / 100000000000000 : ℝ)) (q := (438829020017 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13195])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13195])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13195]

theorem cert13195_2 : CellCertificate 13195 (873359859602341 / 10000000000000000 : ℝ) (1591827936959657 / 1000000000000000000 : ℝ) (16062849796459 / 500000000000000 : ℝ)
    (cell13195 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · have h := gap_lower (n := 13195) (a := (83999031066061 / 100000000000000 : ℝ)) (b := (156034847093 / 100000000000000 : ℝ)) (q := (17553192921 / 800000000000 : ℝ))
      (E := (cell13195 ⟨2, by decide⟩).energy) (xi := (16062849796459 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13195 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13195]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13195])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13195) (a := (83999031066061 / 100000000000000 : ℝ)) (b := (156034847093 / 100000000000000 : ℝ)) (q := (17553192921 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13195])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13195])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13195]

theorem cert13195_3 : CellCertificate 13195 (873359859602341 / 10000000000000000 : ℝ) (1591827936959657 / 1000000000000000000 : ℝ) (16062849796459 / 500000000000000 : ℝ)
    (cell13195 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · have h := gap_lower (n := 13195) (a := (41982096210219 / 50000000000000 : ℝ)) (b := (156034847093 / 100000000000000 : ℝ)) (q := (438830629001 / 20000000000000 : ℝ))
      (E := (cell13195 ⟨3, by decide⟩).energy) (xi := (16062849796459 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13195 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13195]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13195])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13195) (a := (41982096210219 / 50000000000000 : ℝ)) (b := (156034847093 / 100000000000000 : ℝ)) (q := (438830629001 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13195])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13195])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13195]

theorem cert13195_4 : CellCertificate 13195 (873359859602341 / 10000000000000000 : ℝ) (1591827936959657 / 1000000000000000000 : ℝ) (16062849796459 / 500000000000000 : ℝ)
    (cell13195 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · have h := gap_lower (n := 13195) (a := (83929378514961 / 100000000000000 : ℝ)) (b := (156034847093 / 100000000000000 : ℝ)) (q := (219415713989 / 10000000000000 : ℝ))
      (E := (cell13195 ⟨4, by decide⟩).energy) (xi := (16062849796459 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13195 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13195]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13195])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13195) (a := (83929378514961 / 100000000000000 : ℝ)) (b := (156034847093 / 100000000000000 : ℝ)) (q := (219415713989 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13195])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13195])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13195]

theorem cert13195_5 : CellCertificate 13195 (873359859602341 / 10000000000000000 : ℝ) (1591827936959657 / 1000000000000000000 : ℝ) (16062849796459 / 500000000000000 : ℝ)
    (cell13195 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · have h := gap_lower (n := 13195) (a := (41947294656889 / 50000000000000 : ℝ)) (b := (156034847093 / 100000000000000 : ℝ)) (q := (2194161165547 / 100000000000000 : ℝ))
      (E := (cell13195 ⟨5, by decide⟩).energy) (xi := (16062849796459 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13195 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13195]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13195])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13195) (a := (41947294656889 / 50000000000000 : ℝ)) (b := (156034847093 / 100000000000000 : ℝ)) (q := (2194161165547 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13195])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13195])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13195]

theorem cert13195_6 : CellCertificate 13195 (873359859602341 / 10000000000000000 : ℝ) (1591827936959657 / 1000000000000000000 : ℝ) (16062849796459 / 500000000000000 : ℝ)
    (cell13195 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · have h := gap_lower (n := 13195) (a := (3354392991249 / 4000000000000 : ℝ)) (b := (156034847093 / 100000000000000 : ℝ)) (q := (438833034317 / 20000000000000 : ℝ))
      (E := (cell13195 ⟨6, by decide⟩).energy) (xi := (16062849796459 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13195 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13195]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13195])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13195) (a := (3354392991249 / 4000000000000 : ℝ)) (b := (156034847093 / 100000000000000 : ℝ)) (q := (438833034317 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13195])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13195])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13195]

theorem cert13195_7 : CellCertificate 13195 (873359859602341 / 10000000000000000 : ℝ) (1591827936959657 / 1000000000000000000 : ℝ) (16062849796459 / 500000000000000 : ℝ)
    (cell13195 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · have h := gap_lower (n := 13195) (a := (41912542440913 / 50000000000000 : ℝ)) (b := (156034847093 / 100000000000000 : ℝ)) (q := (2194169165287 / 100000000000000 : ℝ))
      (E := (cell13195 ⟨7, by decide⟩).energy) (xi := (16062849796459 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13195 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13195]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13195])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13195) (a := (41912542440913 / 50000000000000 : ℝ)) (b := (156034847093 / 100000000000000 : ℝ)) (q := (2194169165287 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13195])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13195])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13195]

theorem cert13195_8 : CellCertificate 13195 (873359859602341 / 10000000000000000 : ℝ) (1591827936959657 / 1000000000000000000 : ℝ) (16062849796459 / 500000000000000 : ℝ)
    (cell13195 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · have h := gap_lower (n := 13195) (a := (8379036958029 / 10000000000000 : ℝ)) (b := (156034847093 / 100000000000000 : ℝ)) (q := (2194173211729 / 100000000000000 : ℝ))
      (E := (cell13195 ⟨8, by decide⟩).energy) (xi := (16062849796459 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13195 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13195]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13195])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13195) (a := (8379036958029 / 10000000000000 : ℝ)) (b := (156034847093 / 100000000000000 : ℝ)) (q := (2194173211729 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13195])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13195])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13195]

theorem cert13195_9 : CellCertificate 13195 (873359859602341 / 10000000000000000 : ℝ) (1591827936959657 / 1000000000000000000 : ℝ) (16062849796459 / 500000000000000 : ℝ)
    (cell13195 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · have h := gap_lower (n := 13195) (a := (8375567884151 / 10000000000000 : ℝ)) (b := (156034847093 / 100000000000000 : ℝ)) (q := (17553417613 / 800000000000 : ℝ))
      (E := (cell13195 ⟨9, by decide⟩).energy) (xi := (16062849796459 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13195 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13195]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13195])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13195) (a := (8375567884151 / 10000000000000 : ℝ)) (b := (156034847093 / 100000000000000 : ℝ)) (q := (17553417613 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13195])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13195])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13195]

theorem cert13195_10 : CellCertificate 13195 (873359859602341 / 10000000000000000 : ℝ) (1591827936959657 / 1000000000000000000 : ℝ) (16062849796459 / 500000000000000 : ℝ)
    (cell13195 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · have h := gap_lower (n := 13195) (a := (41860506315281 / 50000000000000 : ℝ)) (b := (156034847093 / 100000000000000 : ℝ)) (q := (2194181257619 / 100000000000000 : ℝ))
      (E := (cell13195 ⟨10, by decide⟩).energy) (xi := (16062849796459 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13195 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13195]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13195])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13195) (a := (41860506315281 / 50000000000000 : ℝ)) (b := (156034847093 / 100000000000000 : ℝ)) (q := (2194181257619 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13195])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13195])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13195]

theorem cert13195_11 : CellCertificate 13195 (873359859602341 / 10000000000000000 : ℝ) (1591827936959657 / 1000000000000000000 : ℝ) (16062849796459 / 500000000000000 : ℝ)
    (cell13195 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · have h := gap_lower (n := 13195) (a := (41843185456353 / 50000000000000 : ℝ)) (b := (156034847093 / 100000000000000 : ℝ)) (q := (274273158729 / 12500000000000 : ℝ))
      (E := (cell13195 ⟨11, by decide⟩).energy) (xi := (16062849796459 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13195 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13195]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13195])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13195) (a := (41843185456353 / 50000000000000 : ℝ)) (b := (156034847093 / 100000000000000 : ℝ)) (q := (274273158729 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13195])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13195])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13195]

theorem cert13195_12 : CellCertificate 13195 (873359859602341 / 10000000000000000 : ℝ) (1591827936959657 / 1000000000000000000 : ℝ) (16062849796459 / 500000000000000 : ℝ)
    (cell13195 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · have h := gap_lower (n := 13195) (a := (83651753653379 / 100000000000000 : ℝ)) (b := (156034847093 / 100000000000000 : ℝ)) (q := (548547311057 / 25000000000000 : ℝ))
      (E := (cell13195 ⟨12, by decide⟩).energy) (xi := (16062849796459 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13195 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13195]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13195])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13195) (a := (83651753653379 / 100000000000000 : ℝ)) (b := (156034847093 / 100000000000000 : ℝ)) (q := (548547311057 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13195])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13195])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13195]

theorem cert13195_13 : CellCertificate 13195 (873359859602341 / 10000000000000000 : ℝ) (1591827936959657 / 1000000000000000000 : ℝ) (16062849796459 / 500000000000000 : ℝ)
    (cell13195 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · have h := gap_lower (n := 13195) (a := (418085804091 / 500000000000 : ℝ)) (b := (156034847093 / 100000000000000 : ℝ)) (q := (43883866057 / 2000000000000 : ℝ))
      (E := (cell13195 ⟨13, by decide⟩).energy) (xi := (16062849796459 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13195 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13195]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13195])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13195) (a := (418085804091 / 500000000000 : ℝ)) (b := (156034847093 / 100000000000000 : ℝ)) (q := (43883866057 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13195])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13195])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13195]

theorem cert13195_14 : CellCertificate 13195 (873359859602341 / 10000000000000000 : ℝ) (1591827936959657 / 1000000000000000000 : ℝ) (16062849796459 / 500000000000000 : ℝ)
    (cell13195 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · have h := gap_lower (n := 13195) (a := (83582592372967 / 100000000000000 : ℝ)) (b := (156034847093 / 100000000000000 : ℝ)) (q := (137137329797 / 6250000000000 : ℝ))
      (E := (cell13195 ⟨14, by decide⟩).energy) (xi := (16062849796459 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13195 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13195]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13195])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13195) (a := (83582592372967 / 100000000000000 : ℝ)) (b := (156034847093 / 100000000000000 : ℝ)) (q := (137137329797 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13195])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13195])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13195]

theorem cert13195_15 : CellCertificate 13195 (873359859602341 / 10000000000000000 : ℝ) (1591827936959657 / 1000000000000000000 : ℝ) (16062849796459 / 500000000000000 : ℝ)
    (cell13195 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · have h := gap_lower (n := 13195) (a := (16709609656731 / 20000000000000 : ℝ)) (b := (156034847093 / 100000000000000 : ℝ)) (q := (219420128751 / 10000000000000 : ℝ))
      (E := (cell13195 ⟨15, by decide⟩).energy) (xi := (16062849796459 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13195 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13195]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13195])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13195) (a := (16709609656731 / 20000000000000 : ℝ)) (b := (156034847093 / 100000000000000 : ℝ)) (q := (219420128751 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13195])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13195])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13195]

theorem cert13195_16 : CellCertificate 13195 (873359859602341 / 10000000000000000 : ℝ) (1591827936959657 / 1000000000000000000 : ℝ) (16062849796459 / 500000000000000 : ℝ)
    (cell13195 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · have h := gap_lower (n := 13195) (a := (20878382129103 / 25000000000000 : ℝ)) (b := (156034847093 / 100000000000000 : ℝ)) (q := (109710267009 / 5000000000000 : ℝ))
      (E := (cell13195 ⟨16, by decide⟩).energy) (xi := (16062849796459 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13195 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13195]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13195])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13195) (a := (20878382129103 / 25000000000000 : ℝ)) (b := (156034847093 / 100000000000000 : ℝ)) (q := (109710267009 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13195])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13195])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13195]

theorem cert13195_17 : CellCertificate 13195 (873359859602341 / 10000000000000000 : ℝ) (1591827936959657 / 1000000000000000000 : ℝ) (16062849796459 / 500000000000000 : ℝ)
    (cell13195 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · have h := gap_lower (n := 13195) (a := (41739516518783 / 50000000000000 : ℝ)) (b := (156034847093 / 100000000000000 : ℝ)) (q := (2194209323063 / 100000000000000 : ℝ))
      (E := (cell13195 ⟨17, by decide⟩).energy) (xi := (16062849796459 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13195 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13195]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13195])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13195) (a := (41739516518783 / 50000000000000 : ℝ)) (b := (156034847093 / 100000000000000 : ℝ)) (q := (2194209323063 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13195])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13195])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13195]

theorem cert13195_18 : CellCertificate 13195 (873359859602341 / 10000000000000000 : ℝ) (1591827936959657 / 1000000000000000000 : ℝ) (16062849796459 / 500000000000000 : ℝ)
    (cell13195 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · have h := gap_lower (n := 13195) (a := (5215285113351 / 6250000000000 : ℝ)) (b := (156034847093 / 100000000000000 : ℝ)) (q := (1097106678573 / 50000000000000 : ℝ))
      (E := (cell13195 ⟨18, by decide⟩).energy) (xi := (16062849796459 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13195 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13195]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13195])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13195) (a := (5215285113351 / 6250000000000 : ℝ)) (b := (156034847093 / 100000000000000 : ℝ)) (q := (1097106678573 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13195])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13195])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13195]

theorem cert13195_19 : CellCertificate 13195 (873359859602341 / 10000000000000000 : ℝ) (1591827936959657 / 1000000000000000000 : ℝ) (16062849796459 / 500000000000000 : ℝ)
    (cell13195 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · have h := gap_lower (n := 13195) (a := (41705057405617 / 50000000000000 : ℝ)) (b := (156034847093 / 100000000000000 : ℝ)) (q := (1097108694231 / 50000000000000 : ℝ))
      (E := (cell13195 ⟨19, by decide⟩).energy) (xi := (16062849796459 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13195 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13195]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13195])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13195) (a := (41705057405617 / 50000000000000 : ℝ)) (b := (156034847093 / 100000000000000 : ℝ)) (q := (1097108694231 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13195])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13195])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13195]

theorem cert13196_0 : CellCertificate 13196 (436666949464233 / 5000000000000000 : ℝ) (795853634604117 / 500000000000000000 : ℝ) (160616049100861 / 5000000000000000 : ℝ)
    (cell13196 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · have h := gap_lower (n := 13196) (a := (2627149022159 / 3125000000000 : ℝ)) (b := (31204577693 / 20000000000000 : ℝ)) (q := (219403098179 / 10000000000000 : ℝ))
      (E := (cell13196 ⟨0, by decide⟩).energy) (xi := (160616049100861 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13196 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13196]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13196])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13196) (a := (2627149022159 / 3125000000000 : ℝ)) (b := (31204577693 / 20000000000000 : ℝ)) (q := (219403098179 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13196])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13196])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13196]

theorem cert13196_1 : CellCertificate 13196 (436666949464233 / 5000000000000000 : ℝ) (795853634604117 / 500000000000000000 : ℝ) (160616049100861 / 5000000000000000 : ℝ)
    (cell13196 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · have h := gap_lower (n := 13196) (a := (84033880481083 / 100000000000000 : ℝ)) (b := (31204577693 / 20000000000000 : ℝ)) (q := (219403498707 / 10000000000000 : ℝ))
      (E := (cell13196 ⟨1, by decide⟩).energy) (xi := (160616049100861 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13196 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13196]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13196])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13196) (a := (84033880481083 / 100000000000000 : ℝ)) (b := (31204577693 / 20000000000000 : ℝ)) (q := (219403498707 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13196])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13196])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13196]

theorem cert13196_2 : CellCertificate 13196 (436666949464233 / 5000000000000000 : ℝ) (795853634604117 / 500000000000000000 : ℝ) (160616049100861 / 5000000000000000 : ℝ)
    (cell13196 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · have h := gap_lower (n := 13196) (a := (8399901706549 / 10000000000000 : ℝ)) (b := (31204577693 / 20000000000000 : ℝ)) (q := (2194038998863 / 100000000000000 : ℝ))
      (E := (cell13196 ⟨2, by decide⟩).energy) (xi := (160616049100861 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13196 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13196]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13196])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13196) (a := (8399901706549 / 10000000000000 : ℝ)) (b := (31204577693 / 20000000000000 : ℝ)) (q := (2194038998863 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13196])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13196])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13196]

theorem cert13196_3 : CellCertificate 13196 (436666949464233 / 5000000000000000 : ℝ) (795853634604117 / 500000000000000000 : ℝ) (160616049100861 / 5000000000000000 : ℝ)
    (cell13196 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · have h := gap_lower (n := 13196) (a := (83964178426077 / 100000000000000 : ℝ)) (b := (31204577693 / 20000000000000 : ℝ)) (q := (2194043025543 / 100000000000000 : ℝ))
      (E := (cell13196 ⟨3, by decide⟩).energy) (xi := (160616049100861 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13196 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13196]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13196])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13196) (a := (83964178426077 / 100000000000000 : ℝ)) (b := (31204577693 / 20000000000000 : ℝ)) (q := (2194043025543 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13196])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13196])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13196]

theorem cert13196_4 : CellCertificate 13196 (436666949464233 / 5000000000000000 : ℝ) (795853634604117 / 500000000000000000 : ℝ) (160616049100861 / 5000000000000000 : ℝ)
    (cell13196 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · have h := gap_lower (n := 13196) (a := (20982341131701 / 25000000000000 : ℝ)) (b := (31204577693 / 20000000000000 : ℝ)) (q := (548511768807 / 25000000000000 : ℝ))
      (E := (cell13196 ⟨4, by decide⟩).energy) (xi := (160616049100861 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13196 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13196]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13196])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13196) (a := (20982341131701 / 25000000000000 : ℝ)) (b := (31204577693 / 20000000000000 : ℝ)) (q := (548511768807 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13196])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13196])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13196]

theorem cert13196_5 : CellCertificate 13196 (436666949464233 / 5000000000000000 : ℝ) (795853634604117 / 500000000000000000 : ℝ) (160616049100861 / 5000000000000000 : ℝ)
    (cell13196 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · have h := gap_lower (n := 13196) (a := (83894575331819 / 100000000000000 : ℝ)) (b := (31204577693 / 20000000000000 : ℝ)) (q := (2194051039829 / 100000000000000 : ℝ))
      (E := (cell13196 ⟨5, by decide⟩).energy) (xi := (160616049100861 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13196 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13196]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13196])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13196) (a := (83894575331819 / 100000000000000 : ℝ)) (b := (31204577693 / 20000000000000 : ℝ)) (q := (2194051039829 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13196])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13196])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13196]

theorem cert13196_6 : CellCertificate 13196 (436666949464233 / 5000000000000000 : ℝ) (795853634604117 / 500000000000000000 : ℝ) (160616049100861 / 5000000000000000 : ℝ)
    (cell13196 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · have h := gap_lower (n := 13196) (a := (83859810805459 / 100000000000000 : ℝ)) (b := (31204577693 / 20000000000000 : ℝ)) (q := (2194055100807 / 100000000000000 : ℝ))
      (E := (cell13196 ⟨6, by decide⟩).energy) (xi := (160616049100861 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13196 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13196]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13196])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13196) (a := (83859810805459 / 100000000000000 : ℝ)) (b := (31204577693 / 20000000000000 : ℝ)) (q := (2194055100807 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13196])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13196])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13196]

theorem cert13196_7 : CellCertificate 13196 (436666949464233 / 5000000000000000 : ℝ) (795853634604117 / 500000000000000000 : ℝ) (160616049100861 / 5000000000000000 : ℝ)
    (cell13196 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · have h := gap_lower (n := 13196) (a := (83825070912247 / 100000000000000 : ℝ)) (b := (31204577693 / 20000000000000 : ℝ)) (q := (1097029545761 / 50000000000000 : ℝ))
      (E := (cell13196 ⟨7, by decide⟩).energy) (xi := (160616049100861 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13196 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13196]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13196])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13196) (a := (83825070912247 / 100000000000000 : ℝ)) (b := (31204577693 / 20000000000000 : ℝ)) (q := (1097029545761 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13196])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13196])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13196]

theorem cert13196_8 : CellCertificate 13196 (436666949464233 / 5000000000000000 : ℝ) (795853634604117 / 500000000000000000 : ℝ) (160616049100861 / 5000000000000000 : ℝ)
    (cell13196 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · have h := gap_lower (n := 13196) (a := (83790355616893 / 100000000000000 : ℝ)) (b := (31204577693 / 20000000000000 : ℝ)) (q := (2194063135023 / 100000000000000 : ℝ))
      (E := (cell13196 ⟨8, by decide⟩).energy) (xi := (160616049100861 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13196 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13196]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13196])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13196) (a := (83790355616893 / 100000000000000 : ℝ)) (b := (31204577693 / 20000000000000 : ℝ)) (q := (2194063135023 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13196])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13196])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13196]

theorem cert13196_9 : CellCertificate 13196 (436666949464233 / 5000000000000000 : ℝ) (795853634604117 / 500000000000000000 : ℝ) (160616049100861 / 5000000000000000 : ℝ)
    (cell13196 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · have h := gap_lower (n := 13196) (a := (8375566488429 / 10000000000000 : ℝ)) (b := (31204577693 / 20000000000000 : ℝ)) (q := (87762684881 / 4000000000000 : ℝ))
      (E := (cell13196 ⟨9, by decide⟩).energy) (xi := (160616049100861 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13196 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13196]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13196])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13196) (a := (8375566488429 / 10000000000000 : ℝ)) (b := (31204577693 / 20000000000000 : ℝ)) (q := (87762684881 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13196])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13196])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13196]

theorem cert13196_10 : CellCertificate 13196 (436666949464233 / 5000000000000000 : ℝ) (795853634604117 / 500000000000000000 : ℝ) (160616049100861 / 5000000000000000 : ℝ)
    (cell13196 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · have h := gap_lower (n := 13196) (a := (83720998679513 / 100000000000000 : ℝ)) (b := (31204577693 / 20000000000000 : ℝ)) (q := (54851777927 / 2500000000000 : ℝ))
      (E := (cell13196 ⟨10, by decide⟩).energy) (xi := (160616049100861 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13196 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13196]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13196])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13196) (a := (83720998679513 / 100000000000000 : ℝ)) (b := (31204577693 / 20000000000000 : ℝ)) (q := (54851777927 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13196])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13196])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13196]

theorem cert13196_11 : CellCertificate 13196 (436666949464233 / 5000000000000000 : ℝ) (795853634604117 / 500000000000000000 : ℝ) (160616049100861 / 5000000000000000 : ℝ)
    (cell13196 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · have h := gap_lower (n := 13196) (a := (41843178483911 / 50000000000000 : ℝ)) (b := (31204577693 / 20000000000000 : ℝ)) (q := (438815036917 / 20000000000000 : ℝ))
      (E := (cell13196 ⟨11, by decide⟩).energy) (xi := (160616049100861 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13196 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13196]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13196])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13196) (a := (41843178483911 / 50000000000000 : ℝ)) (b := (31204577693 / 20000000000000 : ℝ)) (q := (438815036917 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13196])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13196])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13196]

theorem cert13196_12 : CellCertificate 13196 (436666949464233 / 5000000000000000 : ℝ) (795853634604117 / 500000000000000000 : ℝ) (160616049100861 / 5000000000000000 : ℝ)
    (cell13196 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · have h := gap_lower (n := 13196) (a := (16730347942931 / 20000000000000 : ℝ)) (b := (31204577693 / 20000000000000 : ℝ)) (q := (548519789057 / 25000000000000 : ℝ))
      (E := (cell13196 ⟨12, by decide⟩).energy) (xi := (160616049100861 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13196 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13196]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13196])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13196) (a := (16730347942931 / 20000000000000 : ℝ)) (b := (31204577693 / 20000000000000 : ℝ)) (q := (548519789057 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13196])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13196])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13196]

theorem cert13196_13 : CellCertificate 13196 (436666949464233 / 5000000000000000 : ℝ) (795853634604117 / 500000000000000000 : ℝ) (160616049100861 / 5000000000000000 : ℝ)
    (cell13196 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · have h := gap_lower (n := 13196) (a := (83617146885631 / 100000000000000 : ℝ)) (b := (31204577693 / 20000000000000 : ℝ)) (q := (1097041606071 / 50000000000000 : ℝ))
      (E := (cell13196 ⟨13, by decide⟩).energy) (xi := (160616049100861 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13196 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13196]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13196])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13196) (a := (83617146885631 / 100000000000000 : ℝ)) (b := (31204577693 / 20000000000000 : ℝ)) (q := (1097041606071 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13196])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13196])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13196]

theorem cert13196_14 : CellCertificate 13196 (436666949464233 / 5000000000000000 : ℝ) (795853634604117 / 500000000000000000 : ℝ) (160616049100861 / 5000000000000000 : ℝ)
    (cell13196 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · have h := gap_lower (n := 13196) (a := (83582578446547 / 100000000000000 : ℝ)) (b := (31204577693 / 20000000000000 : ℝ)) (q := (438817436677 / 20000000000000 : ℝ))
      (E := (cell13196 ⟨14, by decide⟩).energy) (xi := (160616049100861 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13196 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13196]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13196])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13196) (a := (83582578446547 / 100000000000000 : ℝ)) (b := (31204577693 / 20000000000000 : ℝ)) (q := (438817436677 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13196])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13196])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13196]

theorem cert13196_15 : CellCertificate 13196 (436666949464233 / 5000000000000000 : ℝ) (795853634604117 / 500000000000000000 : ℝ) (160616049100861 / 5000000000000000 : ℝ)
    (cell13196 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · have h := gap_lower (n := 13196) (a := (83548034363379 / 100000000000000 : ℝ)) (b := (31204577693 / 20000000000000 : ℝ)) (q := (1097045624869 / 50000000000000 : ℝ))
      (E := (cell13196 ⟨15, by decide⟩).energy) (xi := (160616049100861 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13196 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13196]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13196])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13196) (a := (83548034363379 / 100000000000000 : ℝ)) (b := (31204577693 / 20000000000000 : ℝ)) (q := (1097045624869 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13196])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13196])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13196]

theorem cert13196_16 : CellCertificate 13196 (436666949464233 / 5000000000000000 : ℝ) (795853634604117 / 500000000000000000 : ℝ) (160616049100861 / 5000000000000000 : ℝ)
    (cell13196 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · have h := gap_lower (n := 13196) (a := (3340540584091 / 4000000000000 : ℝ)) (b := (31204577693 / 20000000000000 : ℝ)) (q := (2194095241633 / 100000000000000 : ℝ))
      (E := (cell13196 ⟨16, by decide⟩).energy) (xi := (160616049100861 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13196 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13196]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13196])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13196) (a := (3340540584091 / 4000000000000 : ℝ)) (b := (31204577693 / 20000000000000 : ℝ)) (q := (2194095241633 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13196])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13196])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13196]

theorem cert13196_17 : CellCertificate 13196 (436666949464233 / 5000000000000000 : ℝ) (795853634604117 / 500000000000000000 : ℝ) (160616049100861 / 5000000000000000 : ℝ)
    (cell13196 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · have h := gap_lower (n := 13196) (a := (41739509564781 / 50000000000000 : ℝ)) (b := (31204577693 / 20000000000000 : ℝ)) (q := (548524820063 / 25000000000000 : ℝ))
      (E := (cell13196 ⟨17, by decide⟩).energy) (xi := (160616049100861 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13196 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13196]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13196])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13196) (a := (41739509564781 / 50000000000000 : ℝ)) (b := (31204577693 / 20000000000000 : ℝ)) (q := (548524820063 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13196])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13196])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13196]

theorem cert13196_18 : CellCertificate 13196 (436666949464233 / 5000000000000000 : ℝ) (795853634604117 / 500000000000000000 : ℝ) (160616049100861 / 5000000000000000 : ℝ)
    (cell13196 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · have h := gap_lower (n := 13196) (a := (4172227395587 / 5000000000000 : ℝ)) (b := (31204577693 / 20000000000000 : ℝ)) (q := (2194103253607 / 100000000000000 : ℝ))
      (E := (cell13196 ⟨18, by decide⟩).energy) (xi := (160616049100861 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13196 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13196]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13196])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13196) (a := (4172227395587 / 5000000000000 : ℝ)) (b := (31204577693 / 20000000000000 : ℝ)) (q := (2194103253607 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13196])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13196])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13196]

theorem cert13196_19 : CellCertificate 13196 (436666949464233 / 5000000000000000 : ℝ) (795853634604117 / 500000000000000000 : ℝ) (160616049100861 / 5000000000000000 : ℝ)
    (cell13196 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · have h := gap_lower (n := 13196) (a := (2085252522887 / 2500000000000 : ℝ)) (b := (31204577693 / 20000000000000 : ℝ)) (q := (2194107282497 / 100000000000000 : ℝ))
      (E := (cell13196 ⟨19, by decide⟩).energy) (xi := (160616049100861 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13196 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13196]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13196])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13196) (a := (2085252522887 / 2500000000000 : ℝ)) (b := (31204577693 / 20000000000000 : ℝ)) (q := (2194107282497 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13196])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13196])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13196]

theorem cert13197_0 : CellCertificate 13197 (873307942017991 / 10000000000000000 : ℝ) (1591586619749743 / 1000000000000000000 : ℝ) (4015090054459 / 125000000000000 : ℝ)
    (cell13197 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · have h := gap_lower (n := 13197) (a := (84068754698207 / 100000000000000 : ℝ)) (b := (39002732919 / 25000000000000 : ℝ)) (q := (438784185149 / 20000000000000 : ℝ))
      (E := (cell13197 ⟨0, by decide⟩).energy) (xi := (4015090054459 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13197 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13197]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13197])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13197) (a := (84068754698207 / 100000000000000 : ℝ)) (b := (39002732919 / 25000000000000 : ℝ)) (q := (438784185149 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13197])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13197])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13197]

theorem cert13197_1 : CellCertificate 13197 (873307942017991 / 10000000000000000 : ℝ) (1591586619749743 / 1000000000000000000 : ℝ) (4015090054459 / 125000000000000 : ℝ)
    (cell13197 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · have h := gap_lower (n := 13197) (a := (42016933238211 / 50000000000000 : ℝ)) (b := (39002732919 / 25000000000000 : ℝ)) (q := (548481231939 / 25000000000000 : ℝ))
      (E := (cell13197 ⟨1, by decide⟩).energy) (xi := (4015090054459 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13197 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13197]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13197])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13197) (a := (42016933238211 / 50000000000000 : ℝ)) (b := (39002732919 / 25000000000000 : ℝ)) (q := (548481231939 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13197])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13197])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13197]

theorem cert13197_2 : CellCertificate 13197 (873307942017991 / 10000000000000000 : ℝ) (1591586619749743 / 1000000000000000000 : ℝ) (4015090054459 / 125000000000000 : ℝ)
    (cell13197 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · have h := gap_lower (n := 13197) (a := (83999003067043 / 100000000000000 : ℝ)) (b := (39002732919 / 25000000000000 : ℝ)) (q := (2193928936327 / 100000000000000 : ℝ))
      (E := (cell13197 ⟨2, by decide⟩).energy) (xi := (4015090054459 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13197 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13197]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13197])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13197) (a := (83999003067043 / 100000000000000 : ℝ)) (b := (39002732919 / 25000000000000 : ℝ)) (q := (2193928936327 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13197])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13197])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13197]

theorem cert13197_3 : CellCertificate 13197 (873307942017991 / 10000000000000000 : ℝ) (1591586619749743 / 1000000000000000000 : ℝ) (4015090054459 / 125000000000000 : ℝ)
    (cell13197 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · have h := gap_lower (n := 13197) (a := (83964164433839 / 100000000000000 : ℝ)) (b := (39002732919 / 25000000000000 : ℝ)) (q := (2193932959833 / 100000000000000 : ℝ))
      (E := (cell13197 ⟨3, by decide⟩).energy) (xi := (4015090054459 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13197 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13197]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13197])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13197) (a := (83964164433839 / 100000000000000 : ℝ)) (b := (39002732919 / 25000000000000 : ℝ)) (q := (2193932959833 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13197])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13197])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13197]

theorem cert13197_4 : CellCertificate 13197 (873307942017991 / 10000000000000000 : ℝ) (1591586619749743 / 1000000000000000000 : ℝ) (4015090054459 / 125000000000000 : ℝ)
    (cell13197 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · have h := gap_lower (n := 13197) (a := (83929350540769 / 100000000000000 : ℝ)) (b := (39002732919 / 25000000000000 : ℝ)) (q := (219393700639 / 10000000000000 : ℝ))
      (E := (cell13197 ⟨4, by decide⟩).energy) (xi := (4015090054459 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13197 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13197]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13197])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13197) (a := (83929350540769 / 100000000000000 : ℝ)) (b := (39002732919 / 25000000000000 : ℝ)) (q := (219393700639 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13197])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13197])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13197]

theorem cert13197_5 : CellCertificate 13197 (873307942017991 / 10000000000000000 : ℝ) (1591586619749743 / 1000000000000000000 : ℝ) (4015090054459 / 125000000000000 : ℝ)
    (cell13197 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · have h := gap_lower (n := 13197) (a := (83894561351981 / 100000000000000 : ℝ)) (b := (39002732919 / 25000000000000 : ℝ)) (q := (1096970512943 / 50000000000000 : ℝ))
      (E := (cell13197 ⟨5, by decide⟩).energy) (xi := (4015090054459 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13197 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13197]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13197])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13197) (a := (83894561351981 / 100000000000000 : ℝ)) (b := (39002732919 / 25000000000000 : ℝ)) (q := (1096970512943 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13197])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13197])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13197]

theorem cert13197_6 : CellCertificate 13197 (873307942017991 / 10000000000000000 : ℝ) (1591586619749743 / 1000000000000000000 : ℝ) (4015090054459 / 125000000000000 : ℝ)
    (cell13197 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · have h := gap_lower (n := 13197) (a := (41929898415907 / 50000000000000 : ℝ)) (b := (39002732919 / 25000000000000 : ℝ)) (q := (438789005171 / 20000000000000 : ℝ))
      (E := (cell13197 ⟨6, by decide⟩).energy) (xi := (4015090054459 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13197 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13197]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13197])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13197) (a := (41929898415907 / 50000000000000 : ℝ)) (b := (39002732919 / 25000000000000 : ℝ)) (q := (438789005171 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13197])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13197])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13197]

theorem cert13197_7 : CellCertificate 13197 (873307942017991 / 10000000000000000 : ℝ) (1591586619749743 / 1000000000000000000 : ℝ) (4015090054459 / 125000000000000 : ℝ)
    (cell13197 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · have h := gap_lower (n := 13197) (a := (83825056944789 / 100000000000000 : ℝ)) (b := (39002732919 / 25000000000000 : ℝ)) (q := (1096974506791 / 50000000000000 : ℝ))
      (E := (cell13197 ⟨7, by decide⟩).energy) (xi := (4015090054459 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13197 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13197]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13197])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13197) (a := (83825056944789 / 100000000000000 : ℝ)) (b := (39002732919 / 25000000000000 : ℝ)) (q := (1096974506791 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13197])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13197])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13197]

theorem cert13197_8 : CellCertificate 13197 (873307942017991 / 10000000000000000 : ℝ) (1591586619749743 / 1000000000000000000 : ℝ) (4015090054459 / 125000000000000 : ℝ)
    (cell13197 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · have h := gap_lower (n := 13197) (a := (16758068331123 / 20000000000000 : ℝ)) (b := (39002732919 / 25000000000000 : ℝ)) (q := (34280516471 / 1562500000000 : ℝ))
      (E := (cell13197 ⟨8, by decide⟩).energy) (xi := (4015090054459 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13197 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13197]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13197])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13197) (a := (16758068331123 / 20000000000000 : ℝ)) (b := (39002732919 / 25000000000000 : ℝ)) (q := (34280516471 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13197])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13197])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13197]

theorem cert13197_9 : CellCertificate 13197 (873307942017991 / 10000000000000000 : ℝ) (1591586619749743 / 1000000000000000000 : ℝ) (4015090054459 / 125000000000000 : ℝ)
    (cell13197 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · have h := gap_lower (n := 13197) (a := (83755650929187 / 100000000000000 : ℝ)) (b := (39002732919 / 25000000000000 : ℝ)) (q := (1096978519127 / 50000000000000 : ℝ))
      (E := (cell13197 ⟨9, by decide⟩).energy) (xi := (4015090054459 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13197 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13197]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13197])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13197) (a := (83755650929187 / 100000000000000 : ℝ)) (b := (39002732919 / 25000000000000 : ℝ)) (q := (1096978519127 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13197])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13197])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13197]

theorem cert13197_10 : CellCertificate 13197 (873307942017991 / 10000000000000000 : ℝ) (1591586619749743 / 1000000000000000000 : ℝ) (4015090054459 / 125000000000000 : ℝ)
    (cell13197 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · have h := gap_lower (n := 13197) (a := (83720984730581 / 100000000000000 : ℝ)) (b := (39002732919 / 25000000000000 : ℝ)) (q := (1096980544277 / 50000000000000 : ℝ))
      (E := (cell13197 ⟨10, by decide⟩).energy) (xi := (4015090054459 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13197 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13197]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13197])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13197) (a := (83720984730581 / 100000000000000 : ℝ)) (b := (39002732919 / 25000000000000 : ℝ)) (q := (1096980544277 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13197])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13197])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13197]

theorem cert13197_11 : CellCertificate 13197 (873307942017991 / 10000000000000000 : ℝ) (1591586619749743 / 1000000000000000000 : ℝ) (4015090054459 / 125000000000000 : ℝ)
    (cell13197 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · have h := gap_lower (n := 13197) (a := (41843171512527 / 50000000000000 : ℝ)) (b := (39002732919 / 25000000000000 : ℝ)) (q := (8570176153 / 390625000000 : ℝ))
      (E := (cell13197 ⟨11, by decide⟩).energy) (xi := (4015090054459 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13197 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13197]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13197])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13197) (a := (41843171512527 / 50000000000000 : ℝ)) (b := (39002732919 / 25000000000000 : ℝ)) (q := (8570176153 / 390625000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13197])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13197])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13197]

theorem cert13197_12 : CellCertificate 13197 (873307942017991 / 10000000000000000 : ℝ) (1591586619749743 / 1000000000000000000 : ℝ) (4015090054459 / 125000000000000 : ℝ)
    (cell13197 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · have h := gap_lower (n := 13197) (a := (41825862889023 / 50000000000000 : ℝ)) (b := (39002732919 / 25000000000000 : ℝ)) (q := (2193969122197 / 100000000000000 : ℝ))
      (E := (cell13197 ⟨12, by decide⟩).energy) (xi := (4015090054459 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13197 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13197]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13197])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13197) (a := (41825862889023 / 50000000000000 : ℝ)) (b := (39002732919 / 25000000000000 : ℝ)) (q := (2193969122197 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13197])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13197])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13197]

theorem cert13197_13 : CellCertificate 13197 (873307942017991 / 10000000000000000 : ℝ) (1591586619749743 / 1000000000000000000 : ℝ) (4015090054459 / 125000000000000 : ℝ)
    (cell13197 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · have h := gap_lower (n := 13197) (a := (10452141619397 / 12500000000000 : ℝ)) (b := (39002732919 / 25000000000000 : ℝ)) (q := (2193973117267 / 100000000000000 : ℝ))
      (E := (cell13197 ⟨13, by decide⟩).energy) (xi := (4015090054459 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13197 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13197]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13197])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13197) (a := (10452141619397 / 12500000000000 : ℝ)) (b := (39002732919 / 25000000000000 : ℝ)) (q := (2193973117267 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13197])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13197])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13197]

theorem cert13197_14 : CellCertificate 13197 (873307942017991 / 10000000000000000 : ℝ) (1591586619749743 / 1000000000000000000 : ℝ) (4015090054459 / 125000000000000 : ℝ)
    (cell13197 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · have h := gap_lower (n := 13197) (a := (83582564522241 / 100000000000000 : ℝ)) (b := (39002732919 / 25000000000000 : ℝ)) (q := (548494286009 / 25000000000000 : ℝ))
      (E := (cell13197 ⟨14, by decide⟩).energy) (xi := (4015090054459 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13197 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13197]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13197])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13197) (a := (83582564522241 / 100000000000000 : ℝ)) (b := (39002732919 / 25000000000000 : ℝ)) (q := (548494286009 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13197])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13197])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13197]

theorem cert13197_15 : CellCertificate 13197 (873307942017991 / 10000000000000000 : ℝ) (1591586619749743 / 1000000000000000000 : ℝ) (4015090054459 / 125000000000000 : ℝ)
    (cell13197 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · have h := gap_lower (n := 13197) (a := (16709604089043 / 20000000000000 : ℝ)) (b := (39002732919 / 25000000000000 : ℝ)) (q := (274247643699 / 12500000000000 : ℝ))
      (E := (cell13197 ⟨15, by decide⟩).energy) (xi := (4015090054459 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13197 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13197]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13197])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13197) (a := (16709604089043 / 20000000000000 : ℝ)) (b := (39002732919 / 25000000000000 : ℝ)) (q := (274247643699 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13197])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13197])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13197]

theorem cert13197_16 : CellCertificate 13197 (873307942017991 / 10000000000000000 : ℝ) (1591586619749743 / 1000000000000000000 : ℝ) (4015090054459 / 125000000000000 : ℝ)
    (cell13197 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · have h := gap_lower (n := 13197) (a := (83513500690249 / 100000000000000 : ℝ)) (b := (39002732919 / 25000000000000 : ℝ)) (q := (1096992598577 / 50000000000000 : ℝ))
      (E := (cell13197 ⟨16, by decide⟩).energy) (xi := (4015090054459 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13197 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13197]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13197])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13197) (a := (83513500690249 / 100000000000000 : ℝ)) (b := (39002732919 / 25000000000000 : ℝ)) (q := (1096992598577 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13197])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13197])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13197]

theorem cert13197_17 : CellCertificate 13197 (873307942017991 / 10000000000000000 : ℝ) (1591586619749743 / 1000000000000000000 : ℝ) (4015090054459 / 125000000000000 : ℝ)
    (cell13197 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · have h := gap_lower (n := 13197) (a := (20869751305917 / 25000000000000 : ℝ)) (b := (39002732919 / 25000000000000 : ℝ)) (q := (1096994587511 / 50000000000000 : ℝ))
      (E := (cell13197 ⟨17, by decide⟩).energy) (xi := (4015090054459 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13197 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13197]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13197])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13197) (a := (20869751305917 / 25000000000000 : ℝ)) (b := (39002732919 / 25000000000000 : ℝ)) (q := (1096994587511 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13197])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13197])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13197]

theorem cert13197_18 : CellCertificate 13197 (873307942017991 / 10000000000000000 : ℝ) (1591586619749743 / 1000000000000000000 : ℝ) (4015090054459 / 125000000000000 : ℝ)
    (cell13197 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · have h := gap_lower (n := 13197) (a := (83444534011973 / 100000000000000 : ℝ)) (b := (39002732919 / 25000000000000 : ℝ)) (q := (274249150523 / 12500000000000 : ℝ))
      (E := (cell13197 ⟨18, by decide⟩).energy) (xi := (4015090054459 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13197 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13197]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13197])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13197) (a := (83444534011973 / 100000000000000 : ℝ)) (b := (39002732919 / 25000000000000 : ℝ)) (q := (274249150523 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13197])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13197])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13197]

theorem cert13197_19 : CellCertificate 13197 (873307942017991 / 10000000000000000 : ℝ) (1591586619749743 / 1000000000000000000 : ℝ) (4015090054459 / 125000000000000 : ℝ)
    (cell13197 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · have h := gap_lower (n := 13197) (a := (16682017404367 / 20000000000000 : ℝ)) (b := (39002732919 / 25000000000000 : ℝ)) (q := (2193997230671 / 100000000000000 : ℝ))
      (E := (cell13197 ⟨19, by decide⟩).energy) (xi := (4015090054459 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13197 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13197]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13197])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13197) (a := (16682017404367 / 20000000000000 : ℝ)) (b := (39002732919 / 25000000000000 : ℝ)) (q := (2193997230671 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13197])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13197])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13197]

theorem cert13198_0 : CellCertificate 13198 (109160248608757 / 1250000000000000 : ℝ) (1591465988580027 / 1000000000000000000 : ℝ) (321182314393219 / 10000000000000000 : ℝ)
    (cell13198 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · have h := gap_lower (n := 13198) (a := (21017185172363 / 25000000000000 : ℝ)) (b := (6239959069 / 4000000000000 : ℝ)) (q := (2193810865523 / 100000000000000 : ℝ))
      (E := (cell13198 ⟨0, by decide⟩).energy) (xi := (321182314393219 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13198 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13198]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13198])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13198) (a := (21017185172363 / 25000000000000 : ℝ)) (b := (6239959069 / 4000000000000 : ℝ)) (q := (2193810865523 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13198])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13198])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13198]

theorem cert13198_1 : CellCertificate 13198 (109160248608757 / 1250000000000000 : ℝ) (1591465988580027 / 1000000000000000000 : ℝ) (321182314393219 / 10000000000000000 : ℝ)
    (cell13198 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · have h := gap_lower (n := 13198) (a := (42016926236943 / 50000000000000 : ℝ)) (b := (6239959069 / 4000000000000 : ℝ)) (q := (2193814922147 / 100000000000000 : ℝ))
      (E := (cell13198 ⟨1, by decide⟩).energy) (xi := (321182314393219 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13198 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13198]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13198])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13198) (a := (42016926236943 / 50000000000000 : ℝ)) (b := (6239959069 / 4000000000000 : ℝ)) (q := (2193814922147 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13198])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13198])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13198]

theorem cert13198_2 : CellCertificate 13198 (109160248608757 / 1250000000000000 : ℝ) (1591465988580027 / 1000000000000000000 : ℝ) (321182314393219 / 10000000000000000 : ℝ)
    (cell13198 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · have h := gap_lower (n := 13198) (a := (131248420423 / 156250000000 : ℝ)) (b := (6239959069 / 4000000000000 : ℝ)) (q := (2193818927521 / 100000000000000 : ℝ))
      (E := (cell13198 ⟨2, by decide⟩).energy) (xi := (321182314393219 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13198 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13198]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13198])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13198) (a := (131248420423 / 156250000000 : ℝ)) (b := (6239959069 / 4000000000000 : ℝ)) (q := (2193818927521 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13198])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13198])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13198]

theorem cert13198_3 : CellCertificate 13198 (109160248608757 / 1250000000000000 : ℝ) (1591465988580027 / 1000000000000000000 : ℝ) (321182314393219 / 10000000000000000 : ℝ)
    (cell13198 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · have h := gap_lower (n := 13198) (a := (20991037610931 / 25000000000000 : ℝ)) (b := (6239959069 / 4000000000000 : ℝ)) (q := (548455736969 / 25000000000000 : ℝ))
      (E := (cell13198 ⟨3, by decide⟩).energy) (xi := (321182314393219 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13198 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13198]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13198])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13198) (a := (20991037610931 / 25000000000000 : ℝ)) (b := (6239959069 / 4000000000000 : ℝ)) (q := (548455736969 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13198])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13198])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13198]

theorem cert13198_4 : CellCertificate 13198 (109160248608757 / 1250000000000000 : ℝ) (1591465988580027 / 1000000000000000000 : ℝ) (321182314393219 / 10000000000000000 : ℝ)
    (cell13198 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · have h := gap_lower (n := 13198) (a := (10491167069607 / 12500000000000 : ℝ)) (b := (6239959069 / 4000000000000 : ℝ)) (q := (1096913466689 / 50000000000000 : ℝ))
      (E := (cell13198 ⟨4, by decide⟩).energy) (xi := (321182314393219 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13198 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13198]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13198])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13198) (a := (10491167069607 / 12500000000000 : ℝ)) (b := (6239959069 / 4000000000000 : ℝ)) (q := (1096913466689 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13198])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13198])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13198]

theorem cert13198_5 : CellCertificate 13198 (109160248608757 / 1250000000000000 : ℝ) (1591465988580027 / 1000000000000000000 : ℝ) (321182314393219 / 10000000000000000 : ℝ)
    (cell13198 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · have h := gap_lower (n := 13198) (a := (16778909474853 / 20000000000000 : ℝ)) (b := (6239959069 / 4000000000000 : ℝ)) (q := (1096915474897 / 50000000000000 : ℝ))
      (E := (cell13198 ⟨5, by decide⟩).energy) (xi := (321182314393219 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13198 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13198]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13198])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13198) (a := (16778909474853 / 20000000000000 : ℝ)) (b := (6239959069 / 4000000000000 : ℝ)) (q := (1096915474897 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13198])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13198])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13198]

theorem cert13198_6 : CellCertificate 13198 (109160248608757 / 1250000000000000 : ℝ) (1591465988580027 / 1000000000000000000 : ℝ) (321182314393219 / 10000000000000000 : ℝ)
    (cell13198 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · have h := gap_lower (n := 13198) (a := (83859782860289 / 100000000000000 : ℝ)) (b := (6239959069 / 4000000000000 : ℝ)) (q := (219383494673 / 10000000000000 : ℝ))
      (E := (cell13198 ⟨6, by decide⟩).energy) (xi := (321182314393219 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13198 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13198]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13198])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13198) (a := (83859782860289 / 100000000000000 : ℝ)) (b := (6239959069 / 4000000000000 : ℝ)) (q := (219383494673 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13198])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13198])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13198]

theorem cert13198_7 : CellCertificate 13198 (109160248608757 / 1250000000000000 : ℝ) (1591465988580027 / 1000000000000000000 : ℝ) (321182314393219 / 10000000000000000 : ℝ)
    (cell13198 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · have h := gap_lower (n := 13198) (a := (83825042979449 / 100000000000000 : ℝ)) (b := (6239959069 / 4000000000000 : ℝ)) (q := (2193838989493 / 100000000000000 : ℝ))
      (E := (cell13198 ⟨7, by decide⟩).energy) (xi := (321182314393219 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13198 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13198]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13198])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13198) (a := (83825042979449 / 100000000000000 : ℝ)) (b := (6239959069 / 4000000000000 : ℝ)) (q := (2193838989493 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13198])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13198])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13198]

theorem cert13198_8 : CellCertificate 13198 (109160248608757 / 1250000000000000 : ℝ) (1591465988580027 / 1000000000000000000 : ℝ) (321182314393219 / 10000000000000000 : ℝ)
    (cell13198 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · have h := gap_lower (n := 13198) (a := (10473790962057 / 12500000000000 : ℝ)) (b := (6239959069 / 4000000000000 : ℝ)) (q := (2193843027139 / 100000000000000 : ℝ))
      (E := (cell13198 ⟨8, by decide⟩).energy) (xi := (321182314393219 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13198 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13198]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13198])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13198) (a := (10473790962057 / 12500000000000 : ℝ)) (b := (6239959069 / 4000000000000 : ℝ)) (q := (2193843027139 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13198])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13198])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13198]

theorem cert13198_9 : CellCertificate 13198 (109160248608757 / 1250000000000000 : ℝ) (1591465988580027 / 1000000000000000000 : ℝ) (321182314393219 / 10000000000000000 : ℝ)
    (cell13198 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · have h := gap_lower (n := 13198) (a := (41877818488101 / 50000000000000 : ℝ)) (b := (6239959069 / 4000000000000 : ℝ)) (q := (109692350419 / 5000000000000 : ℝ))
      (E := (cell13198 ⟨9, by decide⟩).energy) (xi := (321182314393219 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13198 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13198]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13198])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13198) (a := (41877818488101 / 50000000000000 : ℝ)) (b := (6239959069 / 4000000000000 : ℝ)) (q := (109692350419 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13198])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13198])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13198]

theorem cert13198_10 : CellCertificate 13198 (109160248608757 / 1250000000000000 : ℝ) (1591465988580027 / 1000000000000000000 : ℝ) (321182314393219 / 10000000000000000 : ℝ)
    (cell13198 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · have h := gap_lower (n := 13198) (a := (16744194156753 / 20000000000000 : ℝ)) (b := (6239959069 / 4000000000000 : ℝ)) (q := (1096925527929 / 50000000000000 : ℝ))
      (E := (cell13198 ⟨10, by decide⟩).energy) (xi := (321182314393219 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13198 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13198]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13198])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13198) (a := (16744194156753 / 20000000000000 : ℝ)) (b := (6239959069 / 4000000000000 : ℝ)) (q := (1096925527929 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13198])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13198])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13198]

theorem cert13198_11 : CellCertificate 13198 (109160248608757 / 1250000000000000 : ℝ) (1591465988580027 / 1000000000000000000 : ℝ) (321182314393219 / 10000000000000000 : ℝ)
    (cell13198 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · have h := gap_lower (n := 13198) (a := (41843164542201 / 50000000000000 : ℝ)) (b := (6239959069 / 4000000000000 : ℝ)) (q := (2193855059697 / 100000000000000 : ℝ))
      (E := (cell13198 ⟨11, by decide⟩).energy) (xi := (321182314393219 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13198 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13198]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13198])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13198) (a := (41843164542201 / 50000000000000 : ℝ)) (b := (6239959069 / 4000000000000 : ℝ)) (q := (2193855059697 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13198])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13198])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13198]

theorem cert13198_12 : CellCertificate 13198 (109160248608757 / 1250000000000000 : ℝ) (1591465988580027 / 1000000000000000000 : ℝ) (321182314393219 / 10000000000000000 : ℝ)
    (cell13198 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · have h := gap_lower (n := 13198) (a := (2614115995111 / 3125000000000 : ℝ)) (b := (6239959069 / 4000000000000 : ℝ)) (q := (1096929541999 / 50000000000000 : ℝ))
      (E := (cell13198 ⟨12, by decide⟩).energy) (xi := (321182314393219 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13198 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13198]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13198])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13198) (a := (2614115995111 / 3125000000000 : ℝ)) (b := (6239959069 / 4000000000000 : ℝ)) (q := (1096929541999 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13198])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13198])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13198]

theorem cert13198_13 : CellCertificate 13198 (109160248608757 / 1250000000000000 : ℝ) (1591465988580027 / 1000000000000000000 : ℝ) (321182314393219 / 10000000000000000 : ℝ)
    (cell13198 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · have h := gap_lower (n := 13198) (a := (16723423805367 / 20000000000000 : ℝ)) (b := (6239959069 / 4000000000000 : ℝ)) (q := (2193863076387 / 100000000000000 : ℝ))
      (E := (cell13198 ⟨13, by decide⟩).energy) (xi := (321182314393219 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13198 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13198]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13198])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13198) (a := (16723423805367 / 20000000000000 : ℝ)) (b := (6239959069 / 4000000000000 : ℝ)) (q := (2193863076387 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13198])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13198])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13198]

theorem cert13198_14 : CellCertificate 13198 (109160248608757 / 1250000000000000 : ℝ) (1591465988580027 / 1000000000000000000 : ℝ) (321182314393219 / 10000000000000000 : ℝ)
    (cell13198 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · have h := gap_lower (n := 13198) (a := (83582550600047 / 100000000000000 : ℝ)) (b := (6239959069 / 4000000000000 : ℝ)) (q := (2193867100521 / 100000000000000 : ℝ))
      (E := (cell13198 ⟨14, by decide⟩).energy) (xi := (321182314393219 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13198 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13198]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13198])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13198) (a := (83582550600047 / 100000000000000 : ℝ)) (b := (6239959069 / 4000000000000 : ℝ)) (q := (2193867100521 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13198])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13198])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13198]

theorem cert13198_15 : CellCertificate 13198 (109160248608757 / 1250000000000000 : ℝ) (1591465988580027 / 1000000000000000000 : ℝ) (321182314393219 / 10000000000000000 : ℝ)
    (cell13198 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · have h := gap_lower (n := 13198) (a := (83548006529163 / 100000000000000 : ℝ)) (b := (6239959069 / 4000000000000 : ℝ)) (q := (219387110349 / 10000000000000 : ℝ))
      (E := (cell13198 ⟨15, by decide⟩).energy) (xi := (321182314393219 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13198 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13198]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13198])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13198) (a := (83548006529163 / 100000000000000 : ℝ)) (b := (6239959069 / 4000000000000 : ℝ)) (q := (219387110349 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13198])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13198])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13198]

theorem cert13198_16 : CellCertificate 13198 (109160248608757 / 1250000000000000 : ℝ) (1591465988580027 / 1000000000000000000 : ℝ) (321182314393219 / 10000000000000000 : ℝ)
    (cell13198 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · have h := gap_lower (n := 13198) (a := (83513486780333 / 100000000000000 : ℝ)) (b := (6239959069 / 4000000000000 : ℝ)) (q := (2193875148511 / 100000000000000 : ℝ))
      (E := (cell13198 ⟨16, by decide⟩).energy) (xi := (321182314393219 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13198 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13198]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13198])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13198) (a := (83513486780333 / 100000000000000 : ℝ)) (b := (6239959069 / 4000000000000 : ℝ)) (q := (2193875148511 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13198])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13198])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13198]

theorem cert13198_17 : CellCertificate 13198 (109160248608757 / 1250000000000000 : ℝ) (1591465988580027 / 1000000000000000000 : ℝ) (321182314393219 / 10000000000000000 : ℝ)
    (cell13198 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · have h := gap_lower (n := 13198) (a := (20869747829971 / 25000000000000 : ℝ)) (b := (6239959069 / 4000000000000 : ℝ)) (q := (2193879123883 / 100000000000000 : ℝ))
      (E := (cell13198 ⟨17, by decide⟩).energy) (xi := (321182314393219 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13198 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13198]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13198])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13198) (a := (20869747829971 / 25000000000000 : ℝ)) (b := (6239959069 / 4000000000000 : ℝ)) (q := (2193879123883 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13198])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13198])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13198]

theorem cert13198_18 : CellCertificate 13198 (109160248608757 / 1250000000000000 : ℝ) (1591465988580027 / 1000000000000000000 : ℝ) (321182314393219 / 10000000000000000 : ℝ)
    (cell13198 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · have h := gap_lower (n := 13198) (a := (41722260057157 / 50000000000000 : ℝ)) (b := (6239959069 / 4000000000000 : ℝ)) (q := (2193883150599 / 100000000000000 : ℝ))
      (E := (cell13198 ⟨18, by decide⟩).energy) (xi := (321182314393219 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13198 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13198]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13198])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13198) (a := (41722260057157 / 50000000000000 : ℝ)) (b := (6239959069 / 4000000000000 : ℝ)) (q := (2193883150599 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13198])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13198])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13198]

theorem cert13198_19 : CellCertificate 13198 (109160248608757 / 1250000000000000 : ℝ) (1591465988580027 / 1000000000000000000 : ℝ) (321182314393219 / 10000000000000000 : ℝ)
    (cell13198 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · have h := gap_lower (n := 13198) (a := (83410073130297 / 100000000000000 : ℝ)) (b := (6239959069 / 4000000000000 : ℝ)) (q := (548471793671 / 25000000000000 : ℝ))
      (E := (cell13198 ⟨19, by decide⟩).energy) (xi := (321182314393219 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13198 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13198]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13198])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13198) (a := (83410073130297 / 100000000000000 : ℝ)) (b := (6239959069 / 4000000000000 : ℝ)) (q := (548471793671 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13198])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13198])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13198]

theorem cert13199_0 : CellCertificate 13199 (873256039483803 / 10000000000000000 : ℝ) (795672687847463 / 500000000000000000 : ℝ) (160578714155133 / 5000000000000000 : ℝ)
    (cell13199 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · have h := gap_lower (n := 13199) (a := (42034363341411 / 50000000000000 : ℝ)) (b := (155987023611 / 100000000000000 : ℝ)) (q := (1096850429491 / 50000000000000 : ℝ))
      (E := (cell13199 ⟨0, by decide⟩).energy) (xi := (160578714155133 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13199 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13199]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13199])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13199) (a := (42034363341411 / 50000000000000 : ℝ)) (b := (155987023611 / 100000000000000 : ℝ)) (q := (1096850429491 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13199])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13199])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13199]

theorem cert13199_1 : CellCertificate 13199 (873256039483803 / 10000000000000000 : ℝ) (795672687847463 / 500000000000000000 : ℝ) (160578714155133 / 5000000000000000 : ℝ)
    (cell13199 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · have h := gap_lower (n := 13199) (a := (42016919236737 / 50000000000000 : ℝ)) (b := (155987023611 / 100000000000000 : ℝ)) (q := (2193704854481 / 100000000000000 : ℝ))
      (E := (cell13199 ⟨1, by decide⟩).energy) (xi := (160578714155133 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13199 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13199]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13199])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13199) (a := (42016919236737 / 50000000000000 : ℝ)) (b := (155987023611 / 100000000000000 : ℝ)) (q := (2193704854481 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13199])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13199])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13199]

theorem cert13199_2 : CellCertificate 13199 (873256039483803 / 10000000000000000 : ℝ) (795672687847463 / 500000000000000000 : ℝ) (160578714155133 / 5000000000000000 : ℝ)
    (cell13199 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · have h := gap_lower (n := 13199) (a := (83998975076521 / 100000000000000 : ℝ)) (b := (155987023611 / 100000000000000 : ℝ)) (q := (2193708914539 / 100000000000000 : ℝ))
      (E := (cell13199 ⟨2, by decide⟩).energy) (xi := (160578714155133 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13199 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13199]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13199])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13199) (a := (83998975076521 / 100000000000000 : ℝ)) (b := (155987023611 / 100000000000000 : ℝ)) (q := (2193708914539 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13199])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13199])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13199]

theorem cert13199_3 : CellCertificate 13199 (873256039483803 / 10000000000000000 : ℝ) (795672687847463 / 500000000000000000 : ℝ) (160578714155133 / 5000000000000000 : ℝ)
    (cell13199 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · have h := gap_lower (n := 13199) (a := (83964136455731 / 100000000000000 : ℝ)) (b := (155987023611 / 100000000000000 : ℝ)) (q := (2193712873817 / 100000000000000 : ℝ))
      (E := (cell13199 ⟨3, by decide⟩).energy) (xi := (160578714155133 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13199 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13199]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13199])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13199) (a := (83964136455731 / 100000000000000 : ℝ)) (b := (155987023611 / 100000000000000 : ℝ)) (q := (2193712873817 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13199])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13199])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13199]

theorem cert13199_4 : CellCertificate 13199 (873256039483803 / 10000000000000000 : ℝ) (795672687847463 / 500000000000000000 : ℝ) (160578714155133 / 5000000000000000 : ℝ)
    (cell13199 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · have h := gap_lower (n := 13199) (a := (16785864515013 / 20000000000000 : ℝ)) (b := (155987023611 / 100000000000000 : ℝ)) (q := (68553653567 / 3125000000000 : ℝ))
      (E := (cell13199 ⟨4, by decide⟩).energy) (xi := (160578714155133 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13199 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13199]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13199])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13199) (a := (16785864515013 / 20000000000000 : ℝ)) (b := (155987023611 / 100000000000000 : ℝ)) (q := (68553653567 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13199])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13199])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13199]

theorem cert13199_5 : CellCertificate 13199 (873256039483803 / 10000000000000000 : ℝ) (795672687847463 / 500000000000000000 : ℝ) (160578714155133 / 5000000000000000 : ℝ)
    (cell13199 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · have h := gap_lower (n := 13199) (a := (8389453339867 / 10000000000000 : ℝ)) (b := (155987023611 / 100000000000000 : ℝ)) (q := (137107557969 / 6250000000000 : ℝ))
      (E := (cell13199 ⟨5, by decide⟩).energy) (xi := (160578714155133 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13199 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13199]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13199])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13199) (a := (8389453339867 / 10000000000000 : ℝ)) (b := (155987023611 / 100000000000000 : ℝ)) (q := (137107557969 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13199])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13199])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13199]

theorem cert13199_6 : CellCertificate 13199 (873256039483803 / 10000000000000000 : ℝ) (795672687847463 / 500000000000000000 : ℝ) (160578714155133 / 5000000000000000 : ℝ)
    (cell13199 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · have h := gap_lower (n := 13199) (a := (83859768890883 / 100000000000000 : ℝ)) (b := (155987023611 / 100000000000000 : ℝ)) (q := (274215615179 / 12500000000000 : ℝ))
      (E := (cell13199 ⟨6, by decide⟩).energy) (xi := (160578714155133 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13199 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13199]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13199])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13199) (a := (83859768890883 / 100000000000000 : ℝ)) (b := (155987023611 / 100000000000000 : ℝ)) (q := (274215615179 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13199])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13199])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13199]

theorem cert13199_7 : CellCertificate 13199 (873256039483803 / 10000000000000000 : ℝ) (795672687847463 / 500000000000000000 : ℝ) (160578714155133 / 5000000000000000 : ℝ)
    (cell13199 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · have h := gap_lower (n := 13199) (a := (20956257254057 / 25000000000000 : ℝ)) (b := (155987023611 / 100000000000000 : ℝ)) (q := (1096864480617 / 50000000000000 : ℝ))
      (E := (cell13199 ⟨7, by decide⟩).energy) (xi := (160578714155133 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13199 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13199]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13199])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13199) (a := (20956257254057 / 25000000000000 : ℝ)) (b := (155987023611 / 100000000000000 : ℝ)) (q := (1096864480617 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13199])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13199])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13199]

theorem cert13199_8 : CellCertificate 13199 (873256039483803 / 10000000000000000 : ℝ) (795672687847463 / 500000000000000000 : ℝ) (160578714155133 / 5000000000000000 : ℝ)
    (cell13199 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · have h := gap_lower (n := 13199) (a := (41895156869707 / 50000000000000 : ℝ)) (b := (155987023611 / 100000000000000 : ℝ)) (q := (438746599193 / 20000000000000 : ℝ))
      (E := (cell13199 ⟨8, by decide⟩).energy) (xi := (160578714155133 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13199 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13199]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13199])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13199) (a := (41895156869707 / 50000000000000 : ℝ)) (b := (155987023611 / 100000000000000 : ℝ)) (q := (438746599193 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13199])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13199])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13199]

theorem cert13199_9 : CellCertificate 13199 (873256039483803 / 10000000000000000 : ℝ) (795672687847463 / 500000000000000000 : ℝ) (160578714155133 / 5000000000000000 : ℝ)
    (cell13199 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · have h := gap_lower (n := 13199) (a := (41877811512667 / 50000000000000 : ℝ)) (b := (155987023611 / 100000000000000 : ℝ)) (q := (1096868487169 / 50000000000000 : ℝ))
      (E := (cell13199 ⟨9, by decide⟩).energy) (xi := (160578714155133 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13199 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13199]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13199])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13199) (a := (41877811512667 / 50000000000000 : ℝ)) (b := (155987023611 / 100000000000000 : ℝ)) (q := (1096868487169 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13199])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13199])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13199]

theorem cert13199_10 : CellCertificate 13199 (873256039483803 / 10000000000000000 : ℝ) (795672687847463 / 500000000000000000 : ℝ) (160578714155133 / 5000000000000000 : ℝ)
    (cell13199 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · have h := gap_lower (n := 13199) (a := (16744191367813 / 20000000000000 : ℝ)) (b := (155987023611 / 100000000000000 : ℝ)) (q := (438748203799 / 20000000000000 : ℝ))
      (E := (cell13199 ⟨10, by decide⟩).energy) (xi := (160578714155133 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13199 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13199]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13199])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13199) (a := (16744191367813 / 20000000000000 : ℝ)) (b := (155987023611 / 100000000000000 : ℝ)) (q := (438748203799 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13199])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13199])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13199]

theorem cert13199_11 : CellCertificate 13199 (873256039483803 / 10000000000000000 : ℝ) (795672687847463 / 500000000000000000 : ℝ) (160578714155133 / 5000000000000000 : ℝ)
    (cell13199 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · have h := gap_lower (n := 13199) (a := (10460789393233 / 12500000000000 : ℝ)) (b := (155987023611 / 100000000000000 : ℝ)) (q := (109687251003 / 5000000000000 : ℝ))
      (E := (cell13199 ⟨11, by decide⟩).energy) (xi := (160578714155133 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13199 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13199]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13199])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13199) (a := (10460789393233 / 12500000000000 : ℝ)) (b := (155987023611 / 100000000000000 : ℝ)) (q := (109687251003 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13199])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13199])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13199]

theorem cert13199_12 : CellCertificate 13199 (873256039483803 / 10000000000000000 : ℝ) (795672687847463 / 500000000000000000 : ℝ) (160578714155133 / 5000000000000000 : ℝ)
    (cell13199 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · have h := gap_lower (n := 13199) (a := (20912924477793 / 25000000000000 : ℝ)) (b := (155987023611 / 100000000000000 : ℝ)) (q := (2193749041633 / 100000000000000 : ℝ))
      (E := (cell13199 ⟨12, by decide⟩).energy) (xi := (160578714155133 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13199 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13199]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13199])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13199) (a := (20912924477793 / 25000000000000 : ℝ)) (b := (155987023611 / 100000000000000 : ℝ)) (q := (2193749041633 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13199])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13199])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13199]

theorem cert13199_13 : CellCertificate 13199 (873256039483803 / 10000000000000000 : ℝ) (795672687847463 / 500000000000000000 : ℝ) (160578714155133 / 5000000000000000 : ℝ)
    (cell13199 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · have h := gap_lower (n := 13199) (a := (83617105100607 / 100000000000000 : ℝ)) (b := (155987023611 / 100000000000000 : ℝ)) (q := (2193753031341 / 100000000000000 : ℝ))
      (E := (cell13199 ⟨13, by decide⟩).energy) (xi := (160578714155133 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13199 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13199]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13199])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13199) (a := (83617105100607 / 100000000000000 : ℝ)) (b := (155987023611 / 100000000000000 : ℝ)) (q := (2193753031341 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13199])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13199])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13199]

theorem cert13199_14 : CellCertificate 13199 (873256039483803 / 10000000000000000 : ℝ) (795672687847463 / 500000000000000000 : ℝ) (160578714155133 / 5000000000000000 : ℝ)
    (cell13199 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · have h := gap_lower (n := 13199) (a := (16716507335993 / 20000000000000 : ℝ)) (b := (155987023611 / 100000000000000 : ℝ)) (q := (1096878526421 / 50000000000000 : ℝ))
      (E := (cell13199 ⟨14, by decide⟩).energy) (xi := (160578714155133 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13199 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13199]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13199])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13199) (a := (16716507335993 / 20000000000000 : ℝ)) (b := (155987023611 / 100000000000000 : ℝ)) (q := (1096878526421 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13199])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13199])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13199]

theorem cert13199_15 : CellCertificate 13199 (873256039483803 / 10000000000000000 : ℝ) (795672687847463 / 500000000000000000 : ℝ) (160578714155133 / 5000000000000000 : ℝ)
    (cell13199 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · have h := gap_lower (n := 13199) (a := (41773996307611 / 50000000000000 : ℝ)) (b := (155987023611 / 100000000000000 : ℝ)) (q := (2193761111433 / 100000000000000 : ℝ))
      (E := (cell13199 ⟨15, by decide⟩).energy) (xi := (160578714155133 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13199 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13199]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13199])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13199) (a := (41773996307611 / 50000000000000 : ℝ)) (b := (155987023611 / 100000000000000 : ℝ)) (q := (2193761111433 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13199])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13199])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13199]

theorem cert13199_16 : CellCertificate 13199 (873256039483803 / 10000000000000000 : ℝ) (795672687847463 / 500000000000000000 : ℝ) (160578714155133 / 5000000000000000 : ℝ)
    (cell13199 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · have h := gap_lower (n := 13199) (a := (5219592054533 / 6250000000000 : ℝ)) (b := (155987023611 / 100000000000000 : ℝ)) (q := (274220636963 / 12500000000000 : ℝ))
      (E := (cell13199 ⟨16, by decide⟩).energy) (xi := (160578714155133 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13199 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13199]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13199])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13199) (a := (5219592054533 / 6250000000000 : ℝ)) (b := (155987023611 / 100000000000000 : ℝ)) (q := (274220636963 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13199])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13199])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13199]

theorem cert13199_17 : CellCertificate 13199 (873256039483803 / 10000000000000000 : ℝ) (795672687847463 / 500000000000000000 : ℝ) (160578714155133 / 5000000000000000 : ℝ)
    (cell13199 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · have h := gap_lower (n := 13199) (a := (83478977418209 / 100000000000000 : ℝ)) (b := (155987023611 / 100000000000000 : ℝ)) (q := (2193769126839 / 100000000000000 : ℝ))
      (E := (cell13199 ⟨17, by decide⟩).energy) (xi := (160578714155133 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13199 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13199]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13199])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13199) (a := (83478977418209 / 100000000000000 : ℝ)) (b := (155987023611 / 100000000000000 : ℝ)) (q := (2193769126839 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13199])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13199])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13199]

theorem cert13199_18 : CellCertificate 13199 (873256039483803 / 10000000000000000 : ℝ) (795672687847463 / 500000000000000000 : ℝ) (160578714155133 / 5000000000000000 : ℝ)
    (cell13199 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · have h := gap_lower (n := 13199) (a := (16688901243753 / 20000000000000 : ℝ)) (b := (155987023611 / 100000000000000 : ℝ)) (q := (219377315113 / 10000000000000 : ℝ))
      (E := (cell13199 ⟨18, by decide⟩).energy) (xi := (160578714155133 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13199 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13199]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13199])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13199) (a := (16688901243753 / 20000000000000 : ℝ)) (b := (155987023611 / 100000000000000 : ℝ)) (q := (219377315113 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13199])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13199])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13199]

theorem cert13199_19 : CellCertificate 13199 (873256039483803 / 10000000000000000 : ℝ) (795672687847463 / 500000000000000000 : ℝ) (160578714155133 / 5000000000000000 : ℝ)
    (cell13199 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · have h := gap_lower (n := 13199) (a := (83410059240867 / 100000000000000 : ℝ)) (b := (155987023611 / 100000000000000 : ℝ)) (q := (54844429321 / 2500000000000 : ℝ))
      (E := (cell13199 ⟨19, by decide⟩).energy) (xi := (160578714155133 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13199 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13199]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13199])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13199) (a := (83410059240867 / 100000000000000 : ℝ)) (b := (155987023611 / 100000000000000 : ℝ)) (q := (54844429321 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13199])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13199])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13199]

end BstLean.Part268
