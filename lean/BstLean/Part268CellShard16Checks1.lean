import BstLean.Part268CellShard16Checks0

/-! Twenty scalar cells per dimension in a 25-dimension shard. -/
namespace BstLean.Part268
open Real BstLean.Part263

theorem cert12750_20 : CellCertificate 12750 (885298970126629 / 10000000000000000 : ℝ) (164740404868793 / 100000000000000000 : ℝ) (332736528762233 / 10000000000000000 : ℝ)
    (cell12750 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · have h := gap_lower (n := 12750) (a := (41690374317107 / 50000000000000 : ℝ)) (b := (6461824219 / 4000000000000 : ℝ)) (q := (1122727606041 / 50000000000000 : ℝ))
      (E := (cell12750 ⟨20, by decide⟩).energy) (xi := (332736528762233 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12750 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12750]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12750])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12750) (a := (41690374317107 / 50000000000000 : ℝ)) (b := (6461824219 / 4000000000000 : ℝ)) (q := (1122727606041 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12750])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12750])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12750]

theorem cert12750_21 : CellCertificate 12750 (885298970126629 / 10000000000000000 : ℝ) (164740404868793 / 100000000000000000 : ℝ) (332736528762233 / 10000000000000000 : ℝ)
    (cell12750 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · have h := gap_lower (n := 12750) (a := (20836570278013 / 25000000000000 : ℝ)) (b := (6461824219 / 4000000000000 : ℝ)) (q := (1122729601011 / 50000000000000 : ℝ))
      (E := (cell12750 ⟨21, by decide⟩).energy) (xi := (332736528762233 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12750 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12750]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12750])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12750) (a := (20836570278013 / 25000000000000 : ℝ)) (b := (6461824219 / 4000000000000 : ℝ)) (q := (1122729601011 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12750])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12750])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12750]

theorem cert12750_22 : CellCertificate 12750 (885298970126629 / 10000000000000000 : ℝ) (164740404868793 / 100000000000000000 : ℝ) (332736528762233 / 10000000000000000 : ℝ)
    (cell12750 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · have h := gap_lower (n := 12750) (a := (83311837807661 / 100000000000000 : ℝ)) (b := (6461824219 / 4000000000000 : ℝ)) (q := (1122731603831 / 50000000000000 : ℝ))
      (E := (cell12750 ⟨22, by decide⟩).energy) (xi := (332736528762233 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12750 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12750]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12750])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12750) (a := (83311837807661 / 100000000000000 : ℝ)) (b := (6461824219 / 4000000000000 : ℝ)) (q := (1122731603831 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12750])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12750])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12750]

theorem cert12750_23 : CellCertificate 12750 (885298970126629 / 10000000000000000 : ℝ) (164740404868793 / 100000000000000000 : ℝ) (332736528762233 / 10000000000000000 : ℝ)
    (cell12750 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · have h := gap_lower (n := 12750) (a := (41638709344101 / 50000000000000 : ℝ)) (b := (6461824219 / 4000000000000 : ℝ)) (q := (2245467232709 / 100000000000000 : ℝ))
      (E := (cell12750 ⟨23, by decide⟩).energy) (xi := (332736528762233 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12750 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12750]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12750])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12750) (a := (41638709344101 / 50000000000000 : ℝ)) (b := (6461824219 / 4000000000000 : ℝ)) (q := (2245467232709 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12750])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12750])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12750]

theorem cert12750_24 : CellCertificate 12750 (885298970126629 / 10000000000000000 : ℝ) (164740404868793 / 100000000000000000 : ℝ) (332736528762233 / 10000000000000000 : ℝ)
    (cell12750 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · have h := gap_lower (n := 12750) (a := (20810755930251 / 25000000000000 : ℝ)) (b := (6461824219 / 4000000000000 : ℝ)) (q := (140341951391 / 6250000000000 : ℝ))
      (E := (cell12750 ⟨24, by decide⟩).energy) (xi := (332736528762233 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12750 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12750]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12750])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12750) (a := (20810755930251 / 25000000000000 : ℝ)) (b := (6461824219 / 4000000000000 : ℝ)) (q := (140341951391 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12750])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12750])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12750]

theorem cert12750_25 : CellCertificate 12750 (885298970126629 / 10000000000000000 : ℝ) (164740404868793 / 100000000000000000 : ℝ) (332736528762233 / 10000000000000000 : ℝ)
    (cell12750 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · have h := gap_lower (n := 12750) (a := (16641730574713 / 20000000000000 : ℝ)) (b := (6461824219 / 4000000000000 : ℝ)) (q := (2245475237867 / 100000000000000 : ℝ))
      (E := (cell12750 ⟨25, by decide⟩).energy) (xi := (332736528762233 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12750 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12750]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12750])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12750) (a := (16641730574713 / 20000000000000 : ℝ)) (b := (6461824219 / 4000000000000 : ℝ)) (q := (2245475237867 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12750])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12750])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12750]

theorem cert12750_26 : CellCertificate 12750 (885298970126629 / 10000000000000000 : ℝ) (164740404868793 / 100000000000000000 : ℝ) (332736528762233 / 10000000000000000 : ℝ)
    (cell12750 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · have h := gap_lower (n := 12750) (a := (20793576528387 / 25000000000000 : ℝ)) (b := (6461824219 / 4000000000000 : ℝ)) (q := (2245479224121 / 100000000000000 : ℝ))
      (E := (cell12750 ⟨26, by decide⟩).energy) (xi := (332736528762233 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12750 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12750]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12750])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12750) (a := (20793576528387 / 25000000000000 : ℝ)) (b := (6461824219 / 4000000000000 : ℝ)) (q := (2245479224121 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12750])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12750])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12750]

theorem cert12750_27 : CellCertificate 12750 (885298970126629 / 10000000000000000 : ℝ) (164740404868793 / 100000000000000000 : ℝ) (332736528762233 / 10000000000000000 : ℝ)
    (cell12750 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · have h := gap_lower (n := 12750) (a := (41569991704391 / 50000000000000 : ℝ)) (b := (6461824219 / 4000000000000 : ℝ)) (q := (1122741621081 / 50000000000000 : ℝ))
      (E := (cell12750 ⟨27, by decide⟩).energy) (xi := (332736528762233 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12750 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12750]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12750])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12750) (a := (41569991704391 / 50000000000000 : ℝ)) (b := (6461824219 / 4000000000000 : ℝ)) (q := (1122741621081 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12750])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12750])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12750]

theorem cert12750_28 : CellCertificate 12750 (885298970126629 / 10000000000000000 : ℝ) (164740404868793 / 100000000000000000 : ℝ) (332736528762233 / 10000000000000000 : ℝ)
    (cell12750 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · have h := gap_lower (n := 12750) (a := (83105684727263 / 100000000000000 : ℝ)) (b := (6461824219 / 4000000000000 : ℝ)) (q := (1122743618027 / 50000000000000 : ℝ))
      (E := (cell12750 ⟨28, by decide⟩).energy) (xi := (332736528762233 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12750 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12750]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12750])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12750) (a := (83105684727263 / 100000000000000 : ℝ)) (b := (6461824219 / 4000000000000 : ℝ)) (q := (1122743618027 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12750])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12750])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12750]

theorem cert12750_29 : CellCertificate 12750 (885298970126629 / 10000000000000000 : ℝ) (164740404868793 / 100000000000000000 : ℝ) (332736528762233 / 10000000000000000 : ℝ)
    (cell12750 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · have h := gap_lower (n := 12750) (a := (83071410037147 / 100000000000000 : ℝ)) (b := (6461824219 / 4000000000000 : ℝ)) (q := (89819650661 / 4000000000000 : ℝ))
      (E := (cell12750 ⟨29, by decide⟩).energy) (xi := (332736528762233 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12750 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12750]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12750])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12750) (a := (83071410037147 / 100000000000000 : ℝ)) (b := (6461824219 / 4000000000000 : ℝ)) (q := (89819650661 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12750])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12750])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12750]

theorem cert12750_30 : CellCertificate 12750 (885298970126629 / 10000000000000000 : ℝ) (164740404868793 / 100000000000000000 : ℝ) (332736528762233 / 10000000000000000 : ℝ)
    (cell12750 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · have h := gap_lower (n := 12750) (a := (20759289826689 / 25000000000000 : ℝ)) (b := (6461824219 / 4000000000000 : ℝ)) (q := (561373819283 / 25000000000000 : ℝ))
      (E := (cell12750 ⟨30, by decide⟩).energy) (xi := (332736528762233 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12750 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12750]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12750])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12750) (a := (20759289826689 / 25000000000000 : ℝ)) (b := (6461824219 / 4000000000000 : ℝ)) (q := (561373819283 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12750])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12750])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12750]

theorem cert12750_31 : CellCertificate 12750 (885298970126629 / 10000000000000000 : ℝ) (164740404868793 / 100000000000000000 : ℝ) (332736528762233 / 10000000000000000 : ℝ)
    (cell12750 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · have h := gap_lower (n := 12750) (a := (83002932504571 / 100000000000000 : ℝ)) (b := (6461824219 / 4000000000000 : ℝ)) (q := (140343704353 / 6250000000000 : ℝ))
      (E := (cell12750 ⟨31, by decide⟩).energy) (xi := (332736528762233 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12750 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12750]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12750])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12750) (a := (83002932504571 / 100000000000000 : ℝ)) (b := (6461824219 / 4000000000000 : ℝ)) (q := (140343704353 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12750])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12750])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12750]

theorem cert12750_32 : CellCertificate 12750 (885298970126629 / 10000000000000000 : ℝ) (164740404868793 / 100000000000000000 : ℝ) (332736528762233 / 10000000000000000 : ℝ)
    (cell12750 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · have h := gap_lower (n := 12750) (a := (41484364799617 / 50000000000000 : ℝ)) (b := (6461824219 / 4000000000000 : ℝ)) (q := (2245503245621 / 100000000000000 : ℝ))
      (E := (cell12750 ⟨32, by decide⟩).energy) (xi := (332736528762233 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12750 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12750]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12750])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12750) (a := (41484364799617 / 50000000000000 : ℝ)) (b := (6461824219 / 4000000000000 : ℝ)) (q := (2245503245621 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12750])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12750])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12750]

theorem cert12750_33 : CellCertificate 12750 (885298970126629 / 10000000000000000 : ℝ) (164740404868793 / 100000000000000000 : ℝ) (332736528762233 / 10000000000000000 : ℝ)
    (cell12750 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · have h := gap_lower (n := 12750) (a := (20733637639887 / 25000000000000 : ℝ)) (b := (6461824219 / 4000000000000 : ℝ)) (q := (2245507264957 / 100000000000000 : ℝ))
      (E := (cell12750 ⟨33, by decide⟩).energy) (xi := (332736528762233 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12750 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12750]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12750])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12750) (a := (20733637639887 / 25000000000000 : ℝ)) (b := (6461824219 / 4000000000000 : ℝ)) (q := (2245507264957 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12750])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12750])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12750]

theorem cert12750_34 : CellCertificate 12750 (885298970126629 / 10000000000000000 : ℝ) (164740404868793 / 100000000000000000 : ℝ) (332736528762233 / 10000000000000000 : ℝ)
    (cell12750 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · have h := gap_lower (n := 12750) (a := (3316015814179 / 4000000000000 : ℝ)) (b := (6461824219 / 4000000000000 : ℝ)) (q := (2245511270203 / 100000000000000 : ℝ))
      (E := (cell12750 ⟨34, by decide⟩).energy) (xi := (332736528762233 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12750 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12750]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12750])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12750) (a := (3316015814179 / 4000000000000 : ℝ)) (b := (6461824219 / 4000000000000 : ℝ)) (q := (2245511270203 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12750])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12750])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12750]

theorem cert12750_35 : CellCertificate 12750 (885298970126629 / 10000000000000000 : ℝ) (164740404868793 / 100000000000000000 : ℝ) (332736528762233 / 10000000000000000 : ℝ)
    (cell12750 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · have h := gap_lower (n := 12750) (a := (20716565988283 / 25000000000000 : ℝ)) (b := (6461824219 / 4000000000000 : ℝ)) (q := (224551526223 / 10000000000000 : ℝ))
      (E := (cell12750 ⟨35, by decide⟩).energy) (xi := (332736528762233 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12750 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12750]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12750])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12750) (a := (20716565988283 / 25000000000000 : ℝ)) (b := (6461824219 / 4000000000000 : ℝ)) (q := (224551526223 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12750])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12750])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12750]

theorem cert12750_36 : CellCertificate 12750 (885298970126629 / 10000000000000000 : ℝ) (164740404868793 / 100000000000000000 : ℝ) (332736528762233 / 10000000000000000 : ℝ)
    (cell12750 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · have h := gap_lower (n := 12750) (a := (41416078162397 / 50000000000000 : ℝ)) (b := (6461824219 / 4000000000000 : ℝ)) (q := (449103860067 / 20000000000000 : ℝ))
      (E := (cell12750 ⟨36, by decide⟩).energy) (xi := (332736528762233 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12750 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12750]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12750])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12750) (a := (41416078162397 / 50000000000000 : ℝ)) (b := (6461824219 / 4000000000000 : ℝ)) (q := (449103860067 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12750])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12750])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12750]

theorem cert12750_37 : CellCertificate 12750 (885298970126629 / 10000000000000000 : ℝ) (164740404868793 / 100000000000000000 : ℝ) (332736528762233 / 10000000000000000 : ℝ)
    (cell12750 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · have h := gap_lower (n := 12750) (a := (41399036219447 / 50000000000000 : ℝ)) (b := (6461824219 / 4000000000000 : ℝ)) (q := (2245523267643 / 100000000000000 : ℝ))
      (E := (cell12750 ⟨37, by decide⟩).energy) (xi := (332736528762233 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12750 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12750]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12750])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12750) (a := (41399036219447 / 50000000000000 : ℝ)) (b := (6461824219 / 4000000000000 : ℝ)) (q := (2245523267643 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12750])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12750])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12750]

theorem cert12750_38 : CellCertificate 12750 (885298970126629 / 10000000000000000 : ℝ) (164740404868793 / 100000000000000000 : ℝ) (332736528762233 / 10000000000000000 : ℝ)
    (cell12750 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · have h := gap_lower (n := 12750) (a := (82764012265017 / 100000000000000 : ℝ)) (b := (6461824219 / 4000000000000 : ℝ)) (q := (280690910211 / 12500000000000 : ℝ))
      (E := (cell12750 ⟨38, by decide⟩).energy) (xi := (332736528762233 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12750 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12750]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12750])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12750) (a := (82764012265017 / 100000000000000 : ℝ)) (b := (6461824219 / 4000000000000 : ℝ)) (q := (280690910211 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12750])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12750])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12750]

theorem cert12750_39 : CellCertificate 12750 (885298970126629 / 10000000000000000 : ℝ) (164740404868793 / 100000000000000000 : ℝ) (332736528762233 / 10000000000000000 : ℝ)
    (cell12750 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · have h := gap_lower (n := 12750) (a := (82729975772903 / 100000000000000 : ℝ)) (b := (6461824219 / 4000000000000 : ℝ)) (q := (449106256757 / 20000000000000 : ℝ))
      (E := (cell12750 ⟨39, by decide⟩).energy) (xi := (332736528762233 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12750 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12750]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12750])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12750) (a := (82729975772903 / 100000000000000 : ℝ)) (b := (6461824219 / 4000000000000 : ℝ)) (q := (449106256757 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12750])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12750])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12750]

theorem cert12751_20 : CellCertificate 12751 (442635622719861 / 5000000000000000 : ℝ) (823637404175571 / 500000000000000000 : ℝ) (332709802679853 / 10000000000000000 : ℝ)
    (cell12751 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · have h := gap_lower (n := 12751) (a := (4169036995129 / 5000000000000 : ℝ)) (b := (40383195753 / 25000000000000 : ℝ)) (q := (1122667102457 / 50000000000000 : ℝ))
      (E := (cell12751 ⟨20, by decide⟩).energy) (xi := (332709802679853 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12751 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12751]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12751])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12751) (a := (4169036995129 / 5000000000000 : ℝ)) (b := (40383195753 / 25000000000000 : ℝ)) (q := (1122667102457 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12751])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12751])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12751]

theorem cert12751_21 : CellCertificate 12751 (442635622719861 / 5000000000000000 : ℝ) (823637404175571 / 500000000000000000 : ℝ) (332709802679853 / 10000000000000000 : ℝ)
    (cell12751 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · have h := gap_lower (n := 12751) (a := (20836568172429 / 25000000000000 : ℝ)) (b := (40383195753 / 25000000000000 : ℝ)) (q := (1122669089051 / 50000000000000 : ℝ))
      (E := (cell12751 ⟨21, by decide⟩).energy) (xi := (332709802679853 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12751 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12751]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12751])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12751) (a := (20836568172429 / 25000000000000 : ℝ)) (b := (40383195753 / 25000000000000 : ℝ)) (q := (1122669089051 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12751])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12751])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12751]

theorem cert12751_22 : CellCertificate 12751 (442635622719861 / 5000000000000000 : ℝ) (823637404175571 / 500000000000000000 : ℝ) (332709802679853 / 10000000000000000 : ℝ)
    (cell12751 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · have h := gap_lower (n := 12751) (a := (83311829694191 / 100000000000000 : ℝ)) (b := (40383195753 / 25000000000000 : ℝ)) (q := (2245342167699 / 100000000000000 : ℝ))
      (E := (cell12751 ⟨22, by decide⟩).energy) (xi := (332709802679853 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12751 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12751]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12751])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12751) (a := (83311829694191 / 100000000000000 : ℝ)) (b := (40383195753 / 25000000000000 : ℝ)) (q := (2245342167699 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12751])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12751])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12751]

theorem cert12751_23 : CellCertificate 12751 (442635622719861 / 5000000000000000 : ℝ) (823637404175571 / 500000000000000000 : ℝ) (332709802679853 / 10000000000000000 : ℝ)
    (cell12751 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · have h := gap_lower (n := 12751) (a := (2602419090099 / 3125000000000 : ℝ)) (b := (40383195753 / 25000000000000 : ℝ)) (q := (17541767011 / 781250000000 : ℝ))
      (E := (cell12751 ⟨23, by decide⟩).energy) (xi := (332709802679853 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12751 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12751]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12751])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12751) (a := (2602419090099 / 3125000000000 : ℝ)) (b := (40383195753 / 25000000000000 : ℝ)) (q := (17541767011 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12751])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12751])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12751]

theorem cert12751_24 : CellCertificate 12751 (442635622719861 / 5000000000000000 : ℝ) (823637404175571 / 500000000000000000 : ℝ) (332709802679853 / 10000000000000000 : ℝ)
    (cell12751 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · have h := gap_lower (n := 12751) (a := (83243016223977 / 100000000000000 : ℝ)) (b := (40383195753 / 25000000000000 : ℝ)) (q := (1122675105349 / 50000000000000 : ℝ))
      (E := (cell12751 ⟨24, by decide⟩).energy) (xi := (332709802679853 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12751 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12751]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12751])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12751) (a := (83243016223977 / 100000000000000 : ℝ)) (b := (40383195753 / 25000000000000 : ℝ)) (q := (1122675105349 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12751])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12751])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12751]

theorem cert12751_25 : CellCertificate 12751 (442635622719861 / 5000000000000000 : ℝ) (823637404175571 / 500000000000000000 : ℝ) (332709802679853 / 10000000000000000 : ℝ)
    (cell12751 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · have h := gap_lower (n := 12751) (a := (20802161421029 / 25000000000000 : ℝ)) (b := (40383195753 / 25000000000000 : ℝ)) (q := (2245354212403 / 100000000000000 : ℝ))
      (E := (cell12751 ⟨25, by decide⟩).energy) (xi := (332709802679853 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12751 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12751]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12751])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12751) (a := (20802161421029 / 25000000000000 : ℝ)) (b := (40383195753 / 25000000000000 : ℝ)) (q := (2245354212403 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12751])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12751])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12751]

theorem cert12751_26 : CellCertificate 12751 (442635622719861 / 5000000000000000 : ℝ) (823637404175571 / 500000000000000000 : ℝ) (332709802679853 / 10000000000000000 : ℝ)
    (cell12751 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · have h := gap_lower (n := 12751) (a := (83174299231249 / 100000000000000 : ℝ)) (b := (40383195753 / 25000000000000 : ℝ)) (q := (449071637091 / 20000000000000 : ℝ))
      (E := (cell12751 ⟨26, by decide⟩).energy) (xi := (332709802679853 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12751 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12751]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12751])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12751) (a := (83174299231249 / 100000000000000 : ℝ)) (b := (40383195753 / 25000000000000 : ℝ)) (q := (449071637091 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12751])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12751])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12751]

theorem cert12751_27 : CellCertificate 12751 (442635622719861 / 5000000000000000 : ℝ) (823637404175571 / 500000000000000000 : ℝ) (332709802679853 / 10000000000000000 : ℝ)
    (cell12751 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · have h := gap_lower (n := 12751) (a := (10392497104151 / 12500000000000 : ℝ)) (b := (40383195753 / 25000000000000 : ℝ)) (q := (1122681095497 / 50000000000000 : ℝ))
      (E := (cell12751 ⟨27, by decide⟩).energy) (xi := (332709802679853 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12751 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12751]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12751])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12751) (a := (10392497104151 / 12500000000000 : ℝ)) (b := (40383195753 / 25000000000000 : ℝ)) (q := (1122681095497 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12751])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12751])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12751]

theorem cert12751_28 : CellCertificate 12751 (442635622719861 / 5000000000000000 : ℝ) (823637404175571 / 500000000000000000 : ℝ) (332709802679853 / 10000000000000000 : ℝ)
    (cell12751 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · have h := gap_lower (n := 12751) (a := (41552839228993 / 50000000000000 : ℝ)) (b := (40383195753 / 25000000000000 : ℝ)) (q := (2245366173087 / 100000000000000 : ℝ))
      (E := (cell12751 ⟨28, by decide⟩).energy) (xi := (332709802679853 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12751 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12751]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12751])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12751) (a := (41552839228993 / 50000000000000 : ℝ)) (b := (40383195753 / 25000000000000 : ℝ)) (q := (2245366173087 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12751])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12751])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12751]

theorem cert12751_29 : CellCertificate 12751 (442635622719861 / 5000000000000000 : ℝ) (823637404175571 / 500000000000000000 : ℝ) (332709802679853 / 10000000000000000 : ℝ)
    (cell12751 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · have h := gap_lower (n := 12751) (a := (83071404073743 / 100000000000000 : ℝ)) (b := (40383195753 / 25000000000000 : ℝ)) (q := (112268509623 / 5000000000000 : ℝ))
      (E := (cell12751 ⟨29, by decide⟩).energy) (xi := (332709802679853 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12751 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12751]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12751])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12751) (a := (83071404073743 / 100000000000000 : ℝ)) (b := (40383195753 / 25000000000000 : ℝ)) (q := (112268509623 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12751])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12751])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12751]

theorem cert12751_30 : CellCertificate 12751 (442635622719861 / 5000000000000000 : ℝ) (823637404175571 / 500000000000000000 : ℝ) (332709802679853 / 10000000000000000 : ℝ)
    (cell12751 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · have h := gap_lower (n := 12751) (a := (83037153648799 / 100000000000000 : ℝ)) (b := (40383195753 / 25000000000000 : ℝ)) (q := (224537419267 / 10000000000000 : ℝ))
      (E := (cell12751 ⟨30, by decide⟩).energy) (xi := (332709802679853 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12751 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12751]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12751])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12751) (a := (83037153648799 / 100000000000000 : ℝ)) (b := (40383195753 / 25000000000000 : ℝ)) (q := (224537419267 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12751])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12751])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12751]

theorem cert12751_31 : CellCertificate 12751 (442635622719861 / 5000000000000000 : ℝ) (823637404175571 / 500000000000000000 : ℝ) (332709802679853 / 10000000000000000 : ℝ)
    (cell12751 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · have h := gap_lower (n := 12751) (a := (83002927151639 / 100000000000000 : ℝ)) (b := (40383195753 / 25000000000000 : ℝ)) (q := (561344558507 / 25000000000000 : ℝ))
      (E := (cell12751 ⟨31, by decide⟩).energy) (xi := (332709802679853 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12751 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12751]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12751])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12751) (a := (83002927151639 / 100000000000000 : ℝ)) (b := (40383195753 / 25000000000000 : ℝ)) (q := (561344558507 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12751])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12751])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12751]

theorem cert12751_32 : CellCertificate 12751 (442635622719861 / 5000000000000000 : ℝ) (823637404175571 / 500000000000000000 : ℝ) (332709802679853 / 10000000000000000 : ℝ)
    (cell12751 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · have h := gap_lower (n := 12751) (a := (10371090568863 / 12500000000000 : ℝ)) (b := (40383195753 / 25000000000000 : ℝ)) (q := (2245382201023 / 100000000000000 : ℝ))
      (E := (cell12751 ⟨32, by decide⟩).energy) (xi := (332709802679853 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12751 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12751]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12751])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12751) (a := (10371090568863 / 12500000000000 : ℝ)) (b := (40383195753 / 25000000000000 : ℝ)) (q := (2245382201023 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12751])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12751])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12751]

theorem cert12751_33 : CellCertificate 12751 (442635622719861 / 5000000000000000 : ℝ) (823637404175571 / 500000000000000000 : ℝ) (332709802679853 / 10000000000000000 : ℝ)
    (cell12751 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · have h := gap_lower (n := 12751) (a := (41467272907699 / 50000000000000 : ℝ)) (b := (40383195753 / 25000000000000 : ℝ)) (q := (2245386212079 / 100000000000000 : ℝ))
      (E := (cell12751 ⟨33, by decide⟩).energy) (xi := (332709802679853 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12751 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12751]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12751])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12751) (a := (41467272907699 / 50000000000000 : ℝ)) (b := (40383195753 / 25000000000000 : ℝ)) (q := (2245386212079 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12751])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12751])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12751]

theorem cert12751_34 : CellCertificate 12751 (442635622719861 / 5000000000000000 : ℝ) (823637404175571 / 500000000000000000 : ℝ) (332709802679853 / 10000000000000000 : ℝ)
    (cell12751 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · have h := gap_lower (n := 12751) (a := (82900390914083 / 100000000000000 : ℝ)) (b := (40383195753 / 25000000000000 : ℝ)) (q := (140336888109 / 6250000000000 : ℝ))
      (E := (cell12751 ⟨34, by decide⟩).energy) (xi := (332709802679853 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12751 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12751]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12751])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12751) (a := (82900390914083 / 100000000000000 : ℝ)) (b := (40383195753 / 25000000000000 : ℝ)) (q := (140336888109 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12751])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12751])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12751]

theorem cert12751_35 : CellCertificate 12751 (442635622719861 / 5000000000000000 : ℝ) (823637404175571 / 500000000000000000 : ℝ) (332709802679853 / 10000000000000000 : ℝ)
    (cell12751 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · have h := gap_lower (n := 12751) (a := (41433129908039 / 50000000000000 : ℝ)) (b := (40383195753 / 25000000000000 : ℝ)) (q := (2245394253519 / 100000000000000 : ℝ))
      (E := (cell12751 ⟨35, by decide⟩).energy) (xi := (332709802679853 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12751 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12751]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12751])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12751) (a := (41433129908039 / 50000000000000 : ℝ)) (b := (40383195753 / 25000000000000 : ℝ)) (q := (2245394253519 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12751])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12751])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12751]

theorem cert12751_36 : CellCertificate 12751 (442635622719861 / 5000000000000000 : ℝ) (823637404175571 / 500000000000000000 : ℝ) (332709802679853 / 10000000000000000 : ℝ)
    (cell12751 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · have h := gap_lower (n := 12751) (a := (82832152490659 / 100000000000000 : ℝ)) (b := (40383195753 / 25000000000000 : ℝ)) (q := (1122699113399 / 50000000000000 : ℝ))
      (E := (cell12751 ⟨36, by decide⟩).energy) (xi := (332709802679853 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12751 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12751]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12751])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12751) (a := (82832152490659 / 100000000000000 : ℝ)) (b := (40383195753 / 25000000000000 : ℝ)) (q := (1122699113399 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12751])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12751])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12751]

theorem cert12751_37 : CellCertificate 12751 (442635622719861 / 5000000000000000 : ℝ) (823637404175571 / 500000000000000000 : ℝ) (332709802679853 / 10000000000000000 : ℝ)
    (cell12751 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · have h := gap_lower (n := 12751) (a := (82798068907259 / 100000000000000 : ℝ)) (b := (40383195753 / 25000000000000 : ℝ)) (q := (2245402247291 / 100000000000000 : ℝ))
      (E := (cell12751 ⟨37, by decide⟩).energy) (xi := (332709802679853 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12751 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12751]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12751])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12751) (a := (82798068907259 / 100000000000000 : ℝ)) (b := (40383195753 / 25000000000000 : ℝ)) (q := (2245402247291 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12751])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12751])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12751]

theorem cert12751_38 : CellCertificate 12751 (442635622719861 / 5000000000000000 : ℝ) (823637404175571 / 500000000000000000 : ℝ) (332709802679853 / 10000000000000000 : ℝ)
    (cell12751 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · have h := gap_lower (n := 12751) (a := (10345501129433 / 12500000000000 : ℝ)) (b := (40383195753 / 25000000000000 : ℝ)) (q := (2245406256557 / 100000000000000 : ℝ))
      (E := (cell12751 ⟨38, by decide⟩).energy) (xi := (332709802679853 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12751 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12751]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12751])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12751) (a := (10345501129433 / 12500000000000 : ℝ)) (b := (40383195753 / 25000000000000 : ℝ)) (q := (2245406256557 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12751])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12751])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12751]

theorem cert12751_39 : CellCertificate 12751 (442635622719861 / 5000000000000000 : ℝ) (823637404175571 / 500000000000000000 : ℝ) (332709802679853 / 10000000000000000 : ℝ)
    (cell12751 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · have h := gap_lower (n := 12751) (a := (16545994569003 / 20000000000000 : ℝ)) (b := (40383195753 / 25000000000000 : ℝ)) (q := (2245410254567 / 100000000000000 : ℝ))
      (E := (cell12751 ⟨39, by decide⟩).energy) (xi := (332709802679853 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12751 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12751]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12751])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12751) (a := (16545994569003 / 20000000000000 : ℝ)) (b := (40383195753 / 25000000000000 : ℝ)) (q := (2245410254567 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12751])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12751])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12751]

theorem cert12752_20 : CellCertificate 12752 (885243524926223 / 10000000000000000 : ℝ) (411786397072701 / 250000000000000000 : ℝ) (166341540472813 / 5000000000000000 : ℝ)
    (cell12752 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · have h := gap_lower (n := 12752) (a := (83380731172543 / 100000000000000 : ℝ)) (b := (80759981299 / 50000000000000 : ℝ)) (q := (1122606567789 / 50000000000000 : ℝ))
      (E := (cell12752 ⟨20, by decide⟩).energy) (xi := (166341540472813 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12752 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12752]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12752])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12752) (a := (83380731172543 / 100000000000000 : ℝ)) (b := (80759981299 / 50000000000000 : ℝ)) (q := (1122606567789 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12752])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12752])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12752]

theorem cert12752_21 : CellCertificate 12752 (885243524926223 / 10000000000000000 : ℝ) (411786397072701 / 250000000000000000 : ℝ) (166341540472813 / 5000000000000000 : ℝ)
    (cell12752 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · have h := gap_lower (n := 12752) (a := (83346264268939 / 100000000000000 : ℝ)) (b := (80759981299 / 50000000000000 : ℝ)) (q := (1122608575169 / 50000000000000 : ℝ))
      (E := (cell12752 ⟨21, by decide⟩).energy) (xi := (166341540472813 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12752 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12752]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12752])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12752) (a := (83346264268939 / 100000000000000 : ℝ)) (b := (80759981299 / 50000000000000 : ℝ)) (q := (1122608575169 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12752])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12752])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12752]

theorem cert12752_22 : CellCertificate 12752 (885243524926223 / 10000000000000000 : ℝ) (411786397072701 / 250000000000000000 : ℝ) (166341540472813 / 5000000000000000 : ℝ)
    (cell12752 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · have h := gap_lower (n := 12752) (a := (20827955395561 / 25000000000000 : ℝ)) (b := (80759981299 / 50000000000000 : ℝ)) (q := (2245221182259 / 100000000000000 : ℝ))
      (E := (cell12752 ⟨22, by decide⟩).energy) (xi := (166341540472813 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12752 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12752]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12752])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12752) (a := (20827955395561 / 25000000000000 : ℝ)) (b := (80759981299 / 50000000000000 : ℝ)) (q := (2245221182259 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12752])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12752])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12752]

theorem cert12752_23 : CellCertificate 12752 (885243524926223 / 10000000000000000 : ℝ) (411786397072701 / 250000000000000000 : ℝ) (166341540472813 / 5000000000000000 : ℝ)
    (cell12752 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · have h := gap_lower (n := 12752) (a := (4163870153981 / 5000000000000 : ℝ)) (b := (80759981299 / 50000000000000 : ℝ)) (q := (2245225176691 / 100000000000000 : ℝ))
      (E := (cell12752 ⟨23, by decide⟩).energy) (xi := (166341540472813 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12752 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12752]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12752])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12752) (a := (4163870153981 / 5000000000000 : ℝ)) (b := (80759981299 / 50000000000000 : ℝ)) (q := (2245225176691 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12752])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12752])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12752]

theorem cert12752_24 : CellCertificate 12752 (885243524926223 / 10000000000000000 : ℝ) (411786397072701 / 250000000000000000 : ℝ) (166341540472813 / 5000000000000000 : ℝ)
    (cell12752 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · have h := gap_lower (n := 12752) (a := (41621504364199 / 50000000000000 : ℝ)) (b := (80759981299 / 50000000000000 : ℝ)) (q := (224522919541 / 10000000000000 : ℝ))
      (E := (cell12752 ⟨24, by decide⟩).energy) (xi := (166341540472813 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12752 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12752]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12752])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12752) (a := (41621504364199 / 50000000000000 : ℝ)) (b := (80759981299 / 50000000000000 : ℝ)) (q := (224522919541 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12752])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12752])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12752]

theorem cert12752_25 : CellCertificate 12752 (885243524926223 / 10000000000000000 : ℝ) (411786397072701 / 250000000000000000 : ℝ) (166341540472813 / 5000000000000000 : ℝ)
    (cell12752 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · have h := gap_lower (n := 12752) (a := (41604319248039 / 50000000000000 : ℝ)) (b := (80759981299 / 50000000000000 : ℝ)) (q := (2245233183247 / 100000000000000 : ℝ))
      (E := (cell12752 ⟨25, by decide⟩).energy) (xi := (166341540472813 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12752 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12752]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12752])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12752) (a := (41604319248039 / 50000000000000 : ℝ)) (b := (80759981299 / 50000000000000 : ℝ)) (q := (2245233183247 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12752])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12752])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12752]

theorem cert12752_26 : CellCertificate 12752 (885243524926223 / 10000000000000000 : ℝ) (411786397072701 / 250000000000000000 : ℝ) (166341540472813 / 5000000000000000 : ℝ)
    (cell12752 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · have h := gap_lower (n := 12752) (a := (3326971694013 / 4000000000000 : ℝ)) (b := (80759981299 / 50000000000000 : ℝ)) (q := (2245237201557 / 100000000000000 : ℝ))
      (E := (cell12752 ⟨26, by decide⟩).energy) (xi := (166341540472813 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12752 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12752]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12752])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12752) (a := (3326971694013 / 4000000000000 : ℝ)) (b := (80759981299 / 50000000000000 : ℝ)) (q := (2245237201557 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12752])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12752])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12752]

theorem cert12752_27 : CellCertificate 12752 (885243524926223 / 10000000000000000 : ℝ) (411786397072701 / 250000000000000000 : ℝ) (166341540472813 / 5000000000000000 : ℝ)
    (cell12752 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · have h := gap_lower (n := 12752) (a := (83139970258969 / 100000000000000 : ℝ)) (b := (80759981299 / 50000000000000 : ℝ)) (q := (2245241194659 / 100000000000000 : ℝ))
      (E := (cell12752 ⟨27, by decide⟩).energy) (xi := (166341540472813 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12752 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12752]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12752])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12752) (a := (83139970258969 / 100000000000000 : ℝ)) (b := (80759981299 / 50000000000000 : ℝ)) (q := (2245241194659 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12752])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12752])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12752]

theorem cert12752_28 : CellCertificate 12752 (885243524926223 / 10000000000000000 : ℝ) (411786397072701 / 250000000000000000 : ℝ) (166341540472813 / 5000000000000000 : ℝ)
    (cell12752 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · have h := gap_lower (n := 12752) (a := (10388209023751 / 12500000000000 : ℝ)) (b := (80759981299 / 50000000000000 : ℝ)) (q := (1122622582507 / 50000000000000 : ℝ))
      (E := (cell12752 ⟨28, by decide⟩).energy) (xi := (166341540472813 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12752 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12752]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12752])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12752) (a := (10388209023751 / 12500000000000 : ℝ)) (b := (80759981299 / 50000000000000 : ℝ)) (q := (1122622582507 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12752])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12752])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12752]

theorem cert12752_29 : CellCertificate 12752 (885243524926223 / 10000000000000000 : ℝ) (411786397072701 / 250000000000000000 : ℝ) (166341540472813 / 5000000000000000 : ℝ)
    (cell12752 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · have h := gap_lower (n := 12752) (a := (83071398111601 / 100000000000000 : ℝ)) (b := (80759981299 / 50000000000000 : ℝ)) (q := (44904983467 / 2000000000000 : ℝ))
      (E := (cell12752 ⟨29, by decide⟩).energy) (xi := (166341540472813 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12752 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12752]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12752])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12752) (a := (83071398111601 / 100000000000000 : ℝ)) (b := (80759981299 / 50000000000000 : ℝ)) (q := (44904983467 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12752])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12752])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12752]

theorem cert12752_30 : CellCertificate 12752 (885243524926223 / 10000000000000000 : ℝ) (411786397072701 / 250000000000000000 : ℝ) (166341540472813 / 5000000000000000 : ℝ)
    (cell12752 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · have h := gap_lower (n := 12752) (a := (20759286998017 / 25000000000000 : ℝ)) (b := (80759981299 / 50000000000000 : ℝ)) (q := (1122626581611 / 50000000000000 : ℝ))
      (E := (cell12752 ⟨30, by decide⟩).energy) (xi := (166341540472813 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12752 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12752]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12752])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12752) (a := (20759286998017 / 25000000000000 : ℝ)) (b := (80759981299 / 50000000000000 : ℝ)) (q := (1122626581611 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12752])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12752])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12752]

theorem cert12752_31 : CellCertificate 12752 (885243524926223 / 10000000000000000 : ℝ) (411786397072701 / 250000000000000000 : ℝ) (166341540472813 / 5000000000000000 : ℝ)
    (cell12752 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · have h := gap_lower (n := 12752) (a := (16600584359979 / 20000000000000 : ℝ)) (b := (80759981299 / 50000000000000 : ℝ)) (q := (2245257194943 / 100000000000000 : ℝ))
      (E := (cell12752 ⟨31, by decide⟩).energy) (xi := (166341540472813 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12752 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12752]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12752])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12752) (a := (16600584359979 / 20000000000000 : ℝ)) (b := (80759981299 / 50000000000000 : ℝ)) (q := (2245257194943 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12752])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12752])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12752]

theorem cert12752_32 : CellCertificate 12752 (885243524926223 / 10000000000000000 : ℝ) (411786397072701 / 250000000000000000 : ℝ) (166341540472813 / 5000000000000000 : ℝ)
    (cell12752 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · have h := gap_lower (n := 12752) (a := (3318748780149 / 4000000000000 : ℝ)) (b := (80759981299 / 50000000000000 : ℝ)) (q := (561315302891 / 25000000000000 : ℝ))
      (E := (cell12752 ⟨32, by decide⟩).energy) (xi := (166341540472813 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12752 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12752]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12752])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12752) (a := (3318748780149 / 4000000000000 : ℝ)) (b := (80759981299 / 50000000000000 : ℝ)) (q := (561315302891 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12752])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12752])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12752]

theorem cert12752_33 : CellCertificate 12752 (885243524926223 / 10000000000000000 : ℝ) (411786397072701 / 250000000000000000 : ℝ) (166341540472813 / 5000000000000000 : ℝ)
    (cell12752 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · have h := gap_lower (n := 12752) (a := (41467270536181 / 50000000000000 : ℝ)) (b := (80759981299 / 50000000000000 : ℝ)) (q := (2245265214401 / 100000000000000 : ℝ))
      (E := (cell12752 ⟨33, by decide⟩).energy) (xi := (166341540472813 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12752 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12752]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12752])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12752) (a := (41467270536181 / 50000000000000 : ℝ)) (b := (80759981299 / 50000000000000 : ℝ)) (q := (2245265214401 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12752])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12752])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12752]

theorem cert12752_34 : CellCertificate 12752 (885243524926223 / 10000000000000000 : ℝ) (411786397072701 / 250000000000000000 : ℝ) (166341540472813 / 5000000000000000 : ℝ)
    (cell12752 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · have h := gap_lower (n := 12752) (a := (82900386474769 / 100000000000000 : ℝ)) (b := (80759981299 / 50000000000000 : ℝ)) (q := (35082331321 / 1562500000000 : ℝ))
      (E := (cell12752 ⟨34, by decide⟩).energy) (xi := (166341540472813 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12752 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12752]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12752])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12752) (a := (82900386474769 / 100000000000000 : ℝ)) (b := (80759981299 / 50000000000000 : ℝ)) (q := (35082331321 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12752])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12752])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12752]

theorem cert12752_35 : CellCertificate 12752 (885243524926223 / 10000000000000000 : ℝ) (411786397072701 / 250000000000000000 : ℝ) (166341540472813 / 5000000000000000 : ℝ)
    (cell12752 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · have h := gap_lower (n := 12752) (a := (41433127840033 / 50000000000000 : ℝ)) (b := (80759981299 / 50000000000000 : ℝ)) (q := (1122636591429 / 50000000000000 : ℝ))
      (E := (cell12752 ⟨35, by decide⟩).energy) (xi := (166341540472813 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12752 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12752]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12752])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12752) (a := (41433127840033 / 50000000000000 : ℝ)) (b := (80759981299 / 50000000000000 : ℝ)) (q := (1122636591429 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12752])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12752])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12752]

theorem cert12752_36 : CellCertificate 12752 (885243524926223 / 10000000000000000 : ℝ) (411786397072701 / 250000000000000000 : ℝ) (166341540472813 / 5000000000000000 : ℝ)
    (cell12752 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · have h := gap_lower (n := 12752) (a := (8283214865753 / 10000000000000 : ℝ)) (b := (80759981299 / 50000000000000 : ℝ)) (q := (1122638604321 / 50000000000000 : ℝ))
      (E := (cell12752 ⟨36, by decide⟩).energy) (xi := (166341540472813 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12752 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12752]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12752])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12752) (a := (8283214865753 / 10000000000000 : ℝ)) (b := (80759981299 / 50000000000000 : ℝ)) (q := (1122638604321 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12752])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12752])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12752]

theorem cert12752_37 : CellCertificate 12752 (885243524926223 / 10000000000000000 : ℝ) (411786397072701 / 250000000000000000 : ℝ) (166341540472813 / 5000000000000000 : ℝ)
    (cell12752 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · have h := gap_lower (n := 12752) (a := (82798065376593 / 100000000000000 : ℝ)) (b := (80759981299 / 50000000000000 : ℝ)) (q := (2245281223699 / 100000000000000 : ℝ))
      (E := (cell12752 ⟨37, by decide⟩).energy) (xi := (166341540472813 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12752 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12752]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12752])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12752) (a := (82798065376593 / 100000000000000 : ℝ)) (b := (80759981299 / 50000000000000 : ℝ)) (q := (2245281223699 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12752])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12752])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12752]

theorem cert12752_38 : CellCertificate 12752 (885243524926223 / 10000000000000000 : ℝ) (411786397072701 / 250000000000000000 : ℝ) (166341540472813 / 5000000000000000 : ℝ)
    (cell12752 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · have h := gap_lower (n := 12752) (a := (82764005806843 / 100000000000000 : ℝ)) (b := (80759981299 / 50000000000000 : ℝ)) (q := (35082581691 / 1562500000000 : ℝ))
      (E := (cell12752 ⟨38, by decide⟩).energy) (xi := (166341540472813 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12752 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12752]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12752])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12752) (a := (82764005806843 / 100000000000000 : ℝ)) (b := (80759981299 / 50000000000000 : ℝ)) (q := (35082581691 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12752])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12752])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12752]

theorem cert12752_39 : CellCertificate 12752 (885243524926223 / 10000000000000000 : ℝ) (411786397072701 / 250000000000000000 : ℝ) (166341540472813 / 5000000000000000 : ℝ)
    (cell12752 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · have h := gap_lower (n := 12752) (a := (41364984959011 / 50000000000000 : ℝ)) (b := (80759981299 / 50000000000000 : ℝ)) (q := (1122644611093 / 50000000000000 : ℝ))
      (E := (cell12752 ⟨39, by decide⟩).energy) (xi := (166341540472813 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12752 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12752]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12752])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12752) (a := (41364984959011 / 50000000000000 : ℝ)) (b := (80759981299 / 50000000000000 : ℝ)) (q := (1122644611093 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12752])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12752])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12752]

theorem cert12753_20 : CellCertificate 12753 (885215808585147 / 10000000000000000 : ℝ) (329403277700429 / 200000000000000000 : ℝ) (166328181779203 / 5000000000000000 : ℝ)
    (cell12753 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · have h := gap_lower (n := 12753) (a := (83380722444103 / 100000000000000 : ℝ)) (b := (161507144233 / 100000000000000 : ℝ)) (q := (2245092178927 / 100000000000000 : ℝ))
      (E := (cell12753 ⟨20, by decide⟩).energy) (xi := (166328181779203 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12753 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12753]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12753])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12753) (a := (83380722444103 / 100000000000000 : ℝ)) (b := (161507144233 / 100000000000000 : ℝ)) (q := (2245092178927 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12753])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12753])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12753]

theorem cert12753_21 : CellCertificate 12753 (885215808585147 / 10000000000000000 : ℝ) (329403277700429 / 200000000000000000 : ℝ) (166328181779203 / 5000000000000000 : ℝ)
    (cell12753 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · have h := gap_lower (n := 12753) (a := (83346255849721 / 100000000000000 : ℝ)) (b := (161507144233 / 100000000000000 : ℝ)) (q := (1122548088519 / 50000000000000 : ℝ))
      (E := (cell12753 ⟨21, by decide⟩).energy) (xi := (166328181779203 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12753 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12753]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12753])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12753) (a := (83346255849721 / 100000000000000 : ℝ)) (b := (161507144233 / 100000000000000 : ℝ)) (q := (1122548088519 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12753])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12753])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12753]

theorem cert12753_22 : CellCertificate 12753 (885215808585147 / 10000000000000000 : ℝ) (329403277700429 / 200000000000000000 : ℝ) (166328181779203 / 5000000000000000 : ℝ)
    (cell12753 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · have h := gap_lower (n := 12753) (a := (41655906735909 / 50000000000000 : ℝ)) (b := (161507144233 / 100000000000000 : ℝ)) (q := (1122550096507 / 50000000000000 : ℝ))
      (E := (cell12753 ⟨22, by decide⟩).energy) (xi := (166328181779203 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12753 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12753]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12753])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12753) (a := (41655906735909 / 50000000000000 : ℝ)) (b := (161507144233 / 100000000000000 : ℝ)) (q := (1122550096507 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12753])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12753])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12753]

theorem cert12753_23 : CellCertificate 12753 (885215808585147 / 10000000000000000 : ℝ) (329403277700429 / 200000000000000000 : ℝ) (166328181779203 / 5000000000000000 : ℝ)
    (cell12753 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · have h := gap_lower (n := 12753) (a := (16655479055511 / 20000000000000 : ℝ)) (b := (161507144233 / 100000000000000 : ℝ)) (q := (140319010763 / 6250000000000 : ℝ))
      (E := (cell12753 ⟨23, by decide⟩).energy) (xi := (166328181779203 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12753 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12753]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12753])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12753) (a := (16655479055511 / 20000000000000 : ℝ)) (b := (161507144233 / 100000000000000 : ℝ)) (q := (140319010763 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12753])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12753])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12753]

theorem cert12753_24 : CellCertificate 12753 (885215808585147 / 10000000000000000 : ℝ) (329403277700429 / 200000000000000000 : ℝ) (166328181779203 / 5000000000000000 : ℝ)
    (cell12753 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · have h := gap_lower (n := 12753) (a := (41621500617133 / 50000000000000 : ℝ)) (b := (161507144233 / 100000000000000 : ℝ)) (q := (280638522049 / 12500000000000 : ℝ))
      (E := (cell12753 ⟨24, by decide⟩).energy) (xi := (166328181779203 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12753 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12753]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12753])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12753) (a := (41621500617133 / 50000000000000 : ℝ)) (b := (161507144233 / 100000000000000 : ℝ)) (q := (280638522049 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12753])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12753])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12753]

theorem cert12753_25 : CellCertificate 12753 (885215808585147 / 10000000000000000 : ℝ) (329403277700429 / 200000000000000000 : ℝ) (166328181779203 / 5000000000000000 : ℝ)
    (cell12753 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · have h := gap_lower (n := 12753) (a := (1664172626189 / 2000000000000 : ℝ)) (b := (161507144233 / 100000000000000 : ℝ)) (q := (2245112208801 / 100000000000000 : ℝ))
      (E := (cell12753 ⟨25, by decide⟩).energy) (xi := (166328181779203 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12753 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12753]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12753])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12753) (a := (1664172626189 / 2000000000000 : ℝ)) (b := (161507144233 / 100000000000000 : ℝ)) (q := (2245112208801 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12753])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12753])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12753]

theorem cert12753_26 : CellCertificate 12753 (885215808585147 / 10000000000000000 : ℝ) (329403277700429 / 200000000000000000 : ℝ) (166328181779203 / 5000000000000000 : ℝ)
    (cell12753 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · have h := gap_lower (n := 12753) (a := (83174285470773 / 100000000000000 : ℝ)) (b := (161507144233 / 100000000000000 : ℝ)) (q := (2245116214007 / 100000000000000 : ℝ))
      (E := (cell12753 ⟨26, by decide⟩).energy) (xi := (166328181779203 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12753 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12753]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12753])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12753) (a := (83174285470773 / 100000000000000 : ℝ)) (b := (161507144233 / 100000000000000 : ℝ)) (q := (2245116214007 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12753])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12753])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12753]

theorem cert12753_27 : CellCertificate 12753 (885215808585147 / 10000000000000000 : ℝ) (329403277700429 / 200000000000000000 : ℝ) (166328181779203 / 5000000000000000 : ℝ)
    (cell12753 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · have h := gap_lower (n := 12753) (a := (83139963686067 / 100000000000000 : ℝ)) (b := (161507144233 / 100000000000000 : ℝ)) (q := (561280048677 / 25000000000000 : ℝ))
      (E := (cell12753 ⟨27, by decide⟩).energy) (xi := (166328181779203 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12753 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12753]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12753])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12753) (a := (83139963686067 / 100000000000000 : ℝ)) (b := (161507144233 / 100000000000000 : ℝ)) (q := (561280048677 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12753])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12753])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12753]

theorem cert12753_28 : CellCertificate 12753 (885215808585147 / 10000000000000000 : ℝ) (329403277700429 / 200000000000000000 : ℝ) (166328181779203 / 5000000000000000 : ℝ)
    (cell12753 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · have h := gap_lower (n := 12753) (a := (8310566592333 / 10000000000000 : ℝ)) (b := (161507144233 / 100000000000000 : ℝ)) (q := (1122562105917 / 50000000000000 : ℝ))
      (E := (cell12753 ⟨28, by decide⟩).energy) (xi := (166328181779203 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12753 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12753]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12753])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12753) (a := (8310566592333 / 10000000000000 : ℝ)) (b := (161507144233 / 100000000000000 : ℝ)) (q := (1122562105917 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12753])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12753])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12753]

theorem cert12753_29 : CellCertificate 12753 (885215808585147 / 10000000000000000 : ℝ) (329403277700429 / 200000000000000000 : ℝ) (166328181779203 / 5000000000000000 : ℝ)
    (cell12753 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · have h := gap_lower (n := 12753) (a := (83071392150721 / 100000000000000 : ℝ)) (b := (161507144233 / 100000000000000 : ℝ)) (q := (1122564104597 / 50000000000000 : ℝ))
      (E := (cell12753 ⟨29, by decide⟩).energy) (xi := (166328181779203 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12753 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12753]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12753])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12753) (a := (83071392150721 / 100000000000000 : ℝ)) (b := (161507144233 / 100000000000000 : ℝ)) (q := (1122564104597 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12753])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12753])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12753]

theorem cert12753_30 : CellCertificate 12753 (885215808585147 / 10000000000000000 : ℝ) (329403277700429 / 200000000000000000 : ℝ) (166328181779203 / 5000000000000000 : ℝ)
    (cell12753 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · have h := gap_lower (n := 12753) (a := (41518571168281 / 50000000000000 : ℝ)) (b := (161507144233 / 100000000000000 : ℝ)) (q := (2245132188791 / 100000000000000 : ℝ))
      (E := (cell12753 ⟨30, by decide⟩).energy) (xi := (166328181779203 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12753 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12753]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12753])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12753) (a := (41518571168281 / 50000000000000 : ℝ)) (b := (161507144233 / 100000000000000 : ℝ)) (q := (2245132188791 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12753])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12753])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12753]

theorem cert12753_31 : CellCertificate 12753 (885215808585147 / 10000000000000000 : ℝ) (329403277700429 / 200000000000000000 : ℝ) (166328181779203 / 5000000000000000 : ℝ)
    (cell12753 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · have h := gap_lower (n := 12753) (a := (4150145822467 / 5000000000000 : ℝ)) (b := (161507144233 / 100000000000000 : ℝ)) (q := (280642026367 / 12500000000000 : ℝ))
      (E := (cell12753 ⟨31, by decide⟩).energy) (xi := (166328181779203 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12753 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12753]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12753])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12753) (a := (4150145822467 / 5000000000000 : ℝ)) (b := (161507144233 / 100000000000000 : ℝ)) (q := (280642026367 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12753])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12753])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12753]

theorem cert12753_32 : CellCertificate 12753 (885215808585147 / 10000000000000000 : ℝ) (329403277700429 / 200000000000000000 : ℝ) (166328181779203 / 5000000000000000 : ℝ)
    (cell12753 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · have h := gap_lower (n := 12753) (a := (41484357228849 / 50000000000000 : ℝ)) (b := (161507144233 / 100000000000000 : ℝ)) (q := (1122570109339 / 50000000000000 : ℝ))
      (E := (cell12753 ⟨32, by decide⟩).energy) (xi := (166328181779203 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12753 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12753]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12753])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12753) (a := (41484357228849 / 50000000000000 : ℝ)) (b := (161507144233 / 100000000000000 : ℝ)) (q := (1122570109339 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12753])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12753])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12753]

theorem cert12753_33 : CellCertificate 12753 (885215808585147 / 10000000000000000 : ℝ) (329403277700429 / 200000000000000000 : ℝ) (166328181779203 / 5000000000000000 : ℝ)
    (cell12753 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · have h := gap_lower (n := 12753) (a := (41467268165221 / 50000000000000 : ℝ)) (b := (161507144233 / 100000000000000 : ℝ)) (q := (1122572106667 / 50000000000000 : ℝ))
      (E := (cell12753 ⟨33, by decide⟩).energy) (xi := (166328181779203 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12753 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12753]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12753])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12753) (a := (41467268165221 / 50000000000000 : ℝ)) (b := (161507144233 / 100000000000000 : ℝ)) (q := (1122572106667 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12753])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12753])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12753]

theorem cert12753_34 : CellCertificate 12753 (885215808585147 / 10000000000000000 : ℝ) (329403277700429 / 200000000000000000 : ℝ) (166328181779203 / 5000000000000000 : ℝ)
    (cell12753 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · have h := gap_lower (n := 12753) (a := (41450191018267 / 50000000000000 : ℝ)) (b := (161507144233 / 100000000000000 : ℝ)) (q := (2245148195993 / 100000000000000 : ℝ))
      (E := (cell12753 ⟨34, by decide⟩).energy) (xi := (166328181779203 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12753 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12753]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12753])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12753) (a := (41450191018267 / 50000000000000 : ℝ)) (b := (161507144233 / 100000000000000 : ℝ)) (q := (2245148195993 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12753])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12753])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12753]

theorem cert12753_35 : CellCertificate 12753 (885215808585147 / 10000000000000000 : ℝ) (329403277700429 / 200000000000000000 : ℝ) (166328181779203 / 5000000000000000 : ℝ)
    (cell12753 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · have h := gap_lower (n := 12753) (a := (10358281443137 / 12500000000000 : ℝ)) (b := (161507144233 / 100000000000000 : ℝ)) (q := (1122576113077 / 50000000000000 : ℝ))
      (E := (cell12753 ⟨35, by decide⟩).energy) (xi := (166328181779203 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12753 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12753]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12753])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12753) (a := (10358281443137 / 12500000000000 : ℝ)) (b := (161507144233 / 100000000000000 : ℝ)) (q := (1122576113077 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12753])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12753])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12753]

theorem cert12753_36 : CellCertificate 12753 (885215808585147 / 10000000000000000 : ℝ) (329403277700429 / 200000000000000000 : ℝ) (166328181779203 / 5000000000000000 : ℝ)
    (cell12753 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · have h := gap_lower (n := 12753) (a := (16566428965081 / 20000000000000 : ℝ)) (b := (161507144233 / 100000000000000 : ℝ)) (q := (2245156245869 / 100000000000000 : ℝ))
      (E := (cell12753 ⟨36, by decide⟩).energy) (xi := (166328181779203 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12753 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12753]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12753])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12753) (a := (16566428965081 / 20000000000000 : ℝ)) (b := (161507144233 / 100000000000000 : ℝ)) (q := (2245156245869 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12753])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12753])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12753]

theorem cert12753_37 : CellCertificate 12753 (885215808585147 / 10000000000000000 : ℝ) (329403277700429 / 200000000000000000 : ℝ) (166328181779203 / 5000000000000000 : ℝ)
    (cell12753 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · have h := gap_lower (n := 12753) (a := (16559612369379 / 20000000000000 : ℝ)) (b := (161507144233 / 100000000000000 : ℝ)) (q := (2245160255551 / 100000000000000 : ℝ))
      (E := (cell12753 ⟨37, by decide⟩).energy) (xi := (166328181779203 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12753 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12753]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12753])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12753) (a := (16559612369379 / 20000000000000 : ℝ)) (b := (161507144233 / 100000000000000 : ℝ)) (q := (2245160255551 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12753])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12753])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12753]

theorem cert12753_38 : CellCertificate 12753 (885215808585147 / 10000000000000000 : ℝ) (329403277700429 / 200000000000000000 : ℝ) (166328181779203 / 5000000000000000 : ℝ)
    (cell12753 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · have h := gap_lower (n := 12753) (a := (41382001289577 / 50000000000000 : ℝ)) (b := (161507144233 / 100000000000000 : ℝ)) (q := (449032851079 / 20000000000000 : ℝ))
      (E := (cell12753 ⟨38, by decide⟩).energy) (xi := (166328181779203 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12753 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12753]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12753])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12753) (a := (41382001289577 / 50000000000000 : ℝ)) (b := (161507144233 / 100000000000000 : ℝ)) (q := (449032851079 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12753])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12753])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12753]

theorem cert12753_39 : CellCertificate 12753 (885215808585147 / 10000000000000000 : ℝ) (329403277700429 / 200000000000000000 : ℝ) (166328181779203 / 5000000000000000 : ℝ)
    (cell12753 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · have h := gap_lower (n := 12753) (a := (3309198679677 / 4000000000000 : ℝ)) (b := (161507144233 / 100000000000000 : ℝ)) (q := (280646030671 / 12500000000000 : ℝ))
      (E := (cell12753 ⟨39, by decide⟩).energy) (xi := (166328181779203 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12753 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12753]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12753])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12753) (a := (3309198679677 / 4000000000000 : ℝ)) (b := (161507144233 / 100000000000000 : ℝ)) (q := (280646030671 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12753])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12753])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12753]

theorem cert12754_20 : CellCertificate 12754 (55324256025969 / 625000000000000 : ℝ) (823443604490197 / 500000000000000000 : ℝ) (332629650517043 / 10000000000000000 : ℝ)
    (cell12754 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · have h := gap_lower (n := 12754) (a := (41690356858629 / 50000000000000 : ℝ)) (b := (32298865583 / 20000000000000 : ℝ)) (q := (2244971218397 / 100000000000000 : ℝ))
      (E := (cell12754 ⟨20, by decide⟩).energy) (xi := (332629650517043 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12754 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12754]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12754])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12754) (a := (41690356858629 / 50000000000000 : ℝ)) (b := (32298865583 / 20000000000000 : ℝ)) (q := (2244971218397 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12754])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12754])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12754]

theorem cert12754_21 : CellCertificate 12754 (55324256025969 / 625000000000000 : ℝ) (823443604490197 / 500000000000000000 : ℝ) (332629650517043 / 10000000000000000 : ℝ)
    (cell12754 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · have h := gap_lower (n := 12754) (a := (83346247432063 / 100000000000000 : ℝ)) (b := (32298865583 / 20000000000000 : ℝ)) (q := (1122487599947 / 50000000000000 : ℝ))
      (E := (cell12754 ⟨21, by decide⟩).energy) (xi := (332629650517043 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12754 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12754]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12754])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12754) (a := (83346247432063 / 100000000000000 : ℝ)) (b := (32298865583 / 20000000000000 : ℝ)) (q := (1122487599947 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12754])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12754])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12754]

theorem cert12754_22 : CellCertificate 12754 (55324256025969 / 625000000000000 : ℝ) (823443604490197 / 500000000000000000 : ℝ) (332629650517043 / 10000000000000000 : ℝ)
    (cell12754 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · have h := gap_lower (n := 12754) (a := (41655902681457 / 50000000000000 : ℝ)) (b := (32298865583 / 20000000000000 : ℝ)) (q := (448995839993 / 20000000000000 : ℝ))
      (E := (cell12754 ⟨22, by decide⟩).energy) (xi := (332629650517043 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12754 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12754]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12754])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12754) (a := (41655902681457 / 50000000000000 : ℝ)) (b := (32298865583 / 20000000000000 : ℝ)) (q := (448995839993 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12754])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12754])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12754]

theorem cert12754_23 : CellCertificate 12754 (55324256025969 / 625000000000000 : ℝ) (823443604490197 / 500000000000000000 : ℝ) (332629650517043 / 10000000000000000 : ℝ)
    (cell12754 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · have h := gap_lower (n := 12754) (a := (5204836717311 / 6250000000000 : ℝ)) (b := (32298865583 / 20000000000000 : ℝ)) (q := (280622902789 / 12500000000000 : ℝ))
      (E := (cell12754 ⟨23, by decide⟩).energy) (xi := (332629650517043 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12754 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12754]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12754])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12754) (a := (5204836717311 / 6250000000000 : ℝ)) (b := (32298865583 / 20000000000000 : ℝ)) (q := (280622902789 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12754])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12754])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12754]

theorem cert12754_24 : CellCertificate 12754 (55324256025969 / 625000000000000 : ℝ) (823443604490197 / 500000000000000000 : ℝ) (332629650517043 / 10000000000000000 : ℝ)
    (cell12754 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · have h := gap_lower (n := 12754) (a := (83242993741581 / 100000000000000 : ℝ)) (b := (32298865583 / 20000000000000 : ℝ)) (q := (89799488481 / 4000000000000 : ℝ))
      (E := (cell12754 ⟨24, by decide⟩).energy) (xi := (332629650517043 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12754 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12754]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12754])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12754) (a := (83242993741581 / 100000000000000 : ℝ)) (b := (32298865583 / 20000000000000 : ℝ)) (q := (89799488481 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12754])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12754])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12754]

theorem cert12754_25 : CellCertificate 12754 (55324256025969 / 625000000000000 : ℝ) (823443604490197 / 500000000000000000 : ℝ) (332629650517043 / 10000000000000000 : ℝ)
    (cell12754 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · have h := gap_lower (n := 12754) (a := (10401078015529 / 12500000000000 : ℝ)) (b := (32298865583 / 20000000000000 : ℝ)) (q := (448998246133 / 20000000000000 : ℝ))
      (E := (cell12754 ⟨25, by decide⟩).energy) (xi := (332629650517043 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12754 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12754]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12754])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12754) (a := (10401078015529 / 12500000000000 : ℝ)) (b := (32298865583 / 20000000000000 : ℝ)) (q := (448998246133 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12754])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12754])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12754]

theorem cert12754_26 : CellCertificate 12754 (55324256025969 / 625000000000000 : ℝ) (823443604490197 / 500000000000000000 : ℝ) (332629650517043 / 10000000000000000 : ℝ)
    (cell12754 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · have h := gap_lower (n := 12754) (a := (41587139296297 / 50000000000000 : ℝ)) (b := (32298865583 / 20000000000000 : ℝ)) (q := (1122497611403 / 50000000000000 : ℝ))
      (E := (cell12754 ⟨26, by decide⟩).energy) (xi := (332629650517043 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12754 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12754]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12754])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12754) (a := (41587139296297 / 50000000000000 : ℝ)) (b := (32298865583 / 20000000000000 : ℝ)) (q := (1122497611403 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12754])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12754])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12754]

theorem cert12754_27 : CellCertificate 12754 (55324256025969 / 625000000000000 : ℝ) (823443604490197 / 500000000000000000 : ℝ) (332629650517043 / 10000000000000000 : ℝ)
    (cell12754 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · have h := gap_lower (n := 12754) (a := (83139957114501 / 100000000000000 : ℝ)) (b := (32298865583 / 20000000000000 : ℝ)) (q := (2244999249591 / 100000000000000 : ℝ))
      (E := (cell12754 ⟨27, by decide⟩).energy) (xi := (332629650517043 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12754 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12754]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12754])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12754) (a := (83139957114501 / 100000000000000 : ℝ)) (b := (32298865583 / 20000000000000 : ℝ)) (q := (2244999249591 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12754])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12754])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12754]

theorem cert12754_28 : CellCertificate 12754 (55324256025969 / 625000000000000 : ℝ) (823443604490197 / 500000000000000000 : ℝ) (332629650517043 / 10000000000000000 : ℝ)
    (cell12754 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · have h := gap_lower (n := 12754) (a := (1662113193159 / 2000000000000 : ℝ)) (b := (32298865583 / 20000000000000 : ℝ)) (q := (2245003255079 / 100000000000000 : ℝ))
      (E := (cell12754 ⟨28, by decide⟩).energy) (xi := (332629650517043 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12754 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12754]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12754])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12754) (a := (1662113193159 / 2000000000000 : ℝ)) (b := (32298865583 / 20000000000000 : ℝ)) (q := (2245003255079 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12754])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12754])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12754]

theorem cert12754_29 : CellCertificate 12754 (55324256025969 / 625000000000000 : ℝ) (823443604490197 / 500000000000000000 : ℝ) (332629650517043 / 10000000000000000 : ℝ)
    (cell12754 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · have h := gap_lower (n := 12754) (a := (41535693095551 / 50000000000000 : ℝ)) (b := (32298865583 / 20000000000000 : ℝ)) (q := (1122503620751 / 50000000000000 : ℝ))
      (E := (cell12754 ⟨29, by decide⟩).energy) (xi := (332629650517043 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12754 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12754]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12754])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12754) (a := (41535693095551 / 50000000000000 : ℝ)) (b := (32298865583 / 20000000000000 : ℝ)) (q := (1122503620751 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12754])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12754])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12754]

theorem cert12754_30 : CellCertificate 12754 (55324256025969 / 625000000000000 : ℝ) (823443604490197 / 500000000000000000 : ℝ) (332629650517043 / 10000000000000000 : ℝ)
    (cell12754 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · have h := gap_lower (n := 12754) (a := (83037136682281 / 100000000000000 : ℝ)) (b := (32298865583 / 20000000000000 : ℝ)) (q := (2245011269379 / 100000000000000 : ℝ))
      (E := (cell12754 ⟨30, by decide⟩).energy) (xi := (332629650517043 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12754 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12754]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12754])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12754) (a := (83037136682281 / 100000000000000 : ℝ)) (b := (32298865583 / 20000000000000 : ℝ)) (q := (2245011269379 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12754])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12754])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12754]

theorem cert12754_31 : CellCertificate 12754 (55324256025969 / 625000000000000 : ℝ) (823443604490197 / 500000000000000000 : ℝ) (332629650517043 / 10000000000000000 : ℝ)
    (cell12754 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · have h := gap_lower (n := 12754) (a := (83002911099973 / 100000000000000 : ℝ)) (b := (32298865583 / 20000000000000 : ℝ)) (q := (1122507611733 / 50000000000000 : ℝ))
      (E := (cell12754 ⟨31, by decide⟩).energy) (xi := (332629650517043 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12754 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12754]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12754])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12754) (a := (83002911099973 / 100000000000000 : ℝ)) (b := (32298865583 / 20000000000000 : ℝ)) (q := (1122507611733 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12754])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12754])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12754]

theorem cert12754_32 : CellCertificate 12754 (55324256025969 / 625000000000000 : ℝ) (823443604490197 / 500000000000000000 : ℝ) (332629650517043 / 10000000000000000 : ℝ)
    (cell12754 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · have h := gap_lower (n := 12754) (a := (82968709412823 / 100000000000000 : ℝ)) (b := (32298865583 / 20000000000000 : ℝ)) (q := (561254820233 / 25000000000000 : ℝ))
      (E := (cell12754 ⟨32, by decide⟩).energy) (xi := (332629650517043 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12754 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12754]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12754])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12754) (a := (82968709412823 / 100000000000000 : ℝ)) (b := (32298865583 / 20000000000000 : ℝ)) (q := (561254820233 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12754])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12754])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12754]

theorem cert12754_33 : CellCertificate 12754 (55324256025969 / 625000000000000 : ℝ) (823443604490197 / 500000000000000000 : ℝ) (332629650517043 / 10000000000000000 : ℝ)
    (cell12754 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · have h := gap_lower (n := 12754) (a := (20733632897409 / 25000000000000 : ℝ)) (b := (32298865583 / 20000000000000 : ℝ)) (q := (561255816867 / 25000000000000 : ℝ))
      (E := (cell12754 ⟨33, by decide⟩).energy) (xi := (332629650517043 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12754 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12754]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12754])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12754) (a := (20733632897409 / 25000000000000 : ℝ)) (b := (32298865583 / 20000000000000 : ℝ)) (q := (561255816867 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12754])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12754])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12754]

theorem cert12754_34 : CellCertificate 12754 (55324256025969 / 625000000000000 : ℝ) (823443604490197 / 500000000000000000 : ℝ) (332629650517043 / 10000000000000000 : ℝ)
    (cell12754 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · have h := gap_lower (n := 12754) (a := (5181273599961 / 6250000000000 : ℝ)) (b := (32298865583 / 20000000000000 : ℝ)) (q := (449005448541 / 20000000000000 : ℝ))
      (E := (cell12754 ⟨34, by decide⟩).energy) (xi := (332629650517043 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12754 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12754]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12754])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12754) (a := (5181273599961 / 6250000000000 : ℝ)) (b := (32298865583 / 20000000000000 : ℝ)) (q := (449005448541 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12754])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12754])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12754]

theorem cert12754_35 : CellCertificate 12754 (55324256025969 / 625000000000000 : ℝ) (823443604490197 / 500000000000000000 : ℝ) (332629650517043 / 10000000000000000 : ℝ)
    (cell12754 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · have h := gap_lower (n := 12754) (a := (82866247411167 / 100000000000000 : ℝ)) (b := (32298865583 / 20000000000000 : ℝ)) (q := (2245031266139 / 100000000000000 : ℝ))
      (E := (cell12754 ⟨35, by decide⟩).energy) (xi := (332629650517043 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12754 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12754]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12754])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12754) (a := (82866247411167 / 100000000000000 : ℝ)) (b := (32298865583 / 20000000000000 : ℝ)) (q := (2245031266139 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12754])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12754])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12754]

theorem cert12754_36 : CellCertificate 12754 (55324256025969 / 625000000000000 : ℝ) (823443604490197 / 500000000000000000 : ℝ) (332629650517043 / 10000000000000000 : ℝ)
    (cell12754 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · have h := gap_lower (n := 12754) (a := (16566428198857 / 20000000000000 : ℝ)) (b := (32298865583 / 20000000000000 : ℝ)) (q := (2245035279821 / 100000000000000 : ℝ))
      (E := (cell12754 ⟨36, by decide⟩).energy) (xi := (332629650517043 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12754 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12754]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12754])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12754) (a := (16566428198857 / 20000000000000 : ℝ)) (b := (32298865583 / 20000000000000 : ℝ)) (q := (2245035279821 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12754])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12754])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12754]

theorem cert12754_37 : CellCertificate 12754 (55324256025969 / 625000000000000 : ℝ) (823443604490197 / 500000000000000000 : ℝ) (332629650517043 / 10000000000000000 : ℝ)
    (cell12754 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · have h := gap_lower (n := 12754) (a := (16559611663633 / 20000000000000 : ℝ)) (b := (32298865583 / 20000000000000 : ℝ)) (q := (2245039284167 / 100000000000000 : ℝ))
      (E := (cell12754 ⟨37, by decide⟩).energy) (xi := (332629650517043 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12754 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12754]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12754])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12754) (a := (16559611663633 / 20000000000000 : ℝ)) (b := (32298865583 / 20000000000000 : ℝ)) (q := (2245039284167 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12754])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12754])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12754]

theorem cert12754_38 : CellCertificate 12754 (55324256025969 / 625000000000000 : ℝ) (823443604490197 / 500000000000000000 : ℝ) (332629650517043 / 10000000000000000 : ℝ)
    (cell12754 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · have h := gap_lower (n := 12754) (a := (82763999352397 / 100000000000000 : ℝ)) (b := (32298865583 / 20000000000000 : ℝ)) (q := (1122521639683 / 50000000000000 : ℝ))
      (E := (cell12754 ⟨38, by decide⟩).energy) (xi := (332629650517043 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12754 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12754]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12754])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12754) (a := (82763999352397 / 100000000000000 : ℝ)) (b := (32298865583 / 20000000000000 : ℝ)) (q := (1122521639683 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12754])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12754])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12754]

theorem cert12754_39 : CellCertificate 12754 (55324256025969 / 625000000000000 : ℝ) (823443604490197 / 500000000000000000 : ℝ) (332629650517043 / 10000000000000000 : ℝ)
    (cell12754 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · have h := gap_lower (n := 12754) (a := (20682491016681 / 25000000000000 : ℝ)) (b := (32298865583 / 20000000000000 : ℝ)) (q := (2245047265389 / 100000000000000 : ℝ))
      (E := (cell12754 ⟨39, by decide⟩).energy) (xi := (332629650517043 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12754 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12754]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12754])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12754) (a := (20682491016681 / 25000000000000 : ℝ)) (b := (32298865583 / 20000000000000 : ℝ)) (q := (2245047265389 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12754])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12754])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12754]

theorem cert12755_20 : CellCertificate 12755 (885160388416309 / 10000000000000000 : ℝ) (1646758049720783 / 1000000000000000000 : ℝ) (41575367727549 / 1250000000000000 : ℝ)
    (cell12755 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · have h := gap_lower (n := 12755) (a := (8338070499201 / 10000000000000 : ℝ)) (b := (32296302729 / 20000000000000 : ℝ)) (q := (2244850312269 / 100000000000000 : ℝ))
      (E := (cell12755 ⟨20, by decide⟩).energy) (xi := (41575367727549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12755 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12755]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12755])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12755) (a := (8338070499201 / 10000000000000 : ℝ)) (b := (32296302729 / 20000000000000 : ℝ)) (q := (2244850312269 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12755])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12755])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12755]

theorem cert12755_21 : CellCertificate 12755 (885160388416309 / 10000000000000000 : ℝ) (1646758049720783 / 1000000000000000000 : ℝ) (41575367727549 / 1250000000000000 : ℝ)
    (cell12755 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · have h := gap_lower (n := 12755) (a := (41673119507981 / 50000000000000 : ℝ)) (b := (32296302729 / 20000000000000 : ℝ)) (q := (2244854277217 / 100000000000000 : ℝ))
      (E := (cell12755 ⟨21, by decide⟩).energy) (xi := (41575367727549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12755 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12755]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12755])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12755) (a := (41673119507981 / 50000000000000 : ℝ)) (b := (32296302729 / 20000000000000 : ℝ)) (q := (2244854277217 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12755])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12755])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12755]

theorem cert12755_22 : CellCertificate 12755 (885160388416309 / 10000000000000000 : ℝ) (1646758049720783 / 1000000000000000000 : ℝ) (41575367727549 / 1250000000000000 : ℝ)
    (cell12755 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · have h := gap_lower (n := 12755) (a := (8331179725553 / 10000000000000 : ℝ)) (b := (32296302729 / 20000000000000 : ℝ)) (q := (1122429159887 / 50000000000000 : ℝ))
      (E := (cell12755 ⟨22, by decide⟩).energy) (xi := (41575367727549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12755 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12755]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12755])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12755) (a := (8331179725553 / 10000000000000 : ℝ)) (b := (32296302729 / 20000000000000 : ℝ)) (q := (1122429159887 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12755])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12755])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12755]

theorem cert12755_23 : CellCertificate 12755 (885160388416309 / 10000000000000000 : ℝ) (1646758049720783 / 1000000000000000000 : ℝ) (41575367727549 / 1250000000000000 : ℝ)
    (cell12755 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · have h := gap_lower (n := 12755) (a := (2081934491947 / 2500000000000 : ℝ)) (b := (32296302729 / 20000000000000 : ℝ)) (q := (448972465401 / 20000000000000 : ℝ))
      (E := (cell12755 ⟨23, by decide⟩).energy) (xi := (41575367727549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12755 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12755]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12755])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12755) (a := (2081934491947 / 2500000000000 : ℝ)) (b := (32296302729 / 20000000000000 : ℝ)) (q := (448972465401 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12755])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12755])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12755]

theorem cert12755_24 : CellCertificate 12755 (885160388416309 / 10000000000000000 : ℝ) (1646758049720783 / 1000000000000000000 : ℝ) (41575367727549 / 1250000000000000 : ℝ)
    (cell12755 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · have h := gap_lower (n := 12755) (a := (83242986250343 / 100000000000000 : ℝ)) (b := (32296302729 / 20000000000000 : ℝ)) (q := (561216575577 / 25000000000000 : ℝ))
      (E := (cell12755 ⟨24, by decide⟩).energy) (xi := (41575367727549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12755 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12755]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12755])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12755) (a := (83242986250343 / 100000000000000 : ℝ)) (b := (32296302729 / 20000000000000 : ℝ)) (q := (561216575577 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12755])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12755])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12755]

theorem cert12755_25 : CellCertificate 12755 (885160388416309 / 10000000000000000 : ℝ) (1646758049720783 / 1000000000000000000 : ℝ) (41575367727549 / 1250000000000000 : ℝ)
    (cell12755 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · have h := gap_lower (n := 12755) (a := (83208616940423 / 100000000000000 : ℝ)) (b := (32296302729 / 20000000000000 : ℝ)) (q := (2244870307241 / 100000000000000 : ℝ))
      (E := (cell12755 ⟨25, by decide⟩).energy) (xi := (41575367727549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12755 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12755]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12755])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12755) (a := (83208616940423 / 100000000000000 : ℝ)) (b := (32296302729 / 20000000000000 : ℝ)) (q := (2244870307241 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12755])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12755])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12755]

theorem cert12755_26 : CellCertificate 12755 (885160388416309 / 10000000000000000 : ℝ) (1646758049720783 / 1000000000000000000 : ℝ) (41575367727549 / 1250000000000000 : ℝ)
    (cell12755 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · have h := gap_lower (n := 12755) (a := (83174271715787 / 100000000000000 : ℝ)) (b := (32296302729 / 20000000000000 : ℝ)) (q := (2244874286379 / 100000000000000 : ℝ))
      (E := (cell12755 ⟨26, by decide⟩).energy) (xi := (41575367727549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12755 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12755]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12755])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12755) (a := (83174271715787 / 100000000000000 : ℝ)) (b := (32296302729 / 20000000000000 : ℝ)) (q := (2244874286379 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12755])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12755])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12755]

theorem cert12755_27 : CellCertificate 12755 (885160388416309 / 10000000000000000 : ℝ) (1646758049720783 / 1000000000000000000 : ℝ) (41575367727549 / 1250000000000000 : ℝ)
    (cell12755 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · have h := gap_lower (n := 12755) (a := (8313995054427 / 10000000000000 : ℝ)) (b := (32296302729 / 20000000000000 : ℝ)) (q := (112243915043 / 5000000000000 : ℝ))
      (E := (cell12755 ⟨27, by decide⟩).energy) (xi := (41575367727549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12755 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12755]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12755])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12755) (a := (8313995054427 / 10000000000000 : ℝ)) (b := (32296302729 / 20000000000000 : ℝ)) (q := (112243915043 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12755])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12755])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12755]

theorem cert12755_28 : CellCertificate 12755 (885160388416309 / 10000000000000000 : ℝ) (1646758049720783 / 1000000000000000000 : ℝ) (41575367727549 / 1250000000000000 : ℝ)
    (cell12755 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · have h := gap_lower (n := 12755) (a := (20776413348467 / 25000000000000 : ℝ)) (b := (32296302729 / 20000000000000 : ℝ)) (q := (2244882294749 / 100000000000000 : ℝ))
      (E := (cell12755 ⟨28, by decide⟩).energy) (xi := (41575367727549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12755 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12755]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12755])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12755) (a := (20776413348467 / 25000000000000 : ℝ)) (b := (32296302729 / 20000000000000 : ℝ)) (q := (2244882294749 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12755])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12755])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12755]

theorem cert12755_29 : CellCertificate 12755 (885160388416309 / 10000000000000000 : ℝ) (1646758049720783 / 1000000000000000000 : ℝ) (41575367727549 / 1250000000000000 : ℝ)
    (cell12755 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · have h := gap_lower (n := 12755) (a := (16614276046549 / 20000000000000 : ℝ)) (b := (32296302729 / 20000000000000 : ℝ)) (q := (1122443164383 / 50000000000000 : ℝ))
      (E := (cell12755 ⟨29, by decide⟩).energy) (xi := (41575367727549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12755 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12755]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12755])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12755) (a := (16614276046549 / 20000000000000 : ℝ)) (b := (32296302729 / 20000000000000 : ℝ)) (q := (1122443164383 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12755])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12755])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12755]

theorem cert12755_30 : CellCertificate 12755 (885160388416309 / 10000000000000000 : ℝ) (1646758049720783 / 1000000000000000000 : ℝ) (41575367727549 / 1250000000000000 : ℝ)
    (cell12755 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · have h := gap_lower (n := 12755) (a := (3321485241169 / 4000000000000 : ℝ)) (b := (32296302729 / 20000000000000 : ℝ)) (q := (1122445173233 / 50000000000000 : ℝ))
      (E := (cell12755 ⟨30, by decide⟩).energy) (xi := (41575367727549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12755 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12755]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12755])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12755) (a := (3321485241169 / 4000000000000 : ℝ)) (b := (32296302729 / 20000000000000 : ℝ)) (q := (1122445173233 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12755])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12755])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12755]

theorem cert12755_31 : CellCertificate 12755 (885160388416309 / 10000000000000000 : ℝ) (1646758049720783 / 1000000000000000000 : ℝ) (41575367727549 / 1250000000000000 : ℝ)
    (cell12755 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · have h := gap_lower (n := 12755) (a := (41501452875897 / 50000000000000 : ℝ)) (b := (32296302729 / 20000000000000 : ℝ)) (q := (2244894349617 / 100000000000000 : ℝ))
      (E := (cell12755 ⟨31, by decide⟩).energy) (xi := (41575367727549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12755 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12755]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12755])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12755) (a := (41501452875897 / 50000000000000 : ℝ)) (b := (32296302729 / 20000000000000 : ℝ)) (q := (2244894349617 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12755])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12755])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12755]

theorem cert12755_32 : CellCertificate 12755 (885160388416309 / 10000000000000000 : ℝ) (1646758049720783 / 1000000000000000000 : ℝ) (41575367727549 / 1250000000000000 : ℝ)
    (cell12755 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · have h := gap_lower (n := 12755) (a := (41484352184549 / 50000000000000 : ℝ)) (b := (32296302729 / 20000000000000 : ℝ)) (q := (2244898339763 / 100000000000000 : ℝ))
      (E := (cell12755 ⟨32, by decide⟩).energy) (xi := (41575367727549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12755 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12755]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12755])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12755) (a := (41484352184549 / 50000000000000 : ℝ)) (b := (32296302729 / 20000000000000 : ℝ)) (q := (2244898339763 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12755])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12755])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12755]

theorem cert12755_33 : CellCertificate 12755 (885160388416309 / 10000000000000000 : ℝ) (1646758049720783 / 1000000000000000000 : ℝ) (41575367727549 / 1250000000000000 : ℝ)
    (cell12755 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · have h := gap_lower (n := 12755) (a := (10366815856243 / 12500000000000 : ℝ)) (b := (32296302729 / 20000000000000 : ℝ)) (q := (2244902318217 / 100000000000000 : ℝ))
      (E := (cell12755 ⟨33, by decide⟩).energy) (xi := (41575367727549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12755 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12755]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12755])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12755) (a := (10366815856243 / 12500000000000 : ℝ)) (b := (32296302729 / 20000000000000 : ℝ)) (q := (2244902318217 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12755])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12755])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12755]

theorem cert12755_34 : CellCertificate 12755 (885160388416309 / 10000000000000000 : ℝ) (1646758049720783 / 1000000000000000000 : ℝ) (41575367727549 / 1250000000000000 : ℝ)
    (cell12755 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · have h := gap_lower (n := 12755) (a := (2590636661353 / 3125000000000 : ℝ)) (b := (32296302729 / 20000000000000 : ℝ)) (q := (56122658617 / 2500000000000 : ℝ))
      (E := (cell12755 ⟨34, by decide⟩).energy) (xi := (41575367727549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12755 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12755]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12755])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12755) (a := (2590636661353 / 3125000000000 : ℝ)) (b := (32296302729 / 20000000000000 : ℝ)) (q := (56122658617 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12755])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12755])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12755]

theorem cert12755_35 : CellCertificate 12755 (885160388416309 / 10000000000000000 : ℝ) (1646758049720783 / 1000000000000000000 : ℝ) (41575367727549 / 1250000000000000 : ℝ)
    (cell12755 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · have h := gap_lower (n := 12755) (a := (41433121639139 / 50000000000000 : ℝ)) (b := (32296302729 / 20000000000000 : ℝ)) (q := (280613795181 / 12500000000000 : ℝ))
      (E := (cell12755 ⟨35, by decide⟩).energy) (xi := (41575367727549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12755 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12755]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12755])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12755) (a := (41433121639139 / 50000000000000 : ℝ)) (b := (32296302729 / 20000000000000 : ℝ)) (q := (280613795181 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12755])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12755])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12755]

theorem cert12755_36 : CellCertificate 12755 (885160388416309 / 10000000000000000 : ℝ) (1646758049720783 / 1000000000000000000 : ℝ) (41575367727549 / 1250000000000000 : ℝ)
    (cell12755 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · have h := gap_lower (n := 12755) (a := (82832137164169 / 100000000000000 : ℝ)) (b := (32296302729 / 20000000000000 : ℝ)) (q := (2244914369159 / 100000000000000 : ℝ))
      (E := (cell12755 ⟨36, by decide⟩).energy) (xi := (41575367727549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12755 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12755]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12755])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12755) (a := (82832137164169 / 100000000000000 : ℝ)) (b := (32296302729 / 20000000000000 : ℝ)) (q := (2244914369159 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12755])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12755])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12755]

theorem cert12755_37 : CellCertificate 12755 (885160388416309 / 10000000000000000 : ℝ) (1646758049720783 / 1000000000000000000 : ℝ) (41575367727549 / 1250000000000000 : ℝ)
    (cell12755 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · have h := gap_lower (n := 12755) (a := (20699513697601 / 25000000000000 : ℝ)) (b := (32296302729 / 20000000000000 : ℝ)) (q := (2244918368227 / 100000000000000 : ℝ))
      (E := (cell12755 ⟨37, by decide⟩).energy) (xi := (41575367727549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12755 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12755]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12755])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12755) (a := (20699513697601 / 25000000000000 : ℝ)) (b := (32296302729 / 20000000000000 : ℝ)) (q := (2244918368227 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12755])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12755])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12755]

theorem cert12755_38 : CellCertificate 12755 (885160388416309 / 10000000000000000 : ℝ) (1646758049720783 / 1000000000000000000 : ℝ) (41575367727549 / 1250000000000000 : ℝ)
    (cell12755 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · have h := gap_lower (n := 12755) (a := (20690999031643 / 25000000000000 : ℝ)) (b := (32296302729 / 20000000000000 : ℝ)) (q := (2244922358843 / 100000000000000 : ℝ))
      (E := (cell12755 ⟨38, by decide⟩).energy) (xi := (41575367727549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12755 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12755]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12755])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12755) (a := (20690999031643 / 25000000000000 : ℝ)) (b := (32296302729 / 20000000000000 : ℝ)) (q := (2244922358843 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12755])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12755])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12755]

theorem cert12755_39 : CellCertificate 12755 (885160388416309 / 10000000000000000 : ℝ) (1646758049720783 / 1000000000000000000 : ℝ) (41575367727549 / 1250000000000000 : ℝ)
    (cell12755 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · have h := gap_lower (n := 12755) (a := (82729961142417 / 100000000000000 : ℝ)) (b := (32296302729 / 20000000000000 : ℝ)) (q := (2244926340977 / 100000000000000 : ℝ))
      (E := (cell12755 ⟨39, by decide⟩).energy) (xi := (41575367727549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12755 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12755]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12755])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12755) (a := (82729961142417 / 100000000000000 : ℝ)) (b := (32296302729 / 20000000000000 : ℝ)) (q := (2244926340977 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12755])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12755])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12755]

theorem cert12756_20 : CellCertificate 12756 (442566342293287 / 5000000000000000 : ℝ) (823314455359273 / 500000000000000000 : ℝ) (66515247493461 / 2000000000000000 : ℝ)
    (cell12756 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · have h := gap_lower (n := 12756) (a := (83380696268357 / 100000000000000 : ℝ)) (b := (80734350711 / 50000000000000 : ℝ)) (q := (2244729402263 / 100000000000000 : ℝ))
      (E := (cell12756 ⟨20, by decide⟩).energy) (xi := (66515247493461 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12756 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12756]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12756])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12756) (a := (83380696268357 / 100000000000000 : ℝ)) (b := (80734350711 / 50000000000000 : ℝ)) (q := (2244729402263 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12756])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12756])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12756]

theorem cert12756_21 : CellCertificate 12756 (442566342293287 / 5000000000000000 : ℝ) (823314455359273 / 500000000000000000 : ℝ) (66515247493461 / 2000000000000000 : ℝ)
    (cell12756 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · have h := gap_lower (n := 12756) (a := (4167311530071 / 5000000000000 : ℝ)) (b := (80734350711 / 50000000000000 : ℝ)) (q := (448946681801 / 20000000000000 : ℝ))
      (E := (cell12756 ⟨21, by decide⟩).energy) (xi := (66515247493461 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12756 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12756]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12756])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12756) (a := (4167311530071 / 5000000000000 : ℝ)) (b := (80734350711 / 50000000000000 : ℝ)) (q := (448946681801 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12756])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12756])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12756]

theorem cert12756_22 : CellCertificate 12756 (442566342293287 / 5000000000000000 : ℝ) (823314455359273 / 500000000000000000 : ℝ) (66515247493461 / 2000000000000000 : ℝ)
    (cell12756 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · have h := gap_lower (n := 12756) (a := (20827947287417 / 25000000000000 : ℝ)) (b := (80734350711 / 50000000000000 : ℝ)) (q := (112236871789 / 5000000000000 : ℝ))
      (E := (cell12756 ⟨22, by decide⟩).energy) (xi := (66515247493461 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12756 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12756]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12756])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12756) (a := (20827947287417 / 25000000000000 : ℝ)) (b := (80734350711 / 50000000000000 : ℝ)) (q := (112236871789 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12756])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12756])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12756]

theorem cert12756_23 : CellCertificate 12756 (442566342293287 / 5000000000000000 : ℝ) (823314455359273 / 500000000000000000 : ℝ) (66515247493461 / 2000000000000000 : ℝ)
    (cell12756 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · have h := gap_lower (n := 12756) (a := (83277371880267 / 100000000000000 : ℝ)) (b := (80734350711 / 50000000000000 : ℝ)) (q := (448948285587 / 20000000000000 : ℝ))
      (E := (cell12756 ⟨23, by decide⟩).energy) (xi := (66515247493461 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12756 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12756]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12756])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12756) (a := (83277371880267 / 100000000000000 : ℝ)) (b := (80734350711 / 50000000000000 : ℝ)) (q := (448948285587 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12756])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12756])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12756]

theorem cert12756_24 : CellCertificate 12756 (442566342293287 / 5000000000000000 : ℝ) (823314455359273 / 500000000000000000 : ℝ) (66515247493461 / 2000000000000000 : ℝ)
    (cell12756 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · have h := gap_lower (n := 12756) (a := (10405372345069 / 12500000000000 : ℝ)) (b := (80734350711 / 50000000000000 : ℝ)) (q := (2244745388863 / 100000000000000 : ℝ))
      (E := (cell12756 ⟨24, by decide⟩).energy) (xi := (66515247493461 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12756 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12756]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12756])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12756) (a := (10405372345069 / 12500000000000 : ℝ)) (b := (80734350711 / 50000000000000 : ℝ)) (q := (2244745388863 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12756])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12756])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12756]

theorem cert12756_25 : CellCertificate 12756 (442566342293287 / 5000000000000000 : ℝ) (823314455359273 / 500000000000000000 : ℝ) (66515247493461 / 2000000000000000 : ℝ)
    (cell12756 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · have h := gap_lower (n := 12756) (a := (10401076219753 / 12500000000000 : ℝ)) (b := (80734350711 / 50000000000000 : ℝ)) (q := (2244749438529 / 100000000000000 : ℝ))
      (E := (cell12756 ⟨25, by decide⟩).energy) (xi := (66515247493461 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12756 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12756]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12756])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12756) (a := (10401076219753 / 12500000000000 : ℝ)) (b := (80734350711 / 50000000000000 : ℝ)) (q := (2244749438529 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12756])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12756])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12756]

theorem cert12756_26 : CellCertificate 12756 (442566342293287 / 5000000000000000 : ℝ) (823314455359273 / 500000000000000000 : ℝ) (66515247493461 / 2000000000000000 : ℝ)
    (cell12756 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · have h := gap_lower (n := 12756) (a := (83174264840353 / 100000000000000 : ℝ)) (b := (80734350711 / 50000000000000 : ℝ)) (q := (561188351181 / 25000000000000 : ℝ))
      (E := (cell12756 ⟨26, by decide⟩).energy) (xi := (66515247493461 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12756 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12756]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12756])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12756) (a := (83174264840353 / 100000000000000 : ℝ)) (b := (80734350711 / 50000000000000 : ℝ)) (q := (561188351181 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12756])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12756])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12756]

theorem cert12756_27 : CellCertificate 12756 (442566342293287 / 5000000000000000 : ℝ) (823314455359273 / 500000000000000000 : ℝ) (66515247493461 / 2000000000000000 : ℝ)
    (cell12756 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · have h := gap_lower (n := 12756) (a := (41569971987687 / 50000000000000 : ℝ)) (b := (80734350711 / 50000000000000 : ℝ)) (q := (1122378703483 / 50000000000000 : ℝ))
      (E := (cell12756 ⟨27, by decide⟩).energy) (xi := (66515247493461 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12756 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12756]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12756])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12756) (a := (41569971987687 / 50000000000000 : ℝ)) (b := (80734350711 / 50000000000000 : ℝ)) (q := (1122378703483 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12756])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12756])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12756]

theorem cert12756_28 : CellCertificate 12756 (442566342293287 / 5000000000000000 : ℝ) (823314455359273 / 500000000000000000 : ℝ) (66515247493461 / 2000000000000000 : ℝ)
    (cell12756 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · have h := gap_lower (n := 12756) (a := (16621129426217 / 20000000000000 : ℝ)) (b := (80734350711 / 50000000000000 : ℝ)) (q := (1122380723893 / 50000000000000 : ℝ))
      (E := (cell12756 ⟨28, by decide⟩).energy) (xi := (66515247493461 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12756 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12756]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12756])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12756) (a := (16621129426217 / 20000000000000 : ℝ)) (b := (80734350711 / 50000000000000 : ℝ)) (q := (1122380723893 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12756])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12756])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12756]

theorem cert12756_29 : CellCertificate 12756 (442566342293287 / 5000000000000000 : ℝ) (823314455359273 / 500000000000000000 : ℝ) (66515247493461 / 2000000000000000 : ℝ)
    (cell12756 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · have h := gap_lower (n := 12756) (a := (83071374275649 / 100000000000000 : ℝ)) (b := (80734350711 / 50000000000000 : ℝ)) (q := (1122382706247 / 50000000000000 : ℝ))
      (E := (cell12756 ⟨29, by decide⟩).energy) (xi := (66515247493461 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12756 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12756]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12756])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12756) (a := (83071374275649 / 100000000000000 : ℝ)) (b := (80734350711 / 50000000000000 : ℝ)) (q := (1122382706247 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12756])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12756])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12756]

theorem cert12756_30 : CellCertificate 12756 (442566342293287 / 5000000000000000 : ℝ) (823314455359273 / 500000000000000000 : ℝ) (66515247493461 / 2000000000000000 : ℝ)
    (cell12756 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · have h := gap_lower (n := 12756) (a := (83037125377393 / 100000000000000 : ℝ)) (b := (80734350711 / 50000000000000 : ℝ)) (q := (1122384710027 / 50000000000000 : ℝ))
      (E := (cell12756 ⟨30, by decide⟩).energy) (xi := (66515247493461 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12756 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12756]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12756])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12756) (a := (83037125377393 / 100000000000000 : ℝ)) (b := (80734350711 / 50000000000000 : ℝ)) (q := (1122384710027 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12756])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12756])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12756]

theorem cert12756_31 : CellCertificate 12756 (442566342293287 / 5000000000000000 : ℝ) (823314455359273 / 500000000000000000 : ℝ) (66515247493461 / 2000000000000000 : ℝ)
    (cell12756 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · have h := gap_lower (n := 12756) (a := (41501450202401 / 50000000000000 : ℝ)) (b := (80734350711 / 50000000000000 : ℝ)) (q := (1122386706883 / 50000000000000 : ℝ))
      (E := (cell12756 ⟨31, by decide⟩).energy) (xi := (66515247493461 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12756 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12756]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12756])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12756) (a := (41501450202401 / 50000000000000 : ℝ)) (b := (80734350711 / 50000000000000 : ℝ)) (q := (1122386706883 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12756])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12756])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12756]

theorem cert12756_32 : CellCertificate 12756 (442566342293287 / 5000000000000000 : ℝ) (823314455359273 / 500000000000000000 : ℝ) (66515247493461 / 2000000000000000 : ℝ)
    (cell12756 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · have h := gap_lower (n := 12756) (a := (20742174831631 / 25000000000000 : ℝ)) (b := (80734350711 / 50000000000000 : ℝ)) (q := (1122388726867 / 50000000000000 : ℝ))
      (E := (cell12756 ⟨32, by decide⟩).energy) (xi := (66515247493461 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12756 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12756]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12756])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12756) (a := (20742174831631 / 25000000000000 : ℝ)) (b := (80734350711 / 50000000000000 : ℝ)) (q := (1122388726867 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12756])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12756])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12756]

theorem cert12756_33 : CellCertificate 12756 (442566342293287 / 5000000000000000 : ℝ) (823314455359273 / 500000000000000000 : ℝ) (66515247493461 / 2000000000000000 : ℝ)
    (cell12756 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · have h := gap_lower (n := 12756) (a := (41467261055683 / 50000000000000 : ℝ)) (b := (80734350711 / 50000000000000 : ℝ)) (q := (280597678021 / 12500000000000 : ℝ))
      (E := (cell12756 ⟨33, by decide⟩).energy) (xi := (66515247493461 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12756 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12756]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12756])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12756) (a := (41467261055683 / 50000000000000 : ℝ)) (b := (80734350711 / 50000000000000 : ℝ)) (q := (280597678021 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12756])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12756])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12756]

theorem cert12756_34 : CellCertificate 12756 (442566342293287 / 5000000000000000 : ℝ) (823314455359273 / 500000000000000000 : ℝ) (66515247493461 / 2000000000000000 : ℝ)
    (cell12756 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · have h := gap_lower (n := 12756) (a := (41450184364147 / 50000000000000 : ℝ)) (b := (80734350711 / 50000000000000 : ℝ)) (q := (448957088661 / 20000000000000 : ℝ))
      (E := (cell12756 ⟨34, by decide⟩).energy) (xi := (66515247493461 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12756 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12756]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12756])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12756) (a := (41450184364147 / 50000000000000 : ℝ)) (b := (80734350711 / 50000000000000 : ℝ)) (q := (448957088661 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12756])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12756])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12756]

theorem cert12756_35 : CellCertificate 12756 (442566342293287 / 5000000000000000 : ℝ) (823314455359273 / 500000000000000000 : ℝ) (66515247493461 / 2000000000000000 : ℝ)
    (cell12756 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · have h := gap_lower (n := 12756) (a := (82866239146431 / 100000000000000 : ℝ)) (b := (80734350711 / 50000000000000 : ℝ)) (q := (448957890689 / 20000000000000 : ℝ))
      (E := (cell12756 ⟨35, by decide⟩).energy) (xi := (66515247493461 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12756 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12756]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12756])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12756) (a := (82866239146431 / 100000000000000 : ℝ)) (b := (80734350711 / 50000000000000 : ℝ)) (q := (448957890689 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12756])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12756])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12756]

theorem cert12756_36 : CellCertificate 12756 (442566342293287 / 5000000000000000 : ℝ) (823314455359273 / 500000000000000000 : ℝ) (66515247493461 / 2000000000000000 : ℝ)
    (cell12756 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · have h := gap_lower (n := 12756) (a := (41416066667529 / 50000000000000 : ℝ)) (b := (80734350711 / 50000000000000 : ℝ)) (q := (2244793455223 / 100000000000000 : ℝ))
      (E := (cell12756 ⟨36, by decide⟩).energy) (xi := (66515247493461 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12756 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12756]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12756])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12756) (a := (41416066667529 / 50000000000000 : ℝ)) (b := (80734350711 / 50000000000000 : ℝ)) (q := (2244793455223 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12756])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12756])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12756]

theorem cert12756_37 : CellCertificate 12756 (442566342293287 / 5000000000000000 : ℝ) (823314455359273 / 500000000000000000 : ℝ) (66515247493461 / 2000000000000000 : ℝ)
    (cell12756 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · have h := gap_lower (n := 12756) (a := (82798051263609 / 100000000000000 : ℝ)) (b := (80734350711 / 50000000000000 : ℝ)) (q := (2244797449053 / 100000000000000 : ℝ))
      (E := (cell12756 ⟨37, by decide⟩).energy) (xi := (66515247493461 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12756 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12756]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12756])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12756) (a := (82798051263609 / 100000000000000 : ℝ)) (b := (80734350711 / 50000000000000 : ℝ)) (q := (2244797449053 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12756])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12756])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12756]

theorem cert12756_38 : CellCertificate 12756 (442566342293287 / 5000000000000000 : ℝ) (823314455359273 / 500000000000000000 : ℝ) (66515247493461 / 2000000000000000 : ℝ)
    (cell12756 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · have h := gap_lower (n := 12756) (a := (82763992901677 / 100000000000000 : ℝ)) (b := (80734350711 / 50000000000000 : ℝ)) (q := (2244801493829 / 100000000000000 : ℝ))
      (E := (cell12756 ⟨38, by decide⟩).energy) (xi := (66515247493461 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12756 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12756]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12756])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12756) (a := (82763992901677 / 100000000000000 : ℝ)) (b := (80734350711 / 50000000000000 : ℝ)) (q := (2244801493829 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12756])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12756])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12756]

theorem cert12756_39 : CellCertificate 12756 (442566342293287 / 5000000000000000 : ℝ) (823314455359273 / 500000000000000000 : ℝ) (66515247493461 / 2000000000000000 : ℝ)
    (cell12756 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · have h := gap_lower (n := 12756) (a := (41364979109503 / 50000000000000 : ℝ)) (b := (80734350711 / 50000000000000 : ℝ)) (q := (561201368033 / 25000000000000 : ℝ))
      (E := (cell12756 ⟨39, by decide⟩).energy) (xi := (66515247493461 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12756 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12756]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12756])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12756) (a := (41364979109503 / 50000000000000 : ℝ)) (b := (80734350711 / 50000000000000 : ℝ)) (q := (561201368033 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12756])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12756])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12756]

theorem cert12757_20 : CellCertificate 12757 (6914882694729 / 78125000000000 : ℝ) (1646499791968917 / 1000000000000000000 : ℝ) (83137384364159 / 2500000000000000 : ℝ)
    (cell12757 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · have h := gap_lower (n := 12757) (a := (833806875463 / 1000000000000 : ℝ)) (b := (32291178249 / 20000000000000 : ℝ)) (q := (1122304273331 / 50000000000000 : ℝ))
      (E := (cell12757 ⟨20, by decide⟩).energy) (xi := (83137384364159 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12757 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12757]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12757])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12757) (a := (833806875463 / 1000000000000 : ℝ)) (b := (32291178249 / 20000000000000 : ℝ)) (q := (1122304273331 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12757])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12757])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12757]

theorem cert12757_21 : CellCertificate 12757 (6914882694729 / 78125000000000 : ℝ) (1646499791968917 / 1000000000000000000 : ℝ) (83137384364159 / 2500000000000000 : ℝ)
    (cell12757 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · have h := gap_lower (n := 12757) (a := (20836555547109 / 25000000000000 : ℝ)) (b := (32291178249 / 20000000000000 : ℝ)) (q := (448922507391 / 20000000000000 : ℝ))
      (E := (cell12757 ⟨21, by decide⟩).energy) (xi := (83137384364159 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12757 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12757]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12757])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12757) (a := (20836555547109 / 25000000000000 : ℝ)) (b := (32291178249 / 20000000000000 : ℝ)) (q := (448922507391 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12757])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12757])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12757]

theorem cert12757_22 : CellCertificate 12757 (6914882694729 / 78125000000000 : ℝ) (1646499791968917 / 1000000000000000000 : ℝ) (83137384364159 / 2500000000000000 : ℝ)
    (cell12757 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · have h := gap_lower (n := 12757) (a := (41655890522663 / 50000000000000 : ℝ)) (b := (32291178249 / 20000000000000 : ℝ)) (q := (1122308273993 / 50000000000000 : ℝ))
      (E := (cell12757 ⟨22, by decide⟩).energy) (xi := (83137384364159 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12757 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12757]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12757])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12757) (a := (41655890522663 / 50000000000000 : ℝ)) (b := (32291178249 / 20000000000000 : ℝ)) (q := (1122308273993 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12757])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12757])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12757]

theorem cert12757_23 : CellCertificate 12757 (6914882694729 / 78125000000000 : ℝ) (1646499791968917 / 1000000000000000000 : ℝ) (83137384364159 / 2500000000000000 : ℝ)
    (cell12757 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · have h := gap_lower (n := 12757) (a := (41638682042069 / 50000000000000 : ℝ)) (b := (32291178249 / 20000000000000 : ℝ)) (q := (2244620525101 / 100000000000000 : ℝ))
      (E := (cell12757 ⟨23, by decide⟩).energy) (xi := (83137384364159 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12757 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12757]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12757])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12757) (a := (41638682042069 / 50000000000000 : ℝ)) (b := (32291178249 / 20000000000000 : ℝ)) (q := (2244620525101 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12757])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12757])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12757]

theorem cert12757_24 : CellCertificate 12757 (6914882694729 / 78125000000000 : ℝ) (1646499791968917 / 1000000000000000000 : ℝ) (83137384364159 / 2500000000000000 : ℝ)
    (cell12757 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · have h := gap_lower (n := 12757) (a := (41621485636103 / 50000000000000 : ℝ)) (b := (32291178249 / 20000000000000 : ℝ)) (q := (2244624530073 / 100000000000000 : ℝ))
      (E := (cell12757 ⟨24, by decide⟩).energy) (xi := (83137384364159 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12757 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12757]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12757])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12757) (a := (41621485636103 / 50000000000000 : ℝ)) (b := (32291178249 / 20000000000000 : ℝ)) (q := (2244624530073 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12757])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12757])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12757]

theorem cert12757_25 : CellCertificate 12757 (6914882694729 / 78125000000000 : ℝ) (1646499791968917 / 1000000000000000000 : ℝ) (83137384364159 / 2500000000000000 : ℝ)
    (cell12757 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · have h := gap_lower (n := 12757) (a := (83208602577033 / 100000000000000 : ℝ)) (b := (32291178249 / 20000000000000 : ℝ)) (q := (561157141533 / 25000000000000 : ℝ))
      (E := (cell12757 ⟨25, by decide⟩).energy) (xi := (83137384364159 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12757 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12757]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12757])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12757) (a := (83208602577033 / 100000000000000 : ℝ)) (b := (32291178249 / 20000000000000 : ℝ)) (q := (561157141533 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12757])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12757])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12757]

theorem cert12757_26 : CellCertificate 12757 (6914882694729 / 78125000000000 : ℝ) (1646499791968917 / 1000000000000000000 : ℝ) (83137384364159 / 2500000000000000 : ℝ)
    (cell12757 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · have h := gap_lower (n := 12757) (a := (8317425796629 / 10000000000000 : ℝ)) (b := (32291178249 / 20000000000000 : ℝ)) (q := (1122316288923 / 50000000000000 : ℝ))
      (E := (cell12757 ⟨26, by decide⟩).energy) (xi := (83137384364159 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12757 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12757]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12757])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12757) (a := (8317425796629 / 10000000000000 : ℝ)) (b := (32291178249 / 20000000000000 : ℝ)) (q := (1122316288923 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12757])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12757])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12757]

theorem cert12757_27 : CellCertificate 12757 (6914882694729 / 78125000000000 : ℝ) (1646499791968917 / 1000000000000000000 : ℝ) (83137384364159 / 2500000000000000 : ℝ)
    (cell12757 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · have h := gap_lower (n := 12757) (a := (20784984351953 / 25000000000000 : ℝ)) (b := (32291178249 / 20000000000000 : ℝ)) (q := (2244636567909 / 100000000000000 : ℝ))
      (E := (cell12757 ⟨27, by decide⟩).energy) (xi := (83137384364159 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12757 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12757]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12757])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12757) (a := (20784984351953 / 25000000000000 : ℝ)) (b := (32291178249 / 20000000000000 : ℝ)) (q := (2244636567909 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12757])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12757])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12757]

theorem cert12757_28 : CellCertificate 12757 (6914882694729 / 78125000000000 : ℝ) (1646499791968917 / 1000000000000000000 : ℝ) (83137384364159 / 2500000000000000 : ℝ)
    (cell12757 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · have h := gap_lower (n := 12757) (a := (83105640869599 / 100000000000000 : ℝ)) (b := (32291178249 / 20000000000000 : ℝ)) (q := (112232026939 / 5000000000000 : ℝ))
      (E := (cell12757 ⟨28, by decide⟩).energy) (xi := (83137384364159 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12757 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12757]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12757])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12757) (a := (83105640869599 / 100000000000000 : ℝ)) (b := (32291178249 / 20000000000000 : ℝ)) (q := (112232026939 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12757])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12757])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12757]

theorem cert12757_29 : CellCertificate 12757 (6914882694729 / 78125000000000 : ℝ) (1646499791968917 / 1000000000000000000 : ℝ) (83137384364159 / 2500000000000000 : ℝ)
    (cell12757 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · have h := gap_lower (n := 12757) (a := (41535684159907 / 50000000000000 : ℝ)) (b := (32291178249 / 20000000000000 : ℝ)) (q := (1122322275591 / 50000000000000 : ℝ))
      (E := (cell12757 ⟨29, by decide⟩).energy) (xi := (83137384364159 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12757 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12757]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12757])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12757) (a := (41535684159907 / 50000000000000 : ℝ)) (b := (32291178249 / 20000000000000 : ℝ)) (q := (1122322275591 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12757])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12757])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12757]

theorem cert12757_30 : CellCertificate 12757 (6914882694729 / 78125000000000 : ℝ) (1646499791968917 / 1000000000000000000 : ℝ) (83137384364159 / 2500000000000000 : ℝ)
    (cell12757 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · have h := gap_lower (n := 12757) (a := (1297454995731 / 1562500000000 : ℝ)) (b := (32291178249 / 20000000000000 : ℝ)) (q := (448929709733 / 20000000000000 : ℝ))
      (E := (cell12757 ⟨30, by decide⟩).energy) (xi := (83137384364159 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12757 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12757]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12757])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12757) (a := (1297454995731 / 1562500000000 : ℝ)) (b := (32291178249 / 20000000000000 : ℝ)) (q := (448929709733 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12757])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12757])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12757]

theorem cert12757_31 : CellCertificate 12757 (6914882694729 / 78125000000000 : ℝ) (1646499791968917 / 1000000000000000000 : ℝ) (83137384364159 / 2500000000000000 : ℝ)
    (cell12757 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · have h := gap_lower (n := 12757) (a := (83002895058997 / 100000000000000 : ℝ)) (b := (32291178249 / 20000000000000 : ℝ)) (q := (2244652591539 / 100000000000000 : ℝ))
      (E := (cell12757 ⟨31, by decide⟩).energy) (xi := (83137384364159 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12757 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12757]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12757])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12757) (a := (83002895058997 / 100000000000000 : ℝ)) (b := (32291178249 / 20000000000000 : ℝ)) (q := (2244652591539 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12757])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12757])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12757]

theorem cert12757_32 : CellCertificate 12757 (6914882694729 / 78125000000000 : ℝ) (1646499791968917 / 1000000000000000000 : ℝ) (83137384364159 / 2500000000000000 : ℝ)
    (cell12757 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · have h := gap_lower (n := 12757) (a := (829686942851 / 1000000000000 : ℝ)) (b := (32291178249 / 20000000000000 : ℝ)) (q := (448931312857 / 20000000000000 : ℝ))
      (E := (cell12757 ⟨32, by decide⟩).energy) (xi := (83137384364159 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12757 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12757]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12757])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12757) (a := (829686942851 / 1000000000000 : ℝ)) (b := (32291178249 / 20000000000000 : ℝ)) (q := (448931312857 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12757])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12757])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12757]

theorem cert12757_33 : CellCertificate 12757 (6914882694729 / 78125000000000 : ℝ) (1646499791968917 / 1000000000000000000 : ℝ) (83137384364159 / 2500000000000000 : ℝ)
    (cell12757 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · have h := gap_lower (n := 12757) (a := (82934517373901 / 100000000000000 : ℝ)) (b := (32291178249 / 20000000000000 : ℝ)) (q := (561165146331 / 25000000000000 : ℝ))
      (E := (cell12757 ⟨33, by decide⟩).energy) (xi := (83137384364159 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12757 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12757]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12757])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12757) (a := (82934517373901 / 100000000000000 : ℝ)) (b := (32291178249 / 20000000000000 : ℝ)) (q := (561165146331 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12757])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12757])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12757]

theorem cert12757_34 : CellCertificate 12757 (6914882694729 / 78125000000000 : ℝ) (1646499791968917 / 1000000000000000000 : ℝ) (83137384364159 / 2500000000000000 : ℝ)
    (cell12757 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · have h := gap_lower (n := 12757) (a := (2590636384199 / 3125000000000 : ℝ)) (b := (32291178249 / 20000000000000 : ℝ)) (q := (1122332298599 / 50000000000000 : ℝ))
      (E := (cell12757 ⟨34, by decide⟩).energy) (xi := (83137384364159 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12757 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12757]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12757])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12757) (a := (2590636384199 / 3125000000000 : ℝ)) (b := (32291178249 / 20000000000000 : ℝ)) (q := (1122332298599 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12757])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12757])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12757]

theorem cert12757_35 : CellCertificate 12757 (6914882694729 / 78125000000000 : ℝ) (1646499791968917 / 1000000000000000000 : ℝ) (83137384364159 / 2500000000000000 : ℝ)
    (cell12757 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · have h := gap_lower (n := 12757) (a := (10358279376953 / 12500000000000 : ℝ)) (b := (32291178249 / 20000000000000 : ℝ)) (q := (2244668600769 / 100000000000000 : ℝ))
      (E := (cell12757 ⟨35, by decide⟩).energy) (xi := (83137384364159 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12757 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12757]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12757])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12757) (a := (10358279376953 / 12500000000000 : ℝ)) (b := (32291178249 / 20000000000000 : ℝ)) (q := (2244668600769 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12757])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12757])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12757]

theorem cert12757_36 : CellCertificate 12757 (6914882694729 / 78125000000000 : ℝ) (1646499791968917 / 1000000000000000000 : ℝ) (83137384364159 / 2500000000000000 : ℝ)
    (cell12757 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · have h := gap_lower (n := 12757) (a := (1656642590139 / 2000000000000 : ℝ)) (b := (32291178249 / 20000000000000 : ℝ)) (q := (1122336298337 / 50000000000000 : ℝ))
      (E := (cell12757 ⟨36, by decide⟩).energy) (xi := (83137384364159 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12757 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12757]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12757])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12757) (a := (1656642590139 / 2000000000000 : ℝ)) (b := (32291178249 / 20000000000000 : ℝ)) (q := (1122336298337 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12757])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12757])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12757]

theorem cert12757_37 : CellCertificate 12757 (6914882694729 / 78125000000000 : ℝ) (1646499791968917 / 1000000000000000000 : ℝ) (83137384364159 / 2500000000000000 : ℝ)
    (cell12757 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · have h := gap_lower (n := 12757) (a := (82798047737783 / 100000000000000 : ℝ)) (b := (32291178249 / 20000000000000 : ℝ)) (q := (89787063413 / 4000000000000 : ℝ))
      (E := (cell12757 ⟨37, by decide⟩).energy) (xi := (83137384364159 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12757 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12757]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12757])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12757) (a := (82798047737783 / 100000000000000 : ℝ)) (b := (32291178249 / 20000000000000 : ℝ)) (q := (89787063413 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12757])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12757])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12757]

theorem cert12757_38 : CellCertificate 12757 (6914882694729 / 78125000000000 : ℝ) (1646499791968917 / 1000000000000000000 : ℝ) (83137384364159 / 2500000000000000 : ℝ)
    (cell12757 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · have h := gap_lower (n := 12757) (a := (41381994838857 / 50000000000000 : ℝ)) (b := (32291178249 / 20000000000000 : ℝ)) (q := (140292539101 / 6250000000000 : ℝ))
      (E := (cell12757 ⟨38, by decide⟩).energy) (xi := (83137384364159 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12757 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12757]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12757])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12757) (a := (41381994838857 / 50000000000000 : ℝ)) (b := (32291178249 / 20000000000000 : ℝ)) (q := (140292539101 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12757])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12757])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12757]

theorem cert12757_39 : CellCertificate 12757 (6914882694729 / 78125000000000 : ℝ) (1646499791968917 / 1000000000000000000 : ℝ) (83137384364159 / 2500000000000000 : ℝ)
    (cell12757 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · have h := gap_lower (n := 12757) (a := (10341244412061 / 12500000000000 : ℝ)) (b := (32291178249 / 20000000000000 : ℝ)) (q := (35073196877 / 1562500000000 : ℝ))
      (E := (cell12757 ⟨39, by decide⟩).energy) (xi := (83137384364159 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12757 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12757]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12757])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12757) (a := (10341244412061 / 12500000000000 : ℝ)) (b := (32291178249 / 20000000000000 : ℝ)) (q := (35073196877 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12757])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12757])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12757]

theorem cert12758_20 : CellCertificate 12758 (442538644715769 / 5000000000000000 : ℝ) (411592673366783 / 250000000000000000 : ℝ) (332522841787239 / 10000000000000000 : ℝ)
    (cell12758 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · have h := gap_lower (n := 12758) (a := (83380678825837 / 100000000000000 : ℝ)) (b := (80721541557 / 50000000000000 : ℝ)) (q := (448897537437 / 20000000000000 : ℝ))
      (E := (cell12758 ⟨20, by decide⟩).energy) (xi := (332522841787239 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12758 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12758]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12758])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12758) (a := (83380678825837 / 100000000000000 : ℝ)) (b := (80721541557 / 50000000000000 : ℝ)) (q := (448897537437 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12758])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12758])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12758]

theorem cert12758_21 : CellCertificate 12758 (442538644715769 / 5000000000000000 : ℝ) (411592673366783 / 250000000000000000 : ℝ) (332522841787239 / 10000000000000000 : ℝ)
    (cell12758 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · have h := gap_lower (n := 12758) (a := (83346213777009 / 100000000000000 : ℝ)) (b := (80721541557 / 50000000000000 : ℝ)) (q := (2244491719373 / 100000000000000 : ℝ))
      (E := (cell12758 ⟨21, by decide⟩).energy) (xi := (332522841787239 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12758 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12758]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12758])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12758) (a := (83346213777009 / 100000000000000 : ℝ)) (b := (80721541557 / 50000000000000 : ℝ)) (q := (2244491719373 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12758])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12758])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12758]

theorem cert12758_22 : CellCertificate 12758 (442538644715769 / 5000000000000000 : ℝ) (411592673366783 / 250000000000000000 : ℝ) (332522841787239 / 10000000000000000 : ℝ)
    (cell12758 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · have h := gap_lower (n := 12758) (a := (10413971617813 / 12500000000000 : ℝ)) (b := (80721541557 / 50000000000000 : ℝ)) (q := (2244495714721 / 100000000000000 : ℝ))
      (E := (cell12758 ⟨22, by decide⟩).energy) (xi := (332522841787239 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12758 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12758]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12758])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12758) (a := (10413971617813 / 12500000000000 : ℝ)) (b := (80721541557 / 50000000000000 : ℝ)) (q := (2244495714721 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12758])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12758])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12758]

theorem cert12758_23 : CellCertificate 12758 (442538644715769 / 5000000000000000 : ℝ) (411592673366783 / 250000000000000000 : ℝ) (332522841787239 / 10000000000000000 : ℝ)
    (cell12758 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · have h := gap_lower (n := 12758) (a := (83277356289491 / 100000000000000 : ℝ)) (b := (80721541557 / 50000000000000 : ℝ)) (q := (1122249867607 / 50000000000000 : ℝ))
      (E := (cell12758 ⟨23, by decide⟩).energy) (xi := (332522841787239 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12758 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12758]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12758])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12758) (a := (83277356289491 / 100000000000000 : ℝ)) (b := (80721541557 / 50000000000000 : ℝ)) (q := (1122249867607 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12758])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12758])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12758]

theorem cert12758_24 : CellCertificate 12758 (442538644715769 / 5000000000000000 : ℝ) (411592673366783 / 250000000000000000 : ℝ) (332522841787239 / 10000000000000000 : ℝ)
    (cell12758 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · have h := gap_lower (n := 12758) (a := (16648592757061 / 20000000000000 : ℝ)) (b := (80721541557 / 50000000000000 : ℝ)) (q := (2244503725937 / 100000000000000 : ℝ))
      (E := (cell12758 ⟨24, by decide⟩).energy) (xi := (332522841787239 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12758 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12758]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12758])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12758) (a := (16648592757061 / 20000000000000 : ℝ)) (b := (80721541557 / 50000000000000 : ℝ)) (q := (2244503725937 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12758])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12758])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12758]

theorem cert12758_25 : CellCertificate 12758 (442538644715769 / 5000000000000000 : ℝ) (411592673366783 / 250000000000000000 : ℝ) (332522841787239 / 10000000000000000 : ℝ)
    (cell12758 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · have h := gap_lower (n := 12758) (a := (83208595397451 / 100000000000000 : ℝ)) (b := (80721541557 / 50000000000000 : ℝ)) (q := (2244507748449 / 100000000000000 : ℝ))
      (E := (cell12758 ⟨25, by decide⟩).energy) (xi := (332522841787239 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12758 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12758]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12758])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12758) (a := (83208595397451 / 100000000000000 : ℝ)) (b := (80721541557 / 50000000000000 : ℝ)) (q := (2244507748449 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12758])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12758])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12758]

theorem cert12758_26 : CellCertificate 12758 (442538644715769 / 5000000000000000 : ℝ) (411592673366783 / 250000000000000000 : ℝ) (332522841787239 / 10000000000000000 : ℝ)
    (cell12758 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · have h := gap_lower (n := 12758) (a := (83174251093599 / 100000000000000 : ℝ)) (b := (80721541557 / 50000000000000 : ℝ)) (q := (56112793683 / 2500000000000 : ℝ))
      (E := (cell12758 ⟨26, by decide⟩).energy) (xi := (332522841787239 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12758 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12758]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12758])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12758) (a := (83174251093599 / 100000000000000 : ℝ)) (b := (80721541557 / 50000000000000 : ℝ)) (q := (56112793683 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12758])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12758])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12758]

theorem cert12758_27 : CellCertificate 12758 (442538644715769 / 5000000000000000 : ℝ) (411592673366783 / 250000000000000000 : ℝ) (332522841787239 / 10000000000000000 : ℝ)
    (cell12758 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · have h := gap_lower (n := 12758) (a := (16627986168317 / 20000000000000 : ℝ)) (b := (80721541557 / 50000000000000 : ℝ)) (q := (1122257862621 / 50000000000000 : ℝ))
      (E := (cell12758 ⟨27, by decide⟩).energy) (xi := (332522841787239 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12758 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12758]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12758])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12758) (a := (16627986168317 / 20000000000000 : ℝ)) (b := (80721541557 / 50000000000000 : ℝ)) (q := (1122257862621 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12758])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12758])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12758]

theorem cert12758_28 : CellCertificate 12758 (442538644715769 / 5000000000000000 : ℝ) (411592673366783 / 250000000000000000 : ℝ) (332522841787239 / 10000000000000000 : ℝ)
    (cell12758 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · have h := gap_lower (n := 12758) (a := (83105634609411 / 100000000000000 : ℝ)) (b := (80721541557 / 50000000000000 : ℝ)) (q := (280564967893 / 12500000000000 : ℝ))
      (E := (cell12758 ⟨28, by decide⟩).energy) (xi := (332522841787239 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12758 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12758]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12758])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12758) (a := (83105634609411 / 100000000000000 : ℝ)) (b := (80721541557 / 50000000000000 : ℝ)) (q := (280564967893 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12758])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12758])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12758]

theorem cert12758_29 : CellCertificate 12758 (442538644715769 / 5000000000000000 : ℝ) (411592673366783 / 250000000000000000 : ℝ) (332522841787239 / 10000000000000000 : ℝ)
    (cell12758 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · have h := gap_lower (n := 12758) (a := (2076784059131 / 2500000000000 : ℝ)) (b := (80721541557 / 50000000000000 : ℝ)) (q := (224452374483 / 10000000000000 : ℝ))
      (E := (cell12758 ⟨29, by decide⟩).energy) (xi := (332522841787239 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12758 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12758]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12758])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12758) (a := (2076784059131 / 2500000000000 : ℝ)) (b := (80721541557 / 50000000000000 : ℝ)) (q := (224452374483 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12758])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12758])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12758]

theorem cert12758_30 : CellCertificate 12758 (442538644715769 / 5000000000000000 : ℝ) (411592673366783 / 250000000000000000 : ℝ) (332522841787239 / 10000000000000000 : ℝ)
    (cell12758 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · have h := gap_lower (n := 12758) (a := (415185570387 / 500000000000 : ℝ)) (b := (80721541557 / 50000000000000 : ℝ)) (q := (280565966537 / 12500000000000 : ℝ))
      (E := (cell12758 ⟨30, by decide⟩).energy) (xi := (332522841787239 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12758 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12758]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12758])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12758) (a := (415185570387 / 500000000000 : ℝ)) (b := (80721541557 / 50000000000000 : ℝ)) (q := (280565966537 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12758])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12758])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12758]

theorem cert12758_31 : CellCertificate 12758 (442538644715769 / 5000000000000000 : ℝ) (411592673366783 / 250000000000000000 : ℝ) (332522841787239 / 10000000000000000 : ℝ)
    (cell12758 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · have h := gap_lower (n := 12758) (a := (83002889714379 / 100000000000000 : ℝ)) (b := (80721541557 / 50000000000000 : ℝ)) (q := (2244531765853 / 100000000000000 : ℝ))
      (E := (cell12758 ⟨31, by decide⟩).energy) (xi := (332522841787239 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12758 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12758]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12758])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12758) (a := (83002889714379 / 100000000000000 : ℝ)) (b := (80721541557 / 50000000000000 : ℝ)) (q := (2244531765853 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12758])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12758])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12758]

theorem cert12758_32 : CellCertificate 12758 (442538644715769 / 5000000000000000 : ℝ) (411592673366783 / 250000000000000000 : ℝ) (332522841787239 / 10000000000000000 : ℝ)
    (cell12758 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · have h := gap_lower (n := 12758) (a := (41484344622413 / 50000000000000 : ℝ)) (b := (80721541557 / 50000000000000 : ℝ)) (q := (2244535729979 / 100000000000000 : ℝ))
      (E := (cell12758 ⟨32, by decide⟩).energy) (xi := (332522841787239 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12758 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12758]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12758])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12758) (a := (41484344622413 / 50000000000000 : ℝ)) (b := (80721541557 / 50000000000000 : ℝ)) (q := (2244535729979 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12758])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12758])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12758]

theorem cert12758_33 : CellCertificate 12758 (442538644715769 / 5000000000000000 : ℝ) (411592673366783 / 250000000000000000 : ℝ) (332522841787239 / 10000000000000000 : ℝ)
    (cell12758 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · have h := gap_lower (n := 12758) (a := (1658690252751 / 2000000000000 : ℝ)) (b := (80721541557 / 50000000000000 : ℝ)) (q := (448907948619 / 20000000000000 : ℝ))
      (E := (cell12758 ⟨33, by decide⟩).energy) (xi := (332522841787239 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12758 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12758]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12758])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12758) (a := (1658690252751 / 2000000000000 : ℝ)) (b := (80721541557 / 50000000000000 : ℝ)) (q := (448907948619 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12758])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12758])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12758]

theorem cert12758_34 : CellCertificate 12758 (442538644715769 / 5000000000000000 : ℝ) (411592673366783 / 250000000000000000 : ℝ) (332522841787239 / 10000000000000000 : ℝ)
    (cell12758 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · have h := gap_lower (n := 12758) (a := (82900359861519 / 100000000000000 : ℝ)) (b := (80721541557 / 50000000000000 : ℝ)) (q := (2244543747743 / 100000000000000 : ℝ))
      (E := (cell12758 ⟨34, by decide⟩).energy) (xi := (332522841787239 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12758 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12758]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12758])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12758) (a := (82900359861519 / 100000000000000 : ℝ)) (b := (80721541557 / 50000000000000 : ℝ)) (q := (2244543747743 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12758])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12758])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12758]

theorem cert12758_35 : CellCertificate 12758 (442538644715769 / 5000000000000000 : ℝ) (411592673366783 / 250000000000000000 : ℝ) (332522841787239 / 10000000000000000 : ℝ)
    (cell12758 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · have h := gap_lower (n := 12758) (a := (82866230885857 / 100000000000000 : ℝ)) (b := (80721541557 / 50000000000000 : ℝ)) (q := (448909548957 / 20000000000000 : ℝ))
      (E := (cell12758 ⟨35, by decide⟩).energy) (xi := (332522841787239 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12758 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12758]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12758])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12758) (a := (82866230885857 / 100000000000000 : ℝ)) (b := (80721541557 / 50000000000000 : ℝ)) (q := (448909548957 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12758])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12758])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12758]

theorem cert12758_36 : CellCertificate 12758 (442538644715769 / 5000000000000000 : ℝ) (411592673366783 / 250000000000000000 : ℝ) (332522841787239 / 10000000000000000 : ℝ)
    (cell12758 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · have h := gap_lower (n := 12758) (a := (16566425135969 / 20000000000000 : ℝ)) (b := (80721541557 / 50000000000000 : ℝ)) (q := (448910358703 / 20000000000000 : ℝ))
      (E := (cell12758 ⟨36, by decide⟩).energy) (xi := (332522841787239 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12758 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12758]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12758])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12758) (a := (16566425135969 / 20000000000000 : ℝ)) (b := (80721541557 / 50000000000000 : ℝ)) (q := (448910358703 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12758])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12758])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12758]

theorem cert12758_37 : CellCertificate 12758 (442538644715769 / 5000000000000000 : ℝ) (411592673366783 / 250000000000000000 : ℝ) (332522841787239 / 10000000000000000 : ℝ)
    (cell12758 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · have h := gap_lower (n := 12758) (a := (82798044212923 / 100000000000000 : ℝ)) (b := (80721541557 / 50000000000000 : ℝ)) (q := (2244555777047 / 100000000000000 : ℝ))
      (E := (cell12758 ⟨37, by decide⟩).energy) (xi := (332522841787239 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12758 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12758]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12758])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12758) (a := (82798044212923 / 100000000000000 : ℝ)) (b := (80721541557 / 50000000000000 : ℝ)) (q := (2244555777047 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12758])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12758])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12758]

theorem cert12758_38 : CellCertificate 12758 (442538644715769 / 5000000000000000 : ℝ) (411592673366783 / 250000000000000000 : ℝ) (332522841787239 / 10000000000000000 : ℝ)
    (cell12758 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · have h := gap_lower (n := 12758) (a := (82763986454681 / 100000000000000 : ℝ)) (b := (80721541557 / 50000000000000 : ℝ)) (q := (70142492319 / 3125000000000 : ℝ))
      (E := (cell12758 ⟨38, by decide⟩).energy) (xi := (332522841787239 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12758 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12758]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12758])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12758) (a := (82763986454681 / 100000000000000 : ℝ)) (b := (80721541557 / 50000000000000 : ℝ)) (q := (70142492319 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12758])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12758])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12758]

theorem cert12758_39 : CellCertificate 12758 (442538644715769 / 5000000000000000 : ℝ) (411592673366783 / 250000000000000000 : ℝ) (332522841787239 / 10000000000000000 : ℝ)
    (cell12758 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · have h := gap_lower (n := 12758) (a := (16545990474973 / 20000000000000 : ℝ)) (b := (80721541557 / 50000000000000 : ℝ)) (q := (448912756739 / 20000000000000 : ℝ))
      (E := (cell12758 ⟨39, by decide⟩).energy) (xi := (332522841787239 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12758 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12758]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12758])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12758) (a := (16545990474973 / 20000000000000 : ℝ)) (b := (80721541557 / 50000000000000 : ℝ)) (q := (448912756739 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12758])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12758])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12758]

theorem cert12759_20 : CellCertificate 12759 (442524799052133 / 5000000000000000 : ℝ) (1646241615208429 / 1000000000000000000 : ℝ) (332496150457969 / 10000000000000000 : ℝ)
    (cell12759 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · have h := gap_lower (n := 12759) (a := (10422583763371 / 12500000000000 : ℝ)) (b := (40357569257 / 25000000000000 : ℝ)) (q := (2244366940401 / 100000000000000 : ℝ))
      (E := (cell12759 ⟨20, by decide⟩).energy) (xi := (332496150457969 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12759 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12759]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12759])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12759) (a := (10422583763371 / 12500000000000 : ℝ)) (b := (40357569257 / 25000000000000 : ℝ)) (q := (2244366940401 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12759])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12759])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12759]

theorem cert12759_21 : CellCertificate 12759 (442524799052133 / 5000000000000000 : ℝ) (1646241615208429 / 1000000000000000000 : ℝ) (332496150457969 / 10000000000000000 : ℝ)
    (cell12759 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · have h := gap_lower (n := 12759) (a := (83346205367139 / 100000000000000 : ℝ)) (b := (40357569257 / 25000000000000 : ℝ)) (q := (1122185448977 / 50000000000000 : ℝ))
      (E := (cell12759 ⟨21, by decide⟩).energy) (xi := (332496150457969 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12759 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12759]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12759])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12759) (a := (83346205367139 / 100000000000000 : ℝ)) (b := (40357569257 / 25000000000000 : ℝ)) (q := (1122185448977 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12759])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12759])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12759]

theorem cert12759_22 : CellCertificate 12759 (442524799052133 / 5000000000000000 : ℝ) (1646241615208429 / 1000000000000000000 : ℝ) (332496150457969 / 10000000000000000 : ℝ)
    (cell12759 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · have h := gap_lower (n := 12759) (a := (41655882420601 / 50000000000000 : ℝ)) (b := (40357569257 / 25000000000000 : ℝ)) (q := (2244374935989 / 100000000000000 : ℝ))
      (E := (cell12759 ⟨22, by decide⟩).energy) (xi := (332496150457969 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12759 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12759]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12759])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12759) (a := (41655882420601 / 50000000000000 : ℝ)) (b := (40357569257 / 25000000000000 : ℝ)) (q := (2244374935989 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12759])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12759])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12759]

theorem cert12759_23 : CellCertificate 12759 (442524799052133 / 5000000000000000 : ℝ) (1646241615208429 / 1000000000000000000 : ℝ) (332496150457969 / 10000000000000000 : ℝ)
    (cell12759 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · have h := gap_lower (n := 12759) (a := (83277348496327 / 100000000000000 : ℝ)) (b := (40357569257 / 25000000000000 : ℝ)) (q := (448875788313 / 20000000000000 : ℝ))
      (E := (cell12759 ⟨23, by decide⟩).energy) (xi := (332496150457969 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12759 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12759]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12759])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12759) (a := (83277348496327 / 100000000000000 : ℝ)) (b := (40357569257 / 25000000000000 : ℝ)) (q := (448875788313 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12759])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12759])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12759]

theorem cert12759_24 : CellCertificate 12759 (442524799052133 / 5000000000000000 : ℝ) (1646241615208429 / 1000000000000000000 : ℝ) (332496150457969 / 10000000000000000 : ℝ)
    (cell12759 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · have h := gap_lower (n := 12759) (a := (1664859125997 / 2000000000000 : ℝ)) (b := (40357569257 / 25000000000000 : ℝ)) (q := (2244382918077 / 100000000000000 : ℝ))
      (E := (cell12759 ⟨24, by decide⟩).energy) (xi := (332496150457969 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12759 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12759]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12759])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12759) (a := (1664859125997 / 2000000000000 : ℝ)) (b := (40357569257 / 25000000000000 : ℝ)) (q := (2244382918077 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12759])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12759])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12759]

theorem cert12759_25 : CellCertificate 12759 (442524799052133 / 5000000000000000 : ℝ) (1646241615208429 / 1000000000000000000 : ℝ) (332496150457969 / 10000000000000000 : ℝ)
    (cell12759 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · have h := gap_lower (n := 12759) (a := (83208588219277 / 100000000000000 : ℝ)) (b := (40357569257 / 25000000000000 : ℝ)) (q := (2244386927081 / 100000000000000 : ℝ))
      (E := (cell12759 ⟨25, by decide⟩).energy) (xi := (332496150457969 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12759 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12759]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12759])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12759) (a := (83208588219277 / 100000000000000 : ℝ)) (b := (40357569257 / 25000000000000 : ℝ)) (q := (2244386927081 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12759])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12759])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12759]

theorem cert12759_26 : CellCertificate 12759 (442524799052133 / 5000000000000000 : ℝ) (1646241615208429 / 1000000000000000000 : ℝ) (332496150457969 / 10000000000000000 : ℝ)
    (cell12759 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · have h := gap_lower (n := 12759) (a := (41587122111139 / 50000000000000 : ℝ)) (b := (40357569257 / 25000000000000 : ℝ)) (q := (561097728287 / 25000000000000 : ℝ))
      (E := (cell12759 ⟨26, by decide⟩).energy) (xi := (332496150457969 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12759 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12759]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12759])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12759) (a := (41587122111139 / 50000000000000 : ℝ)) (b := (40357569257 / 25000000000000 : ℝ)) (q := (561097728287 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12759])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12759])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12759]

theorem cert12759_27 : CellCertificate 12759 (442524799052133 / 5000000000000000 : ℝ) (1646241615208429 / 1000000000000000000 : ℝ) (332496150457969 / 10000000000000000 : ℝ)
    (cell12759 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · have h := gap_lower (n := 12759) (a := (20784981069173 / 25000000000000 : ℝ)) (b := (40357569257 / 25000000000000 : ℝ)) (q := (1122197468707 / 50000000000000 : ℝ))
      (E := (cell12759 ⟨27, by decide⟩).energy) (xi := (332496150457969 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12759 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12759]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12759])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12759) (a := (20784981069173 / 25000000000000 : ℝ)) (b := (40357569257 / 25000000000000 : ℝ)) (q := (1122197468707 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12759])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12759])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12759]

theorem cert12759_28 : CellCertificate 12759 (442524799052133 / 5000000000000000 : ℝ) (1646241615208429 / 1000000000000000000 : ℝ) (332496150457969 / 10000000000000000 : ℝ)
    (cell12759 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · have h := gap_lower (n := 12759) (a := (83105628350519 / 100000000000000 : ℝ)) (b := (40357569257 / 25000000000000 : ℝ)) (q := (1122199471969 / 50000000000000 : ℝ))
      (E := (cell12759 ⟨28, by decide⟩).energy) (xi := (332496150457969 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12759 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12759]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12759])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12759) (a := (83105628350519 / 100000000000000 : ℝ)) (b := (40357569257 / 25000000000000 : ℝ)) (q := (1122199471969 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12759])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12759])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12759]

theorem cert12759_29 : CellCertificate 12759 (442524799052133 / 5000000000000000 : ℝ) (1646241615208429 / 1000000000000000000 : ℝ) (332496150457969 / 10000000000000000 : ℝ)
    (cell12759 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · have h := gap_lower (n := 12759) (a := (3322854256477 / 4000000000000 : ℝ)) (b := (40357569257 / 25000000000000 : ℝ)) (q := (1122201467473 / 50000000000000 : ℝ))
      (E := (cell12759 ⟨29, by decide⟩).energy) (xi := (332496150457969 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12759 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12759]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12759])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12759) (a := (3322854256477 / 4000000000000 : ℝ)) (b := (40357569257 / 25000000000000 : ℝ)) (q := (1122201467473 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12759])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12759])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12759]

theorem cert12759_30 : CellCertificate 12759 (442524799052133 / 5000000000000000 : ℝ) (1646241615208429 / 1000000000000000000 : ℝ) (332496150457969 / 10000000000000000 : ℝ)
    (cell12759 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · have h := gap_lower (n := 12759) (a := (41518554214619 / 50000000000000 : ℝ)) (b := (40357569257 / 25000000000000 : ℝ)) (q := (2244406970951 / 100000000000000 : ℝ))
      (E := (cell12759 ⟨30, by decide⟩).energy) (xi := (332496150457969 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12759 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12759]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12759])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12759) (a := (41518554214619 / 50000000000000 : ℝ)) (b := (40357569257 / 25000000000000 : ℝ)) (q := (2244406970951 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12759])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12759])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12759]

theorem cert12759_31 : CellCertificate 12759 (442524799052133 / 5000000000000000 : ℝ) (1646241615208429 / 1000000000000000000 : ℝ) (332496150457969 / 10000000000000000 : ℝ)
    (cell12759 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · have h := gap_lower (n := 12759) (a := (83002884370947 / 100000000000000 : ℝ)) (b := (40357569257 / 25000000000000 : ℝ)) (q := (2244410936709 / 100000000000000 : ℝ))
      (E := (cell12759 ⟨31, by decide⟩).energy) (xi := (332496150457969 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12759 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12759]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12759])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12759) (a := (83002884370947 / 100000000000000 : ℝ)) (b := (40357569257 / 25000000000000 : ℝ)) (q := (2244410936709 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12759])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12759])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12759]

theorem cert12759_32 : CellCertificate 12759 (442524799052133 / 5000000000000000 : ℝ) (1646241615208429 / 1000000000000000000 : ℝ) (332496150457969 / 10000000000000000 : ℝ)
    (cell12759 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · have h := gap_lower (n := 12759) (a := (41484342102851 / 50000000000000 : ℝ)) (b := (40357569257 / 25000000000000 : ℝ)) (q := (2244414950819 / 100000000000000 : ℝ))
      (E := (cell12759 ⟨32, by decide⟩).energy) (xi := (332496150457969 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12759 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12759]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12759])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12759) (a := (41484342102851 / 50000000000000 : ℝ)) (b := (40357569257 / 25000000000000 : ℝ)) (q := (2244414950819 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12759])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12759])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12759]

theorem cert12759_33 : CellCertificate 12759 (442524799052133 / 5000000000000000 : ℝ) (1646241615208429 / 1000000000000000000 : ℝ) (332496150457969 / 10000000000000000 : ℝ)
    (cell12759 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · have h := gap_lower (n := 12759) (a := (10366813487789 / 12500000000000 : ℝ)) (b := (40357569257 / 25000000000000 : ℝ)) (q := (2244418956073 / 100000000000000 : ℝ))
      (E := (cell12759 ⟨33, by decide⟩).energy) (xi := (332496150457969 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12759 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12759]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12759])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12759) (a := (10366813487789 / 12500000000000 : ℝ)) (b := (40357569257 / 25000000000000 : ℝ)) (q := (2244418956073 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12759])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12759])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12759]

theorem cert12759_34 : CellCertificate 12759 (442524799052133 / 5000000000000000 : ℝ) (1646241615208429 / 1000000000000000000 : ℝ) (332496150457969 / 10000000000000000 : ℝ)
    (cell12759 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · have h := gap_lower (n := 12759) (a := (41450177714873 / 50000000000000 : ℝ)) (b := (40357569257 / 25000000000000 : ℝ)) (q := (2244422953557 / 100000000000000 : ℝ))
      (E := (cell12759 ⟨34, by decide⟩).energy) (xi := (332496150457969 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12759 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12759]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12759])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12759) (a := (41450177714873 / 50000000000000 : ℝ)) (b := (40357569257 / 25000000000000 : ℝ)) (q := (2244422953557 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12759])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12759])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12759]

theorem cert12759_35 : CellCertificate 12759 (442524799052133 / 5000000000000000 : ℝ) (1646241615208429 / 1000000000000000000 : ℝ) (332496150457969 / 10000000000000000 : ℝ)
    (cell12759 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · have h := gap_lower (n := 12759) (a := (82866226757129 / 100000000000000 : ℝ)) (b := (40357569257 / 25000000000000 : ℝ)) (q := (2244426944129 / 100000000000000 : ℝ))
      (E := (cell12759 ⟨35, by decide⟩).energy) (xi := (332496150457969 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12759 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12759]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12759])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12759) (a := (82866226757129 / 100000000000000 : ℝ)) (b := (40357569257 / 25000000000000 : ℝ)) (q := (2244426944129 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12759])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12759])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12759]

theorem cert12759_36 : CellCertificate 12759 (442524799052133 / 5000000000000000 : ℝ) (1646241615208429 / 1000000000000000000 : ℝ) (332496150457969 / 10000000000000000 : ℝ)
    (cell12759 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · have h := gap_lower (n := 12759) (a := (5177007615859 / 6250000000000 : ℝ)) (b := (40357569257 / 25000000000000 : ℝ)) (q := (561107746771 / 25000000000000 : ℝ))
      (E := (cell12759 ⟨36, by decide⟩).energy) (xi := (332496150457969 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12759 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12759]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12759])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12759) (a := (5177007615859 / 6250000000000 : ℝ)) (b := (40357569257 / 25000000000000 : ℝ)) (q := (561107746771 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12759])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12759])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12759]

theorem cert12759_37 : CellCertificate 12759 (442524799052133 / 5000000000000000 : ℝ) (1646241615208429 / 1000000000000000000 : ℝ) (332496150457969 / 10000000000000000 : ℝ)
    (cell12759 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · have h := gap_lower (n := 12759) (a := (8279804068903 / 10000000000000 : ℝ)) (b := (40357569257 / 25000000000000 : ℝ)) (q := (70138592673 / 3125000000000 : ℝ))
      (E := (cell12759 ⟨37, by decide⟩).energy) (xi := (332496150457969 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12759 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12759]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12759])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12759) (a := (8279804068903 / 10000000000000 : ℝ)) (b := (40357569257 / 25000000000000 : ℝ)) (q := (70138592673 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12759])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12759])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12759]

theorem cert12759_38 : CellCertificate 12759 (442524799052133 / 5000000000000000 : ℝ) (1646241615208429 / 1000000000000000000 : ℝ) (332496150457969 / 10000000000000000 : ℝ)
    (cell12759 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · have h := gap_lower (n := 12759) (a := (41381991616289 / 50000000000000 : ℝ)) (b := (40357569257 / 25000000000000 : ℝ)) (q := (2244438997017 / 100000000000000 : ℝ))
      (E := (cell12759 ⟨38, by decide⟩).energy) (xi := (332496150457969 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12759 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12759]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12759])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12759) (a := (41381991616289 / 50000000000000 : ℝ)) (b := (40357569257 / 25000000000000 : ℝ)) (q := (2244438997017 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12759])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12759])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12759]

theorem cert12759_39 : CellCertificate 12759 (442524799052133 / 5000000000000000 : ℝ) (1646241615208429 / 1000000000000000000 : ℝ) (332496150457969 / 10000000000000000 : ℝ)
    (cell12759 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · have h := gap_lower (n := 12759) (a := (10341243681767 / 12500000000000 : ℝ)) (b := (40357569257 / 25000000000000 : ℝ)) (q := (2244442964103 / 100000000000000 : ℝ))
      (E := (cell12759 ⟨39, by decide⟩).energy) (xi := (332496150457969 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12759 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12759]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12759])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12759) (a := (10341243681767 / 12500000000000 : ℝ)) (b := (40357569257 / 25000000000000 : ℝ)) (q := (2244442964103 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12759])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12759])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12759]

theorem cert12760_20 : CellCertificate 12760 (88502191094251 / 1000000000000000 : ℝ) (1646112557188047 / 1000000000000000000 : ℝ) (166234731733841 / 5000000000000000 : ℝ)
    (cell12760 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · have h := gap_lower (n := 12760) (a := (83380661389693 / 100000000000000 : ℝ)) (b := (161417472987 / 100000000000000 : ℝ)) (q := (1122123065729 / 50000000000000 : ℝ))
      (E := (cell12760 ⟨20, by decide⟩).energy) (xi := (166234731733841 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12760 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12760]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12760])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12760) (a := (83380661389693 / 100000000000000 : ℝ)) (b := (161417472987 / 100000000000000 : ℝ)) (q := (1122123065729 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12760])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12760])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12760]

theorem cert12760_21 : CellCertificate 12760 (88502191094251 / 1000000000000000 : ℝ) (1646112557188047 / 1000000000000000000 : ℝ) (166234731733841 / 5000000000000000 : ℝ)
    (cell12760 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · have h := gap_lower (n := 12760) (a := (3333847878353 / 4000000000000 : ℝ)) (b := (161417472987 / 100000000000000 : ℝ)) (q := (1122125065503 / 50000000000000 : ℝ))
      (E := (cell12760 ⟨21, by decide⟩).energy) (xi := (166234731733841 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12760 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12760]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12760])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12760) (a := (3333847878353 / 4000000000000 : ℝ)) (b := (161417472987 / 100000000000000 : ℝ)) (q := (1122125065503 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12760])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12760])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12760]

theorem cert12760_22 : CellCertificate 12760 (88502191094251 / 1000000000000000 : ℝ) (1646112557188047 / 1000000000000000000 : ℝ) (166234731733841 / 5000000000000000 : ℝ)
    (cell12760 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · have h := gap_lower (n := 12760) (a := (83311756741419 / 100000000000000 : ℝ)) (b := (161417472987 / 100000000000000 : ℝ)) (q := (1122127076729 / 50000000000000 : ℝ))
      (E := (cell12760 ⟨22, by decide⟩).energy) (xi := (166234731733841 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12760 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12760]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12760])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12760) (a := (83311756741419 / 100000000000000 : ℝ)) (b := (161417472987 / 100000000000000 : ℝ)) (q := (1122127076729 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12760])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12760])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12760]

theorem cert12760_23 : CellCertificate 12760 (88502191094251 / 1000000000000000 : ℝ) (1646112557188047 / 1000000000000000000 : ℝ) (166234731733841 / 5000000000000000 : ℝ)
    (cell12760 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · have h := gap_lower (n := 12760) (a := (16655468140929 / 20000000000000 : ℝ)) (b := (161417472987 / 100000000000000 : ℝ)) (q := (2244258144157 / 100000000000000 : ℝ))
      (E := (cell12760 ⟨23, by decide⟩).energy) (xi := (166234731733841 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12760 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12760]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12760])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12760) (a := (16655468140929 / 20000000000000 : ℝ)) (b := (161417472987 / 100000000000000 : ℝ)) (q := (2244258144157 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12760])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12760])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12760]

theorem cert12760_24 : CellCertificate 12760 (88502191094251 / 1000000000000000 : ℝ) (1646112557188047 / 1000000000000000000 : ℝ) (166234731733841 / 5000000000000000 : ℝ)
    (cell12760 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · have h := gap_lower (n := 12760) (a := (520268430099 / 625000000000 : ℝ)) (b := (161417472987 / 100000000000000 : ℝ)) (q := (2244262164873 / 100000000000000 : ℝ))
      (E := (cell12760 ⟨24, by decide⟩).energy) (xi := (166234731733841 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12760 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12760]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12760])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12760) (a := (520268430099 / 625000000000 : ℝ)) (b := (161417472987 / 100000000000000 : ℝ)) (q := (2244262164873 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12760])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12760])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12760]

theorem cert12760_25 : CellCertificate 12760 (88502191094251 / 1000000000000000 : ℝ) (1646112557188047 / 1000000000000000000 : ℝ) (166234731733841 / 5000000000000000 : ℝ)
    (cell12760 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · have h := gap_lower (n := 12760) (a := (8320858104251 / 10000000000000 : ℝ)) (b := (161417472987 / 100000000000000 : ℝ)) (q := (2244266160431 / 100000000000000 : ℝ))
      (E := (cell12760 ⟨25, by decide⟩).energy) (xi := (166234731733841 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12760 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12760]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12760])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12760) (a := (8320858104251 / 10000000000000 : ℝ)) (b := (161417472987 / 100000000000000 : ℝ)) (q := (2244266160431 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12760])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12760])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12760]

theorem cert12760_26 : CellCertificate 12760 (88502191094251 / 1000000000000000 : ℝ) (1646112557188047 / 1000000000000000000 : ℝ) (166234731733841 / 5000000000000000 : ℝ)
    (cell12760 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · have h := gap_lower (n := 12760) (a := (83174237352329 / 100000000000000 : ℝ)) (b := (161417472987 / 100000000000000 : ℝ)) (q := (1122135096089 / 50000000000000 : ℝ))
      (E := (cell12760 ⟨26, by decide⟩).energy) (xi := (166234731733841 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12760 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12760]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12760])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12760) (a := (83174237352329 / 100000000000000 : ℝ)) (b := (161417472987 / 100000000000000 : ℝ)) (q := (1122135096089 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12760])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12760])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12760]

theorem cert12760_27 : CellCertificate 12760 (88502191094251 / 1000000000000000 : ℝ) (1646112557188047 / 1000000000000000000 : ℝ) (166234731733841 / 5000000000000000 : ℝ)
    (cell12760 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · have h := gap_lower (n := 12760) (a := (20784979428283 / 25000000000000 : ℝ)) (b := (161417472987 / 100000000000000 : ℝ)) (q := (2244274204427 / 100000000000000 : ℝ))
      (E := (cell12760 ⟨27, by decide⟩).energy) (xi := (166234731733841 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12760 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12760]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12760])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12760) (a := (20784979428283 / 25000000000000 : ℝ)) (b := (161417472987 / 100000000000000 : ℝ)) (q := (2244274204427 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12760])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12760])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12760]

theorem cert12760_28 : CellCertificate 12760 (88502191094251 / 1000000000000000 : ℝ) (1646112557188047 / 1000000000000000000 : ℝ) (166234731733841 / 5000000000000000 : ℝ)
    (cell12760 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · have h := gap_lower (n := 12760) (a := (20776405523231 / 25000000000000 : ℝ)) (b := (161417472987 / 100000000000000 : ℝ)) (q := (2244278199633 / 100000000000000 : ℝ))
      (E := (cell12760 ⟨28, by decide⟩).energy) (xi := (166234731733841 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12760 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12760]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12760])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12760) (a := (20776405523231 / 25000000000000 : ℝ)) (b := (161417472987 / 100000000000000 : ℝ)) (q := (2244278199633 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12760])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12760])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12760]

theorem cert12760_29 : CellCertificate 12760 (88502191094251 / 1000000000000000 : ℝ) (1646112557188047 / 1000000000000000000 : ℝ) (166234731733841 / 5000000000000000 : ℝ)
    (cell12760 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · have h := gap_lower (n := 12760) (a := (83071350459871 / 100000000000000 : ℝ)) (b := (161417472987 / 100000000000000 : ℝ)) (q := (2244282180023 / 100000000000000 : ℝ))
      (E := (cell12760 ⟨29, by decide⟩).energy) (xi := (166234731733841 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12760 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12760]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12760])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12760) (a := (83071350459871 / 100000000000000 : ℝ)) (b := (161417472987 / 100000000000000 : ℝ)) (q := (2244282180023 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12760])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12760])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12760]

theorem cert12760_30 : CellCertificate 12760 (88502191094251 / 1000000000000000 : ℝ) (1646112557188047 / 1000000000000000000 : ℝ) (166234731733841 / 5000000000000000 : ℝ)
    (cell12760 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · have h := gap_lower (n := 12760) (a := (83037102782299 / 100000000000000 : ℝ)) (b := (161417472987 / 100000000000000 : ℝ)) (q := (70133943941 / 3125000000000 : ℝ))
      (E := (cell12760 ⟨30, by decide⟩).energy) (xi := (166234731733841 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12760 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12760]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12760])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12760) (a := (83037102782299 / 100000000000000 : ℝ)) (b := (161417472987 / 100000000000000 : ℝ)) (q := (70133943941 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12760])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12760])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12760]

theorem cert12760_31 : CellCertificate 12760 (88502191094251 / 1000000000000000 : ℝ) (1646112557188047 / 1000000000000000000 : ℝ) (166234731733841 / 5000000000000000 : ℝ)
    (cell12760 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · have h := gap_lower (n := 12760) (a := (83002879028701 / 100000000000000 : ℝ)) (b := (161417472987 / 100000000000000 : ℝ)) (q := (2244290162651 / 100000000000000 : ℝ))
      (E := (cell12760 ⟨31, by decide⟩).energy) (xi := (166234731733841 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12760 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12760]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12760])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12760) (a := (83002879028701 / 100000000000000 : ℝ)) (b := (161417472987 / 100000000000000 : ℝ)) (q := (2244290162651 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12760])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12760])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12760]

theorem cert12760_32 : CellCertificate 12760 (88502191094251 / 1000000000000000 : ℝ) (1646112557188047 / 1000000000000000000 : ℝ) (166234731733841 / 5000000000000000 : ℝ)
    (cell12760 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · have h := gap_lower (n := 12760) (a := (82968679167727 / 100000000000000 : ℝ)) (b := (161417472987 / 100000000000000 : ℝ)) (q := (2244294168239 / 100000000000000 : ℝ))
      (E := (cell12760 ⟨32, by decide⟩).energy) (xi := (166234731733841 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12760 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12760]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12760])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12760) (a := (82968679167727 / 100000000000000 : ℝ)) (b := (161417472987 / 100000000000000 : ℝ)) (q := (2244294168239 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12760])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12760])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12760]

theorem cert12760_33 : CellCertificate 12760 (88502191094251 / 1000000000000000 : ℝ) (1646112557188047 / 1000000000000000000 : ℝ) (166234731733841 / 5000000000000000 : ℝ)
    (cell12760 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · have h := gap_lower (n := 12760) (a := (82934503168187 / 100000000000000 : ℝ)) (b := (161417472987 / 100000000000000 : ℝ)) (q := (1122149112129 / 50000000000000 : ℝ))
      (E := (cell12760 ⟨33, by decide⟩).energy) (xi := (166234731733841 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12760 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12760]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12760])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12760) (a := (82934503168187 / 100000000000000 : ℝ)) (b := (161417472987 / 100000000000000 : ℝ)) (q := (1122149112129 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12760])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12760])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12760]

theorem cert12760_34 : CellCertificate 12760 (88502191094251 / 1000000000000000 : ℝ) (1646112557188047 / 1000000000000000000 : ℝ) (166234731733841 / 5000000000000000 : ℝ)
    (cell12760 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · have h := gap_lower (n := 12760) (a := (82900350999049 / 100000000000000 : ℝ)) (b := (161417472987 / 100000000000000 : ℝ)) (q := (2244302214639 / 100000000000000 : ℝ))
      (E := (cell12760 ⟨34, by decide⟩).energy) (xi := (166234731733841 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12760 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12760]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12760])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12760) (a := (82900350999049 / 100000000000000 : ℝ)) (b := (161417472987 / 100000000000000 : ℝ)) (q := (2244302214639 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12760])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12760])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12760]

theorem cert12760_35 : CellCertificate 12760 (88502191094251 / 1000000000000000 : ℝ) (1646112557188047 / 1000000000000000000 : ℝ) (166234731733841 / 5000000000000000 : ℝ)
    (cell12760 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · have h := gap_lower (n := 12760) (a := (82866222629441 / 100000000000000 : ℝ)) (b := (161417472987 / 100000000000000 : ℝ)) (q := (1122153099401 / 50000000000000 : ℝ))
      (E := (cell12760 ⟨35, by decide⟩).energy) (xi := (166234731733841 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12760 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12760]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12760])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12760) (a := (82866222629441 / 100000000000000 : ℝ)) (b := (161417472987 / 100000000000000 : ℝ)) (q := (1122153099401 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12760])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12760])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12760]

theorem cert12760_36 : CellCertificate 12760 (88502191094251 / 1000000000000000 : ℝ) (1646112557188047 / 1000000000000000000 : ℝ) (166234731733841 / 5000000000000000 : ℝ)
    (cell12760 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · have h := gap_lower (n := 12760) (a := (41416059014323 / 50000000000000 : ℝ)) (b := (161417472987 / 100000000000000 : ℝ)) (q := (2244310236043 / 100000000000000 : ℝ))
      (E := (cell12760 ⟨36, by decide⟩).energy) (xi := (166234731733841 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12760 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12760]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12760])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12760) (a := (41416059014323 / 50000000000000 : ℝ)) (b := (161417472987 / 100000000000000 : ℝ)) (q := (2244310236043 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12760])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12760])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12760]

theorem cert12760_37 : CellCertificate 12760 (88502191094251 / 1000000000000000 : ℝ) (1646112557188047 / 1000000000000000000 : ℝ) (166234731733841 / 5000000000000000 : ℝ)
    (cell12760 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · have h := gap_lower (n := 12760) (a := (82798037166103 / 100000000000000 : ℝ)) (b := (161417472987 / 100000000000000 : ℝ)) (q := (561078552369 / 25000000000000 : ℝ))
      (E := (cell12760 ⟨37, by decide⟩).energy) (xi := (166234731733841 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12760 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12760]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12760])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12760) (a := (82798037166103 / 100000000000000 : ℝ)) (b := (161417472987 / 100000000000000 : ℝ)) (q := (561078552369 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12760])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12760])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12760]

theorem cert12760_38 : CellCertificate 12760 (88502191094251 / 1000000000000000 : ℝ) (1646112557188047 / 1000000000000000000 : ℝ) (166234731733841 / 5000000000000000 : ℝ)
    (cell12760 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · have h := gap_lower (n := 12760) (a := (16552796002281 / 20000000000000 : ℝ)) (b := (161417472987 / 100000000000000 : ℝ)) (q := (2244318236631 / 100000000000000 : ℝ))
      (E := (cell12760 ⟨38, by decide⟩).energy) (xi := (166234731733841 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12760 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12760]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12760])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12760) (a := (16552796002281 / 20000000000000 : ℝ)) (b := (161417472987 / 100000000000000 : ℝ)) (q := (2244318236631 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12760])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12760])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12760]

theorem cert12760_39 : CellCertificate 12760 (88502191094251 / 1000000000000000 : ℝ) (1646112557188047 / 1000000000000000000 : ℝ) (166234731733841 / 5000000000000000 : ℝ)
    (cell12760 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · have h := gap_lower (n := 12760) (a := (82729946534301 / 100000000000000 : ℝ)) (b := (161417472987 / 100000000000000 : ℝ)) (q := (2244322200083 / 100000000000000 : ℝ))
      (E := (cell12760 ⟨39, by decide⟩).energy) (xi := (166234731733841 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12760 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12760]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12760])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12760) (a := (82729946534301 / 100000000000000 : ℝ)) (b := (161417472987 / 100000000000000 : ℝ)) (q := (2244322200083 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12760])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12760])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12760]

theorem cert12761_20 : CellCertificate 12761 (176998845589057 / 2000000000000000 : ℝ) (822991759700613 / 500000000000000000 : ℝ) (166221390407617 / 5000000000000000 : ℝ)
    (cell12761 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · have h := gap_lower (n := 12761) (a := (20845163168503 / 25000000000000 : ℝ)) (b := (16140467099 / 10000000000000 : ℝ)) (q := (224412543521 / 10000000000000 : ℝ))
      (E := (cell12761 ⟨20, by decide⟩).energy) (xi := (166221390407617 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12761 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12761]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12761])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12761) (a := (20845163168503 / 25000000000000 : ℝ)) (b := (16140467099 / 10000000000000 : ℝ)) (q := (224412543521 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12761])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12761])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12761]

theorem cert12761_21 : CellCertificate 12761 (176998845589057 / 2000000000000000 : ℝ) (822991759700613 / 500000000000000000 : ℝ) (166221390407617 / 5000000000000000 : ℝ)
    (cell12761 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · have h := gap_lower (n := 12761) (a := (20836547138017 / 25000000000000 : ℝ)) (b := (16140467099 / 10000000000000 : ℝ)) (q := (224412941853 / 10000000000000 : ℝ))
      (E := (cell12761 ⟨21, by decide⟩).energy) (xi := (166221390407617 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12761 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12761]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12761])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12761) (a := (20836547138017 / 25000000000000 : ℝ)) (b := (16140467099 / 10000000000000 : ℝ)) (q := (224412941853 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12761])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12761])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12761]

theorem cert12761_22 : CellCertificate 12761 (176998845589057 / 2000000000000000 : ℝ) (822991759700613 / 500000000000000000 : ℝ) (166221390407617 / 5000000000000000 : ℝ)
    (cell12761 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · have h := gap_lower (n := 12761) (a := (16662349728631 / 20000000000000 : ℝ)) (b := (16140467099 / 10000000000000 : ℝ)) (q := (2244133425461 / 100000000000000 : ℝ))
      (E := (cell12761 ⟨22, by decide⟩).energy) (xi := (166221390407617 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12761 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12761]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12761])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12761) (a := (16662349728631 / 20000000000000 : ℝ)) (b := (16140467099 / 10000000000000 : ℝ)) (q := (2244133425461 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12761])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12761])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12761]

theorem cert12761_23 : CellCertificate 12761 (176998845589057 / 2000000000000000 : ℝ) (822991759700613 / 500000000000000000 : ℝ) (166221390407617 / 5000000000000000 : ℝ)
    (cell12761 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · have h := gap_lower (n := 12761) (a := (20819333228611 / 25000000000000 : ℝ)) (b := (16140467099 / 10000000000000 : ℝ)) (q := (448827480269 / 20000000000000 : ℝ))
      (E := (cell12761 ⟨23, by decide⟩).energy) (xi := (166221390407617 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12761 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12761]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12761])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12761) (a := (20819333228611 / 25000000000000 : ℝ)) (b := (16140467099 / 10000000000000 : ℝ)) (q := (448827480269 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12761])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12761])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12761]

theorem cert12761_24 : CellCertificate 12761 (176998845589057 / 2000000000000000 : ℝ) (822991759700613 / 500000000000000000 : ℝ) (166221390407617 / 5000000000000000 : ℝ)
    (cell12761 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · have h := gap_lower (n := 12761) (a := (41621470666637 / 50000000000000 : ℝ)) (b := (16140467099 / 10000000000000 : ℝ)) (q := (561035351987 / 25000000000000 : ℝ))
      (E := (cell12761 ⟨24, by decide⟩).energy) (xi := (166221390407617 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12761 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12761]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12761])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12761) (a := (41621470666637 / 50000000000000 : ℝ)) (b := (16140467099 / 10000000000000 : ℝ)) (q := (561035351987 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12761])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12761])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12761]

theorem cert12761_25 : CellCertificate 12761 (176998845589057 / 2000000000000000 : ℝ) (822991759700613 / 500000000000000000 : ℝ) (166221390407617 / 5000000000000000 : ℝ)
    (cell12761 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · have h := gap_lower (n := 12761) (a := (83208573867151 / 100000000000000 : ℝ)) (b := (16140467099 / 10000000000000 : ℝ)) (q := (4488290897 / 200000000000 : ℝ))
      (E := (cell12761 ⟨25, by decide⟩).energy) (xi := (166221390407617 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12761 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12761]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12761])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12761) (a := (83208573867151 / 100000000000000 : ℝ)) (b := (16140467099 / 10000000000000 : ℝ)) (q := (4488290897 / 200000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12761])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12761])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12761]

theorem cert12761_26 : CellCertificate 12761 (176998845589057 / 2000000000000000 : ℝ) (822991759700613 / 500000000000000000 : ℝ) (166221390407617 / 5000000000000000 : ℝ)
    (cell12761 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · have h := gap_lower (n := 12761) (a := (83174230483749 / 100000000000000 : ℝ)) (b := (16140467099 / 10000000000000 : ℝ)) (q := (448829893513 / 20000000000000 : ℝ))
      (E := (cell12761 ⟨26, by decide⟩).energy) (xi := (166221390407617 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12761 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12761]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12761])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12761) (a := (83174230483749 / 100000000000000 : ℝ)) (b := (16140467099 / 10000000000000 : ℝ)) (q := (448829893513 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12761])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12761])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12761]

theorem cert12761_27 : CellCertificate 12761 (176998845589057 / 2000000000000000 : ℝ) (822991759700613 / 500000000000000000 : ℝ) (166221390407617 / 5000000000000000 : ℝ)
    (cell12761 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · have h := gap_lower (n := 12761) (a := (41569955575453 / 50000000000000 : ℝ)) (b := (16140467099 / 10000000000000 : ℝ)) (q := (2244153467833 / 100000000000000 : ℝ))
      (E := (cell12761 ⟨27, by decide⟩).energy) (xi := (166221390407617 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12761 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12761]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12761])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12761) (a := (41569955575453 / 50000000000000 : ℝ)) (b := (16140467099 / 10000000000000 : ℝ)) (q := (2244153467833 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12761])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12761])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12761]

theorem cert12761_28 : CellCertificate 12761 (176998845589057 / 2000000000000000 : ℝ) (822991759700613 / 500000000000000000 : ℝ) (166221390407617 / 5000000000000000 : ℝ)
    (cell12761 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · have h := gap_lower (n := 12761) (a := (41552807918313 / 50000000000000 : ℝ)) (b := (16140467099 / 10000000000000 : ℝ)) (q := (2244157451759 / 100000000000000 : ℝ))
      (E := (cell12761 ⟨28, by decide⟩).energy) (xi := (166221390407617 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12761 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12761]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12761])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12761) (a := (41552807918313 / 50000000000000 : ℝ)) (b := (16140467099 / 10000000000000 : ℝ)) (q := (2244157451759 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12761])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12761])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12761]

theorem cert12761_29 : CellCertificate 12761 (176998845589057 / 2000000000000000 : ℝ) (822991759700613 / 500000000000000000 : ℝ) (166221390407617 / 5000000000000000 : ℝ)
    (cell12761 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · have h := gap_lower (n := 12761) (a := (3322853780363 / 4000000000000 : ℝ)) (b := (16140467099 / 10000000000000 : ℝ)) (q := (224416142157 / 10000000000000 : ℝ))
      (E := (cell12761 ⟨29, by decide⟩).energy) (xi := (166221390407617 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12761 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12761]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12761])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12761) (a := (3322853780363 / 4000000000000 : ℝ)) (b := (16140467099 / 10000000000000 : ℝ)) (q := (224416142157 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12761])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12761])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12761]

theorem cert12761_30 : CellCertificate 12761 (176998845589057 / 2000000000000000 : ℝ) (822991759700613 / 500000000000000000 : ℝ) (166221390407617 / 5000000000000000 : ℝ)
    (cell12761 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · have h := gap_lower (n := 12761) (a := (83037097136583 / 100000000000000 : ℝ)) (b := (16140467099 / 10000000000000 : ℝ)) (q := (2244165437779 / 100000000000000 : ℝ))
      (E := (cell12761 ⟨30, by decide⟩).energy) (xi := (166221390407617 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12761 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12761]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12761])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12761) (a := (83037097136583 / 100000000000000 : ℝ)) (b := (16140467099 / 10000000000000 : ℝ)) (q := (2244165437779 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12761])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12761])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12761]

theorem cert12761_31 : CellCertificate 12761 (176998845589057 / 2000000000000000 : ℝ) (822991759700613 / 500000000000000000 : ℝ) (166221390407617 / 5000000000000000 : ℝ)
    (cell12761 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · have h := gap_lower (n := 12761) (a := (41501436843821 / 50000000000000 : ℝ)) (b := (16140467099 / 10000000000000 : ℝ)) (q := (1122084721839 / 50000000000000 : ℝ))
      (E := (cell12761 ⟨31, by decide⟩).energy) (xi := (166221390407617 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12761 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12761]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12761])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12761) (a := (41501436843821 / 50000000000000 : ℝ)) (b := (16140467099 / 10000000000000 : ℝ)) (q := (1122084721839 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12761])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12761])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12761]

theorem cert12761_32 : CellCertificate 12761 (176998845589057 / 2000000000000000 : ℝ) (822991759700613 / 500000000000000000 : ℝ) (166221390407617 / 5000000000000000 : ℝ)
    (cell12761 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · have h := gap_lower (n := 12761) (a := (82968674130901 / 100000000000000 : ℝ)) (b := (16140467099 / 10000000000000 : ℝ)) (q := (280521680101 / 12500000000000 : ℝ))
      (E := (cell12761 ⟨32, by decide⟩).energy) (xi := (166221390407617 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12761 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12761]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12761])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12761) (a := (82968674130901 / 100000000000000 : ℝ)) (b := (16140467099 / 10000000000000 : ℝ)) (q := (280521680101 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12761])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12761])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12761]

theorem cert12761_33 : CellCertificate 12761 (176998845589057 / 2000000000000000 : ℝ) (822991759700613 / 500000000000000000 : ℝ) (166221390407617 / 5000000000000000 : ℝ)
    (cell12761 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · have h := gap_lower (n := 12761) (a := (41467249217587 / 50000000000000 : ℝ)) (b := (16140467099 / 10000000000000 : ℝ)) (q := (2244177489063 / 100000000000000 : ℝ))
      (E := (cell12761 ⟨33, by decide⟩).energy) (xi := (166221390407617 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12761 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12761]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12761])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12761) (a := (41467249217587 / 50000000000000 : ℝ)) (b := (16140467099 / 10000000000000 : ℝ)) (q := (2244177489063 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12761])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12761])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12761]

theorem cert12761_34 : CellCertificate 12761 (176998845589057 / 2000000000000000 : ℝ) (822991759700613 / 500000000000000000 : ℝ) (166221390407617 / 5000000000000000 : ℝ)
    (cell12761 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · have h := gap_lower (n := 12761) (a := (20725086642357 / 25000000000000 : ℝ)) (b := (16140467099 / 10000000000000 : ℝ)) (q := (2244181472377 / 100000000000000 : ℝ))
      (E := (cell12761 ⟨34, by decide⟩).energy) (xi := (166221390407617 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12761 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12761]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12761])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12761) (a := (20725086642357 / 25000000000000 : ℝ)) (b := (16140467099 / 10000000000000 : ℝ)) (q := (2244181472377 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12761])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12761])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12761]

theorem cert12761_35 : CellCertificate 12761 (176998845589057 / 2000000000000000 : ℝ) (822991759700613 / 500000000000000000 : ℝ) (166221390407617 / 5000000000000000 : ℝ)
    (cell12761 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · have h := gap_lower (n := 12761) (a := (82866218502793 / 100000000000000 : ℝ)) (b := (16140467099 / 10000000000000 : ℝ)) (q := (2244185450169 / 100000000000000 : ℝ))
      (E := (cell12761 ⟨35, by decide⟩).energy) (xi := (166221390407617 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12761 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12761]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12761])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12761) (a := (82866218502793 / 100000000000000 : ℝ)) (b := (16140467099 / 10000000000000 : ℝ)) (q := (2244185450169 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12761])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12761])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12761]

theorem cert12761_36 : CellCertificate 12761 (176998845589057 / 2000000000000000 : ℝ) (822991759700613 / 500000000000000000 : ℝ) (166221390407617 / 5000000000000000 : ℝ)
    (cell12761 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · have h := gap_lower (n := 12761) (a := (82832114204551 / 100000000000000 : ℝ)) (b := (16140467099 / 10000000000000 : ℝ)) (q := (1122094740867 / 50000000000000 : ℝ))
      (E := (cell12761 ⟨36, by decide⟩).energy) (xi := (166221390407617 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12761 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12761]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12761])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12761) (a := (82832114204551 / 100000000000000 : ℝ)) (b := (16140467099 / 10000000000000 : ℝ)) (q := (1122094740867 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12761])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12761])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12761]

theorem cert12761_37 : CellCertificate 12761 (176998845589057 / 2000000000000000 : ℝ) (822991759700613 / 500000000000000000 : ℝ) (166221390407617 / 5000000000000000 : ℝ)
    (cell12761 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · have h := gap_lower (n := 12761) (a := (82798033644143 / 100000000000000 : ℝ)) (b := (16140467099 / 10000000000000 : ℝ)) (q := (561048377217 / 25000000000000 : ℝ))
      (E := (cell12761 ⟨37, by decide⟩).energy) (xi := (166221390407617 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12761 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12761]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12761])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12761) (a := (82798033644143 / 100000000000000 : ℝ)) (b := (16140467099 / 10000000000000 : ℝ)) (q := (561048377217 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12761])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12761])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12761]

theorem cert12761_38 : CellCertificate 12761 (176998845589057 / 2000000000000000 : ℝ) (822991759700613 / 500000000000000000 : ℝ) (166221390407617 / 5000000000000000 : ℝ)
    (cell12761 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · have h := gap_lower (n := 12761) (a := (82763976791163 / 100000000000000 : ℝ)) (b := (16140467099 / 10000000000000 : ℝ)) (q := (2244197473051 / 100000000000000 : ℝ))
      (E := (cell12761 ⟨38, by decide⟩).energy) (xi := (166221390407617 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12761 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12761]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12761])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12761) (a := (82763976791163 / 100000000000000 : ℝ)) (b := (16140467099 / 10000000000000 : ℝ)) (q := (2244197473051 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12761])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12761])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12761]

theorem cert12761_39 : CellCertificate 12761 (176998845589057 / 2000000000000000 : ℝ) (822991759700613 / 500000000000000000 : ℝ) (166221390407617 / 5000000000000000 : ℝ)
    (cell12761 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · have h := gap_lower (n := 12761) (a := (82729943615359 / 100000000000000 : ℝ)) (b := (16140467099 / 10000000000000 : ℝ)) (q := (2244201491637 / 100000000000000 : ℝ))
      (E := (cell12761 ⟨39, by decide⟩).energy) (xi := (166221390407617 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12761 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12761]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12761])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12761) (a := (82729943615359 / 100000000000000 : ℝ)) (b := (16140467099 / 10000000000000 : ℝ)) (q := (2244201491637 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12761])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12761])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12761]

theorem cert12762_20 : CellCertificate 12762 (442483274555803 / 5000000000000000 : ℝ) (1645854501843209 / 1000000000000000000 : ℝ) (8310402562487 / 250000000000000 : ℝ)
    (cell12762 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · have h := gap_lower (n := 12762) (a := (20845160989981 / 25000000000000 : ℝ)) (b := (161391871037 / 100000000000000 : ℝ)) (q := (2244004735089 / 100000000000000 : ℝ))
      (E := (cell12762 ⟨20, by decide⟩).energy) (xi := (8310402562487 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12762 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12762]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12762])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12762) (a := (20845160989981 / 25000000000000 : ℝ)) (b := (161391871037 / 100000000000000 : ℝ)) (q := (2244004735089 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12762])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12762])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12762]

theorem cert12762_21 : CellCertificate 12762 (442483274555803 / 5000000000000000 : ℝ) (1645854501843209 / 1000000000000000000 : ℝ) (8310402562487 / 250000000000000 : ℝ)
    (cell12762 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · have h := gap_lower (n := 12762) (a := (41673090073433 / 50000000000000 : ℝ)) (b := (161391871037 / 100000000000000 : ℝ)) (q := (2244008702221 / 100000000000000 : ℝ))
      (E := (cell12762 ⟨21, by decide⟩).energy) (xi := (8310402562487 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12762 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12762]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12762])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12762) (a := (41673090073433 / 50000000000000 : ℝ)) (b := (161391871037 / 100000000000000 : ℝ)) (q := (2244008702221 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12762])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12762])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12762]

theorem cert12762_22 : CellCertificate 12762 (442483274555803 / 5000000000000000 : ℝ) (1645854501843209 / 1000000000000000000 : ℝ) (8310402562487 / 250000000000000 : ℝ)
    (cell12762 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · have h := gap_lower (n := 12762) (a := (83311740546409 / 100000000000000 : ℝ)) (b := (161391871037 / 100000000000000 : ℝ)) (q := (140250797 / 6250000000 : ℝ))
      (E := (cell12762 ⟨22, by decide⟩).energy) (xi := (8310402562487 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12762 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12762]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12762])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12762) (a := (83311740546409 / 100000000000000 : ℝ)) (b := (161391871037 / 100000000000000 : ℝ)) (q := (140250797 / 6250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12762])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12762])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12762]

theorem cert12762_23 : CellCertificate 12762 (442483274555803 / 5000000000000000 : ℝ) (1645854501843209 / 1000000000000000000 : ℝ) (8310402562487 / 250000000000000 : ℝ)
    (cell12762 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · have h := gap_lower (n := 12762) (a := (3331093005029 / 4000000000000 : ℝ)) (b := (161391871037 / 100000000000000 : ℝ)) (q := (280502089141 / 12500000000000 : ℝ))
      (E := (cell12762 ⟨23, by decide⟩).energy) (xi := (8310402562487 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12762 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12762]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12762])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12762) (a := (3331093005029 / 4000000000000 : ℝ)) (b := (161391871037 / 100000000000000 : ℝ)) (q := (280502089141 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12762])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12762])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12762]

theorem cert12762_24 : CellCertificate 12762 (442483274555803 / 5000000000000000 : ℝ) (1645854501843209 / 1000000000000000000 : ℝ) (8310402562487 / 250000000000000 : ℝ)
    (cell12762 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · have h := gap_lower (n := 12762) (a := (10405366731519 / 12500000000000 : ℝ)) (b := (161391871037 / 100000000000000 : ℝ)) (q := (1122010352841 / 50000000000000 : ℝ))
      (E := (cell12762 ⟨24, by decide⟩).energy) (xi := (8310402562487 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12762 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12762]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12762])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12762) (a := (10405366731519 / 12500000000000 : ℝ)) (b := (161391871037 / 100000000000000 : ℝ)) (q := (1122010352841 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12762])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12762])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12762]

theorem cert12762_25 : CellCertificate 12762 (442483274555803 / 5000000000000000 : ℝ) (1645854501843209 / 1000000000000000000 : ℝ) (8310402562487 / 250000000000000 : ℝ)
    (cell12762 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · have h := gap_lower (n := 12762) (a := (83208566693199 / 100000000000000 : ℝ)) (b := (161391871037 / 100000000000000 : ℝ)) (q := (1122012366443 / 50000000000000 : ℝ))
      (E := (cell12762 ⟨25, by decide⟩).energy) (xi := (8310402562487 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12762 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12762]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12762])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12762) (a := (83208566693199 / 100000000000000 : ℝ)) (b := (161391871037 / 100000000000000 : ℝ)) (q := (1122012366443 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12762])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12762])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12762]

theorem cert12762_26 : CellCertificate 12762 (442483274555803 / 5000000000000000 : ℝ) (1645854501843209 / 1000000000000000000 : ℝ) (8310402562487 / 250000000000000 : ℝ)
    (cell12762 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · have h := gap_lower (n := 12762) (a := (83174223616539 / 100000000000000 : ℝ)) (b := (161391871037 / 100000000000000 : ℝ)) (q := (2244028739307 / 100000000000000 : ℝ))
      (E := (cell12762 ⟨26, by decide⟩).energy) (xi := (8310402562487 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12762 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12762]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12762])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12762) (a := (83174223616539 / 100000000000000 : ℝ)) (b := (161391871037 / 100000000000000 : ℝ)) (q := (2244028739307 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12762])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12762])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12762]

theorem cert12762_27 : CellCertificate 12762 (442483274555803 / 5000000000000000 : ℝ) (1645854501843209 / 1000000000000000000 : ℝ) (8310402562487 / 250000000000000 : ℝ)
    (cell12762 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · have h := gap_lower (n := 12762) (a := (83139904590013 / 100000000000000 : ℝ)) (b := (161391871037 / 100000000000000 : ℝ)) (q := (140252045477 / 6250000000000 : ℝ))
      (E := (cell12762 ⟨27, by decide⟩).energy) (xi := (8310402562487 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12762 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12762]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12762])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12762) (a := (83139904590013 / 100000000000000 : ℝ)) (b := (161391871037 / 100000000000000 : ℝ)) (q := (140252045477 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12762])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12762])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12762]

theorem cert12762_28 : CellCertificate 12762 (442483274555803 / 5000000000000000 : ℝ) (1645854501843209 / 1000000000000000000 : ℝ) (8310402562487 / 250000000000000 : ℝ)
    (cell12762 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · have h := gap_lower (n := 12762) (a := (83105609581623 / 100000000000000 : ℝ)) (b := (161391871037 / 100000000000000 : ℝ)) (q := (2244036758789 / 100000000000000 : ℝ))
      (E := (cell12762 ⟨28, by decide⟩).energy) (xi := (8310402562487 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12762 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12762]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12762])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12762) (a := (83105609581623 / 100000000000000 : ℝ)) (b := (161391871037 / 100000000000000 : ℝ)) (q := (2244036758789 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12762])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12762])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12762]

theorem cert12762_29 : CellCertificate 12762 (442483274555803 / 5000000000000000 : ℝ) (1645854501843209 / 1000000000000000000 : ℝ) (8310402562487 / 250000000000000 : ℝ)
    (cell12762 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · have h := gap_lower (n := 12762) (a := (83071338559539 / 100000000000000 : ℝ)) (b := (161391871037 / 100000000000000 : ℝ)) (q := (2244040776577 / 100000000000000 : ℝ))
      (E := (cell12762 ⟨29, by decide⟩).energy) (xi := (8310402562487 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12762 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12762]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12762])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12762) (a := (83071338559539 / 100000000000000 : ℝ)) (b := (161391871037 / 100000000000000 : ℝ)) (q := (2244040776577 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12762])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12762])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12762]

theorem cert12762_30 : CellCertificate 12762 (442483274555803 / 5000000000000000 : ℝ) (1645854501843209 / 1000000000000000000 : ℝ) (8310402562487 / 250000000000000 : ℝ)
    (cell12762 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · have h := gap_lower (n := 12762) (a := (8303709149209 / 10000000000000 : ℝ)) (b := (161391871037 / 100000000000000 : ℝ)) (q := (2244044724471 / 100000000000000 : ℝ))
      (E := (cell12762 ⟨30, by decide⟩).energy) (xi := (8310402562487 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12762 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12762]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12762])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12762) (a := (8303709149209 / 10000000000000 : ℝ)) (b := (161391871037 / 100000000000000 : ℝ)) (q := (2244044724471 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12762])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12762])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12762]

theorem cert12762_31 : CellCertificate 12762 (442483274555803 / 5000000000000000 : ℝ) (1645854501843209 / 1000000000000000000 : ℝ) (8310402562487 / 250000000000000 : ℝ)
    (cell12762 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · have h := gap_lower (n := 12762) (a := (83002868347767 / 100000000000000 : ℝ)) (b := (161391871037 / 100000000000000 : ℝ)) (q := (1122024389897 / 50000000000000 : ℝ))
      (E := (cell12762 ⟨31, by decide⟩).energy) (xi := (8310402562487 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12762 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12762]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12762])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12762) (a := (83002868347767 / 100000000000000 : ℝ)) (b := (161391871037 / 100000000000000 : ℝ)) (q := (1122024389897 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12762])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12762])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12762]

theorem cert12762_32 : CellCertificate 12762 (442483274555803 / 5000000000000000 : ℝ) (1645854501843209 / 1000000000000000000 : ℝ) (8310402562487 / 250000000000000 : ℝ)
    (cell12762 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · have h := gap_lower (n := 12762) (a := (10371083636903 / 12500000000000 : ℝ)) (b := (161391871037 / 100000000000000 : ℝ)) (q := (2244052768523 / 100000000000000 : ℝ))
      (E := (cell12762 ⟨32, by decide⟩).energy) (xi := (8310402562487 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12762 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12762]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12762])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12762) (a := (10371083636903 / 12500000000000 : ℝ)) (b := (161391871037 / 100000000000000 : ℝ)) (q := (2244052768523 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12762])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12762])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12762]

theorem cert12762_33 : CellCertificate 12762 (442483274555803 / 5000000000000000 : ℝ) (1645854501843209 / 1000000000000000000 : ℝ) (8310402562487 / 250000000000000 : ℝ)
    (cell12762 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · have h := gap_lower (n := 12762) (a := (82934493703273 / 100000000000000 : ℝ)) (b := (161391871037 / 100000000000000 : ℝ)) (q := (280507093811 / 12500000000000 : ℝ))
      (E := (cell12762 ⟨33, by decide⟩).energy) (xi := (8310402562487 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12762 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12762]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12762])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12762) (a := (82934493703273 / 100000000000000 : ℝ)) (b := (161391871037 / 100000000000000 : ℝ)) (q := (280507093811 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12762])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12762])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12762]

theorem cert12762_34 : CellCertificate 12762 (442483274555803 / 5000000000000000 : ℝ) (1645854501843209 / 1000000000000000000 : ℝ) (8310402562487 / 250000000000000 : ℝ)
    (cell12762 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · have h := gap_lower (n := 12762) (a := (82900342140883 / 100000000000000 : ℝ)) (b := (161391871037 / 100000000000000 : ℝ)) (q := (448812157077 / 20000000000000 : ℝ))
      (E := (cell12762 ⟨34, by decide⟩).energy) (xi := (8310402562487 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12762 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12762]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12762])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12762) (a := (82900342140883 / 100000000000000 : ℝ)) (b := (161391871037 / 100000000000000 : ℝ)) (q := (448812157077 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12762])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12762])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12762]

theorem cert12762_35 : CellCertificate 12762 (442483274555803 / 5000000000000000 : ℝ) (1645854501843209 / 1000000000000000000 : ℝ) (8310402562487 / 250000000000000 : ℝ)
    (cell12762 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · have h := gap_lower (n := 12762) (a := (82866214377183 / 100000000000000 : ℝ)) (b := (161391871037 / 100000000000000 : ℝ)) (q := (561016189217 / 25000000000000 : ℝ))
      (E := (cell12762 ⟨35, by decide⟩).energy) (xi := (8310402562487 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12762 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12762]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12762])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12762) (a := (82866214377183 / 100000000000000 : ℝ)) (b := (161391871037 / 100000000000000 : ℝ)) (q := (561016189217 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12762])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12762])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12762]

theorem cert12762_36 : CellCertificate 12762 (442483274555803 / 5000000000000000 : ℝ) (1645854501843209 / 1000000000000000000 : ℝ) (8310402562487 / 250000000000000 : ℝ)
    (cell12762 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · have h := gap_lower (n := 12762) (a := (41416055190729 / 50000000000000 : ℝ)) (b := (161391871037 / 100000000000000 : ℝ)) (q := (2244068782817 / 100000000000000 : ℝ))
      (E := (cell12762 ⟨36, by decide⟩).energy) (xi := (8310402562487 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12762 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12762]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12762])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12762) (a := (41416055190729 / 50000000000000 : ℝ)) (b := (161391871037 / 100000000000000 : ℝ)) (q := (2244068782817 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12762])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12762])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12762]

theorem cert12762_37 : CellCertificate 12762 (442483274555803 / 5000000000000000 : ℝ) (1645854501843209 / 1000000000000000000 : ℝ) (8310402562487 / 250000000000000 : ℝ)
    (cell12762 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · have h := gap_lower (n := 12762) (a := (20699507530787 / 25000000000000 : ℝ)) (b := (161391871037 / 100000000000000 : ℝ)) (q := (224407280503 / 10000000000000 : ℝ))
      (E := (cell12762 ⟨37, by decide⟩).energy) (xi := (8310402562487 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12762 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12762]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12762])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12762) (a := (20699507530787 / 25000000000000 : ℝ)) (b := (161391871037 / 100000000000000 : ℝ)) (q := (224407280503 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12762])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12762])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12762]

theorem cert12762_38 : CellCertificate 12762 (442483274555803 / 5000000000000000 : ℝ) (1645854501843209 / 1000000000000000000 : ℝ) (8310402562487 / 250000000000000 : ℝ)
    (cell12762 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · have h := gap_lower (n := 12762) (a := (82763973571849 / 100000000000000 : ℝ)) (b := (161391871037 / 100000000000000 : ℝ)) (q := (448815352997 / 20000000000000 : ℝ))
      (E := (cell12762 ⟨38, by decide⟩).energy) (xi := (8310402562487 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12762 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12762]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12762])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12762) (a := (82763973571849 / 100000000000000 : ℝ)) (b := (161391871037 / 100000000000000 : ℝ)) (q := (448815352997 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12762])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12762])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12762]

theorem cert12762_39 : CellCertificate 12762 (442483274555803 / 5000000000000000 : ℝ) (1645854501843209 / 1000000000000000000 : ℝ) (8310402562487 / 250000000000000 : ℝ)
    (cell12762 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · have h := gap_lower (n := 12762) (a := (8272994069731 / 10000000000000 : ℝ)) (b := (161391871037 / 100000000000000 : ℝ)) (q := (448816156007 / 20000000000000 : ℝ))
      (E := (cell12762 ⟨39, by decide⟩).energy) (xi := (8310402562487 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12762 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12762]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12762])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12762) (a := (8272994069731 / 10000000000000 : ℝ)) (b := (161391871037 / 100000000000000 : ℝ)) (q := (448816156007 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12762])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12762])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12762]

theorem cert12763_20 : CellCertificate 12763 (884938874440489 / 10000000000000000 : ℝ) (1645725504509239 / 1000000000000000000 : ℝ) (332389428519277 / 10000000000000000 : ℝ)
    (cell12763 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · have h := gap_lower (n := 12763) (a := (20845158811857 / 25000000000000 : ℝ)) (b := (161379073127 / 100000000000000 : ℝ)) (q := (2243884031097 / 100000000000000 : ℝ))
      (E := (cell12763 ⟨20, by decide⟩).energy) (xi := (332389428519277 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12763 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12763]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12763])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12763) (a := (20845158811857 / 25000000000000 : ℝ)) (b := (161379073127 / 100000000000000 : ℝ)) (q := (2243884031097 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12763])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12763])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12763]

theorem cert12763_21 : CellCertificate 12763 (884938874440489 / 10000000000000000 : ℝ) (1645725504509239 / 1000000000000000000 : ℝ) (332389428519277 / 10000000000000000 : ℝ)
    (cell12763 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · have h := gap_lower (n := 12763) (a := (83346171743219 / 100000000000000 : ℝ)) (b := (161379073127 / 100000000000000 : ℝ)) (q := (1121944020193 / 50000000000000 : ℝ))
      (E := (cell12763 ⟨21, by decide⟩).energy) (xi := (332389428519277 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12763 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12763]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12763])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12763) (a := (83346171743219 / 100000000000000 : ℝ)) (b := (161379073127 / 100000000000000 : ℝ)) (q := (1121944020193 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12763])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12763])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12763]

theorem cert12763_22 : CellCertificate 12763 (884938874440489 / 10000000000000000 : ℝ) (1645725504509239 / 1000000000000000000 : ℝ) (332389428519277 / 10000000000000000 : ℝ)
    (cell12763 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · have h := gap_lower (n := 12763) (a := (41655866225591 / 50000000000000 : ℝ)) (b := (161379073127 / 100000000000000 : ℝ)) (q := (2243892074743 / 100000000000000 : ℝ))
      (E := (cell12763 ⟨22, by decide⟩).energy) (xi := (332389428519277 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12763 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12763]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12763])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12763) (a := (41655866225591 / 50000000000000 : ℝ)) (b := (161379073127 / 100000000000000 : ℝ)) (q := (2243892074743 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12763])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12763])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12763]

theorem cert12763_23 : CellCertificate 12763 (884938874440489 / 10000000000000000 : ℝ) (1645725504509239 / 1000000000000000000 : ℝ) (332389428519277 / 10000000000000000 : ℝ)
    (cell12763 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · have h := gap_lower (n := 12763) (a := (41638658669243 / 50000000000000 : ℝ)) (b := (161379073127 / 100000000000000 : ℝ)) (q := (224389607951 / 10000000000000 : ℝ))
      (E := (cell12763 ⟨23, by decide⟩).energy) (xi := (332389428519277 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12763 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12763]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12763])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12763) (a := (41638658669243 / 50000000000000 : ℝ)) (b := (161379073127 / 100000000000000 : ℝ)) (q := (224389607951 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12763])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12763])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12763]

theorem cert12763_24 : CellCertificate 12763 (884938874440489 / 10000000000000000 : ℝ) (1645725504509239 / 1000000000000000000 : ℝ) (332389428519277 / 10000000000000000 : ℝ)
    (cell12763 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · have h := gap_lower (n := 12763) (a := (41621463186237 / 50000000000000 : ℝ)) (b := (161379073127 / 100000000000000 : ℝ)) (q := (89756002323 / 4000000000000 : ℝ))
      (E := (cell12763 ⟨24, by decide⟩).energy) (xi := (332389428519277 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12763 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12763]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12763])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12763) (a := (41621463186237 / 50000000000000 : ℝ)) (b := (161379073127 / 100000000000000 : ℝ)) (q := (89756002323 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12763])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12763])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12763]

theorem cert12763_25 : CellCertificate 12763 (884938874440489 / 10000000000000000 : ℝ) (1645725504509239 / 1000000000000000000 : ℝ) (332389428519277 / 10000000000000000 : ℝ)
    (cell12763 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · have h := gap_lower (n := 12763) (a := (41604279760327 / 50000000000000 : ℝ)) (b := (161379073127 / 100000000000000 : ℝ)) (q := (2243904071993 / 100000000000000 : ℝ))
      (E := (cell12763 ⟨25, by decide⟩).energy) (xi := (332389428519277 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12763 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12763]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12763])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12763) (a := (41604279760327 / 50000000000000 : ℝ)) (b := (161379073127 / 100000000000000 : ℝ)) (q := (2243904071993 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12763])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12763])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12763]

theorem cert12763_26 : CellCertificate 12763 (884938874440489 / 10000000000000000 : ℝ) (1645725504509239 / 1000000000000000000 : ℝ) (332389428519277 / 10000000000000000 : ℝ)
    (cell12763 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · have h := gap_lower (n := 12763) (a := (83174216750699 / 100000000000000 : ℝ)) (b := (161379073127 / 100000000000000 : ℝ)) (q := (280488508229 / 12500000000000 : ℝ))
      (E := (cell12763 ⟨26, by decide⟩).energy) (xi := (332389428519277 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12763 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12763]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12763])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12763) (a := (83174216750699 / 100000000000000 : ℝ)) (b := (161379073127 / 100000000000000 : ℝ)) (q := (280488508229 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12763])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12763])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12763]

theorem cert12763_27 : CellCertificate 12763 (884938874440489 / 10000000000000000 : ℝ) (1645725504509239 / 1000000000000000000 : ℝ) (332389428519277 / 10000000000000000 : ℝ)
    (cell12763 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · have h := gap_lower (n := 12763) (a := (20784974507613 / 25000000000000 : ℝ)) (b := (161379073127 / 100000000000000 : ℝ)) (q := (89756481691 / 4000000000000 : ℝ))
      (E := (cell12763 ⟨27, by decide⟩).energy) (xi := (332389428519277 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12763 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12763]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12763])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12763) (a := (20784974507613 / 25000000000000 : ℝ)) (b := (161379073127 / 100000000000000 : ℝ)) (q := (89756481691 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12763])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12763])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12763]

theorem cert12763_28 : CellCertificate 12763 (884938874440489 / 10000000000000000 : ℝ) (1645725504509239 / 1000000000000000000 : ℝ) (332389428519277 / 10000000000000000 : ℝ)
    (cell12763 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · have h := gap_lower (n := 12763) (a := (20776400831979 / 25000000000000 : ℝ)) (b := (161379073127 / 100000000000000 : ℝ)) (q := (560979015563 / 25000000000000 : ℝ))
      (E := (cell12763 ⟨28, by decide⟩).energy) (xi := (332389428519277 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12763 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12763]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12763])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12763) (a := (20776400831979 / 25000000000000 : ℝ)) (b := (161379073127 / 100000000000000 : ℝ)) (q := (560979015563 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12763])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12763])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12763]

theorem cert12763_29 : CellCertificate 12763 (884938874440489 / 10000000000000000 : ℝ) (1645725504509239 / 1000000000000000000 : ℝ) (332389428519277 / 10000000000000000 : ℝ)
    (cell12763 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · have h := gap_lower (n := 12763) (a := (83071332611261 / 100000000000000 : ℝ)) (b := (161379073127 / 100000000000000 : ℝ)) (q := (2243920069559 / 100000000000000 : ℝ))
      (E := (cell12763 ⟨29, by decide⟩).energy) (xi := (332389428519277 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12763 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12763]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12763])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12763) (a := (83071332611261 / 100000000000000 : ℝ)) (b := (161379073127 / 100000000000000 : ℝ)) (q := (2243920069559 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12763])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12763])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12763]

theorem cert12763_30 : CellCertificate 12763 (884938874440489 / 10000000000000000 : ℝ) (1645725504509239 / 1000000000000000000 : ℝ) (332389428519277 / 10000000000000000 : ℝ)
    (cell12763 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · have h := gap_lower (n := 12763) (a := (41518542924409 / 50000000000000 : ℝ)) (b := (161379073127 / 100000000000000 : ℝ)) (q := (2243924066191 / 100000000000000 : ℝ))
      (E := (cell12763 ⟨30, by decide⟩).energy) (xi := (332389428519277 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12763 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12763]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12763])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12763) (a := (41518542924409 / 50000000000000 : ℝ)) (b := (161379073127 / 100000000000000 : ℝ)) (q := (2243924066191 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12763])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12763])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12763]

theorem cert12763_31 : CellCertificate 12763 (884938874440489 / 10000000000000000 : ℝ) (1645725504509239 / 1000000000000000000 : ℝ) (332389428519277 / 10000000000000000 : ℝ)
    (cell12763 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · have h := gap_lower (n := 12763) (a := (41501431504539 / 50000000000000 : ℝ)) (b := (161379073127 / 100000000000000 : ℝ)) (q := (1121964056227 / 50000000000000 : ℝ))
      (E := (cell12763 ⟨31, by decide⟩).energy) (xi := (332389428519277 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12763 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12763]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12763])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12763) (a := (41501431504539 / 50000000000000 : ℝ)) (b := (161379073127 / 100000000000000 : ℝ)) (q := (1121964056227 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12763])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12763])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12763]

theorem cert12763_32 : CellCertificate 12763 (884938874440489 / 10000000000000000 : ℝ) (1645725504509239 / 1000000000000000000 : ℝ) (332389428519277 / 10000000000000000 : ℝ)
    (cell12763 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · have h := gap_lower (n := 12763) (a := (10371083007587 / 12500000000000 : ℝ)) (b := (161379073127 / 100000000000000 : ℝ)) (q := (2243932092823 / 100000000000000 : ℝ))
      (E := (cell12763 ⟨32, by decide⟩).energy) (xi := (332389428519277 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12763 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12763]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12763])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12763) (a := (10371083007587 / 12500000000000 : ℝ)) (b := (161379073127 / 100000000000000 : ℝ)) (q := (2243932092823 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12763])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12763])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12763]

theorem cert12763_33 : CellCertificate 12763 (884938874440489 / 10000000000000000 : ℝ) (1645725504509239 / 1000000000000000000 : ℝ) (332389428519277 / 10000000000000000 : ℝ)
    (cell12763 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · have h := gap_lower (n := 12763) (a := (82934488972483 / 100000000000000 : ℝ)) (b := (161379073127 / 100000000000000 : ℝ)) (q := (17951488537 / 800000000000 : ℝ))
      (E := (cell12763 ⟨33, by decide⟩).energy) (xi := (332389428519277 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12763 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12763]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12763])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12763) (a := (82934488972483 / 100000000000000 : ℝ)) (b := (161379073127 / 100000000000000 : ℝ)) (q := (17951488537 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12763])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12763])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12763]

theorem cert12763_34 : CellCertificate 12763 (884938874440489 / 10000000000000000 : ℝ) (1645725504509239 / 1000000000000000000 : ℝ) (332389428519277 / 10000000000000000 : ℝ)
    (cell12763 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · have h := gap_lower (n := 12763) (a := (20725084428353 / 25000000000000 : ℝ)) (b := (161379073127 / 100000000000000 : ℝ)) (q := (2243940095053 / 100000000000000 : ℝ))
      (E := (cell12763 ⟨34, by decide⟩).energy) (xi := (332389428519277 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12763 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12763]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12763])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12763) (a := (20725084428353 / 25000000000000 : ℝ)) (b := (161379073127 / 100000000000000 : ℝ)) (q := (2243940095053 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12763])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12763])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12763]

theorem cert12763_35 : CellCertificate 12763 (884938874440489 / 10000000000000000 : ℝ) (1645725504509239 / 1000000000000000000 : ℝ) (332389428519277 / 10000000000000000 : ℝ)
    (cell12763 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · have h := gap_lower (n := 12763) (a := (20716552563153 / 25000000000000 : ℝ)) (b := (161379073127 / 100000000000000 : ℝ)) (q := (1121972059449 / 50000000000000 : ℝ))
      (E := (cell12763 ⟨35, by decide⟩).energy) (xi := (332389428519277 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12763 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12763]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12763])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12763) (a := (20716552563153 / 25000000000000 : ℝ)) (b := (161379073127 / 100000000000000 : ℝ)) (q := (1121972059449 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12763])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12763])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12763]

theorem cert12763_36 : CellCertificate 12763 (884938874440489 / 10000000000000000 : ℝ) (1645725504509239 / 1000000000000000000 : ℝ) (332389428519277 / 10000000000000000 : ℝ)
    (cell12763 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · have h := gap_lower (n := 12763) (a := (82832106559367 / 100000000000000 : ℝ)) (b := (161379073127 / 100000000000000 : ℝ)) (q := (1121974040317 / 50000000000000 : ℝ))
      (E := (cell12763 ⟨36, by decide⟩).energy) (xi := (332389428519277 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12763 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12763]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12763])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12763) (a := (82832106559367 / 100000000000000 : ℝ)) (b := (161379073127 / 100000000000000 : ℝ)) (q := (1121974040317 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12763])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12763])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12763]

theorem cert12763_37 : CellCertificate 12763 (884938874440489 / 10000000000000000 : ℝ) (1645725504509239 / 1000000000000000000 : ℝ) (332389428519277 / 10000000000000000 : ℝ)
    (cell12763 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · have h := gap_lower (n := 12763) (a := (82798026603119 / 100000000000000 : ℝ)) (b := (161379073127 / 100000000000000 : ℝ)) (q := (2243952097963 / 100000000000000 : ℝ))
      (E := (cell12763 ⟨37, by decide⟩).energy) (xi := (332389428519277 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12763 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12763]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12763])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12763) (a := (82798026603119 / 100000000000000 : ℝ)) (b := (161379073127 / 100000000000000 : ℝ)) (q := (2243952097963 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12763])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12763])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12763]

theorem cert12763_38 : CellCertificate 12763 (884938874440489 / 10000000000000000 : ℝ) (1645725504509239 / 1000000000000000000 : ℝ) (332389428519277 / 10000000000000000 : ℝ)
    (cell12763 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · have h := gap_lower (n := 12763) (a := (16552794070693 / 20000000000000 : ℝ)) (b := (161379073127 / 100000000000000 : ℝ)) (q := (1121978056217 / 50000000000000 : ℝ))
      (E := (cell12763 ⟨38, by decide⟩).energy) (xi := (332389428519277 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12763 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12763]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12763])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12763) (a := (16552794070693 / 20000000000000 : ℝ)) (b := (161379073127 / 100000000000000 : ℝ)) (q := (1121978056217 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12763])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12763])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12763]

theorem cert12763_39 : CellCertificate 12763 (884938874440489 / 10000000000000000 : ℝ) (1645725504509239 / 1000000000000000000 : ℝ) (332389428519277 / 10000000000000000 : ℝ)
    (cell12763 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · have h := gap_lower (n := 12763) (a := (16545987556031 / 20000000000000 : ℝ)) (b := (161379073127 / 100000000000000 : ℝ)) (q := (280495015501 / 12500000000000 : ℝ))
      (E := (cell12763 ⟨39, by decide⟩).energy) (xi := (332389428519277 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12763 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12763]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12763])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12763) (a := (16545987556031 / 20000000000000 : ℝ)) (b := (161379073127 / 100000000000000 : ℝ)) (q := (280495015501 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12763])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12763])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12763]

theorem cert12764_20 : CellCertificate 12764 (221227800982737 / 2500000000000000 : ℝ) (1645596527394561 / 1000000000000000000 : ℝ) (332362758873483 / 10000000000000000 : ℝ)
    (cell12764 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · have h := gap_lower (n := 12764) (a := (3335225061461 / 4000000000000 : ℝ)) (b := (8068313863 / 5000000000000 : ℝ)) (q := (1121881690759 / 50000000000000 : ℝ))
      (E := (cell12764 ⟨20, by decide⟩).energy) (xi := (332362758873483 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12764 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12764]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12764])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12764) (a := (3335225061461 / 4000000000000 : ℝ)) (b := (8068313863 / 5000000000000 : ℝ)) (q := (1121881690759 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12764])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12764])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12764]

theorem cert12764_21 : CellCertificate 12764 (221227800982737 / 2500000000000000 : ℝ) (1645596527394561 / 1000000000000000000 : ℝ) (332362758873483 / 10000000000000000 : ℝ)
    (cell12764 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · have h := gap_lower (n := 12764) (a := (10418270417641 / 12500000000000 : ℝ)) (b := (8068313863 / 5000000000000 : ℝ)) (q := (1121883716513 / 50000000000000 : ℝ))
      (E := (cell12764 ⟨21, by decide⟩).energy) (xi := (332362758873483 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12764 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12764]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12764])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12764) (a := (10418270417641 / 12500000000000 : ℝ)) (b := (8068313863 / 5000000000000 : ℝ)) (q := (1121883716513 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12764])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12764])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12764]

theorem cert12764_22 : CellCertificate 12764 (221227800982737 / 2500000000000000 : ℝ) (1645596527394561 / 1000000000000000000 : ℝ) (332362758873483 / 10000000000000000 : ℝ)
    (cell12764 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · have h := gap_lower (n := 12764) (a := (2603491386171 / 3125000000000 : ℝ)) (b := (8068313863 / 5000000000000 : ℝ)) (q := (560942848423 / 25000000000000 : ℝ))
      (E := (cell12764 ⟨22, by decide⟩).energy) (xi := (332362758873483 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12764 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12764]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12764])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12764) (a := (2603491386171 / 3125000000000 : ℝ)) (b := (8068313863 / 5000000000000 : ℝ)) (q := (560942848423 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12764])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12764])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12764]

theorem cert12764_23 : CellCertificate 12764 (221227800982737 / 2500000000000000 : ℝ) (1645596527394561 / 1000000000000000000 : ℝ) (332362758873483 / 10000000000000000 : ℝ)
    (cell12764 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · have h := gap_lower (n := 12764) (a := (10409663694091 / 12500000000000 : ℝ)) (b := (8068313863 / 5000000000000 : ℝ)) (q := (280471930267 / 12500000000000 : ℝ))
      (E := (cell12764 ⟨23, by decide⟩).energy) (xi := (332362758873483 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12764 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12764]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12764])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12764) (a := (10409663694091 / 12500000000000 : ℝ)) (b := (8068313863 / 5000000000000 : ℝ)) (q := (280471930267 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12764])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12764])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12764]

theorem cert12764_24 : CellCertificate 12764 (221227800982737 / 2500000000000000 : ℝ) (1645596527394561 / 1000000000000000000 : ℝ) (332362758873483 / 10000000000000000 : ℝ)
    (cell12764 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · have h := gap_lower (n := 12764) (a := (83242918894239 / 100000000000000 : ℝ)) (b := (8068313863 / 5000000000000 : ℝ)) (q := (8975117627 / 400000000000 : ℝ))
      (E := (cell12764 ⟨24, by decide⟩).energy) (xi := (332362758873483 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12764 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12764]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12764])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12764) (a := (83242918894239 / 100000000000000 : ℝ)) (b := (8068313863 / 5000000000000 : ℝ)) (q := (8975117627 / 400000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12764])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12764])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12764]

theorem cert12764_25 : CellCertificate 12764 (221227800982737 / 2500000000000000 : ℝ) (1645596527394561 / 1000000000000000000 : ℝ) (332362758873483 / 10000000000000000 : ℝ)
    (cell12764 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · have h := gap_lower (n := 12764) (a := (41604276174757 / 50000000000000 : ℝ)) (b := (8068313863 / 5000000000000 : ℝ)) (q := (2243783407421 / 100000000000000 : ℝ))
      (E := (cell12764 ⟨25, by decide⟩).energy) (xi := (332362758873483 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12764 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12764]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12764])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12764) (a := (41604276174757 / 50000000000000 : ℝ)) (b := (8068313863 / 5000000000000 : ℝ)) (q := (2243783407421 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12764])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12764])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12764]

theorem cert12764_26 : CellCertificate 12764 (221227800982737 / 2500000000000000 : ℝ) (1645596527394561 / 1000000000000000000 : ℝ) (332362758873483 / 10000000000000000 : ℝ)
    (cell12764 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · have h := gap_lower (n := 12764) (a := (83174209886229 / 100000000000000 : ℝ)) (b := (8068313863 / 5000000000000 : ℝ)) (q := (1121893723569 / 50000000000000 : ℝ))
      (E := (cell12764 ⟨26, by decide⟩).energy) (xi := (332362758873483 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12764 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12764]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12764])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12764) (a := (83174209886229 / 100000000000000 : ℝ)) (b := (8068313863 / 5000000000000 : ℝ)) (q := (1121893723569 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12764])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12764])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12764]

theorem cert12764_27 : CellCertificate 12764 (221227800982737 / 2500000000000000 : ℝ) (1645596527394561 / 1000000000000000000 : ℝ) (332362758873483 / 10000000000000000 : ℝ)
    (cell12764 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · have h := gap_lower (n := 12764) (a := (83139891472223 / 100000000000000 : ℝ)) (b := (8068313863 / 5000000000000 : ℝ)) (q := (2243791411763 / 100000000000000 : ℝ))
      (E := (cell12764 ⟨27, by decide⟩).energy) (xi := (332362758873483 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12764 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12764]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12764])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12764) (a := (83139891472223 / 100000000000000 : ℝ)) (b := (8068313863 / 5000000000000 : ℝ)) (q := (2243791411763 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12764])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12764])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12764]

theorem cert12764_28 : CellCertificate 12764 (221227800982737 / 2500000000000000 : ℝ) (1645596527394561 / 1000000000000000000 : ℝ) (332362758873483 / 10000000000000000 : ℝ)
    (cell12764 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · have h := gap_lower (n := 12764) (a := (16621119415101 / 20000000000000 : ℝ)) (b := (8068313863 / 5000000000000 : ℝ)) (q := (2243795420619 / 100000000000000 : ℝ))
      (E := (cell12764 ⟨28, by decide⟩).energy) (xi := (332362758873483 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12764 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12764]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12764])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12764) (a := (16621119415101 / 20000000000000 : ℝ)) (b := (8068313863 / 5000000000000 : ℝ)) (q := (2243795420619 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12764])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12764])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12764]

theorem cert12764_29 : CellCertificate 12764 (221227800982737 / 2500000000000000 : ℝ) (1645596527394561 / 1000000000000000000 : ℝ) (332362758873483 / 10000000000000000 : ℝ)
    (cell12764 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · have h := gap_lower (n := 12764) (a := (41535663332121 / 50000000000000 : ℝ)) (b := (8068313863 / 5000000000000 : ℝ)) (q := (560949854377 / 25000000000000 : ℝ))
      (E := (cell12764 ⟨29, by decide⟩).energy) (xi := (332362758873483 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12764 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12764]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12764])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12764) (a := (41535663332121 / 50000000000000 : ℝ)) (b := (8068313863 / 5000000000000 : ℝ)) (q := (560949854377 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12764])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12764])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12764]

theorem cert12764_30 : CellCertificate 12764 (221227800982737 / 2500000000000000 : ℝ) (1645596527394561 / 1000000000000000000 : ℝ) (332362758873483 / 10000000000000000 : ℝ)
    (cell12764 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · have h := gap_lower (n := 12764) (a := (83037080206767 / 100000000000000 : ℝ)) (b := (8068313863 / 5000000000000 : ℝ)) (q := (112190173147 / 5000000000000 : ℝ))
      (E := (cell12764 ⟨30, by decide⟩).energy) (xi := (332362758873483 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12764 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12764]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12764])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12764) (a := (83037080206767 / 100000000000000 : ℝ)) (b := (8068313863 / 5000000000000 : ℝ)) (q := (112190173147 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12764])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12764])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12764]

theorem cert12764_31 : CellCertificate 12764 (221227800982737 / 2500000000000000 : ℝ) (1645596527394561 / 1000000000000000000 : ℝ) (332362758873483 / 10000000000000000 : ℝ)
    (cell12764 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · have h := gap_lower (n := 12764) (a := (41501428835787 / 50000000000000 : ℝ)) (b := (8068313863 / 5000000000000 : ℝ)) (q := (1121903720831 / 50000000000000 : ℝ))
      (E := (cell12764 ⟨31, by decide⟩).energy) (xi := (332362758873483 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12764 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12764]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12764])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12764) (a := (41501428835787 / 50000000000000 : ℝ)) (b := (8068313863 / 5000000000000 : ℝ)) (q := (1121903720831 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12764])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12764])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12764]

theorem cert12764_32 : CellCertificate 12764 (221227800982737 / 2500000000000000 : ℝ) (1645596527394561 / 1000000000000000000 : ℝ) (332362758873483 / 10000000000000000 : ℝ)
    (cell12764 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · have h := gap_lower (n := 12764) (a := (16593731805463 / 20000000000000 : ℝ)) (b := (8068313863 / 5000000000000 : ℝ)) (q := (2243811472273 / 100000000000000 : ℝ))
      (E := (cell12764 ⟨32, by decide⟩).energy) (xi := (332362758873483 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12764 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12764]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12764])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12764) (a := (16593731805463 / 20000000000000 : ℝ)) (b := (8068313863 / 5000000000000 : ℝ)) (q := (2243811472273 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12764])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12764])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12764]

theorem cert12764_33 : CellCertificate 12764 (221227800982737 / 2500000000000000 : ℝ) (1645596527394561 / 1000000000000000000 : ℝ) (332362758873483 / 10000000000000000 : ℝ)
    (cell12764 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · have h := gap_lower (n := 12764) (a := (41467242121403 / 50000000000000 : ℝ)) (b := (8068313863 / 5000000000000 : ℝ)) (q := (224381543897 / 10000000000000 : ℝ))
      (E := (cell12764 ⟨33, by decide⟩).energy) (xi := (332362758873483 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12764 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12764]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12764])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12764) (a := (41467242121403 / 50000000000000 : ℝ)) (b := (8068313863 / 5000000000000 : ℝ)) (q := (224381543897 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12764])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12764])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12764]

theorem cert12764_34 : CellCertificate 12764 (221227800982737 / 2500000000000000 : ℝ) (1645596527394561 / 1000000000000000000 : ℝ) (332362758873483 / 10000000000000000 : ℝ)
    (cell12764 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · have h := gap_lower (n := 12764) (a := (82900333287017 / 100000000000000 : ℝ)) (b := (8068313863 / 5000000000000 : ℝ)) (q := (280477432499 / 12500000000000 : ℝ))
      (E := (cell12764 ⟨34, by decide⟩).energy) (xi := (332362758873483 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12764 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12764]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12764])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12764) (a := (82900333287017 / 100000000000000 : ℝ)) (b := (8068313863 / 5000000000000 : ℝ)) (q := (280477432499 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12764])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12764])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12764]

theorem cert12764_35 : CellCertificate 12764 (221227800982737 / 2500000000000000 : ℝ) (1645596527394561 / 1000000000000000000 : ℝ) (332362758873483 / 10000000000000000 : ℝ)
    (cell12764 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · have h := gap_lower (n := 12764) (a := (82866206129079 / 100000000000000 : ℝ)) (b := (8068313863 / 5000000000000 : ℝ)) (q := (1121911738813 / 50000000000000 : ℝ))
      (E := (cell12764 ⟨35, by decide⟩).energy) (xi := (332362758873483 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12764 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12764]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12764])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12764) (a := (82866206129079 / 100000000000000 : ℝ)) (b := (8068313863 / 5000000000000 : ℝ)) (q := (1121911738813 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12764])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12764])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12764]

theorem cert12764_36 : CellCertificate 12764 (221227800982737 / 2500000000000000 : ℝ) (1645596527394561 / 1000000000000000000 : ℝ) (332362758873483 / 10000000000000000 : ℝ)
    (cell12764 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · have h := gap_lower (n := 12764) (a := (41416051369139 / 50000000000000 : ℝ)) (b := (8068313863 / 5000000000000 : ℝ)) (q := (280478436563 / 12500000000000 : ℝ))
      (E := (cell12764 ⟨36, by decide⟩).energy) (xi := (332362758873483 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12764 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12764]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12764])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12764) (a := (41416051369139 / 50000000000000 : ℝ)) (b := (8068313863 / 5000000000000 : ℝ)) (q := (280478436563 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12764])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12764])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12764]

theorem cert12764_37 : CellCertificate 12764 (221227800982737 / 2500000000000000 : ℝ) (1645596527394561 / 1000000000000000000 : ℝ) (332362758873483 / 10000000000000000 : ℝ)
    (cell12764 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · have h := gap_lower (n := 12764) (a := (10349752885507 / 12500000000000 : ℝ)) (b := (8068313863 / 5000000000000 : ℝ)) (q := (44876628927 / 2000000000000 : ℝ))
      (E := (cell12764 ⟨37, by decide⟩).energy) (xi := (332362758873483 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12764 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12764]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12764])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12764) (a := (10349752885507 / 12500000000000 : ℝ)) (b := (8068313863 / 5000000000000 : ℝ)) (q := (44876628927 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12764])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12764])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12764]

theorem cert12764_38 : CellCertificate 12764 (221227800982737 / 2500000000000000 : ℝ) (1645596527394561 / 1000000000000000000 : ℝ) (332362758873483 / 10000000000000000 : ℝ)
    (cell12764 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · have h := gap_lower (n := 12764) (a := (8276396713601 / 10000000000000 : ℝ)) (b := (8068313863 / 5000000000000 : ℝ)) (q := (2243835456691 / 100000000000000 : ℝ))
      (E := (cell12764 ⟨38, by decide⟩).energy) (xi := (332362758873483 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12764 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12764]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12764])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12764) (a := (8276396713601 / 10000000000000 : ℝ)) (b := (8068313863 / 5000000000000 : ℝ)) (q := (2243835456691 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12764])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12764])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12764]

theorem cert12764_39 : CellCertificate 12764 (221227800982737 / 2500000000000000 : ℝ) (1645596527394561 / 1000000000000000000 : ℝ) (332362758873483 / 10000000000000000 : ℝ)
    (cell12764 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · have h := gap_lower (n := 12764) (a := (20682483715973 / 25000000000000 : ℝ)) (b := (8068313863 / 5000000000000 : ℝ)) (q := (560959866207 / 25000000000000 : ℝ))
      (E := (cell12764 ⟨39, by decide⟩).energy) (xi := (332362758873483 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12764 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12764]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12764])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12764) (a := (20682483715973 / 25000000000000 : ℝ)) (b := (8068313863 / 5000000000000 : ℝ)) (q := (560959866207 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12764])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12764])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12764]

theorem cert12765_20 : CellCertificate 12765 (884883537582001 / 10000000000000000 : ℝ) (822733785247211 / 500000000000000000 : ℝ) (332336093560957 / 10000000000000000 : ℝ)
    (cell12765 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · have h := gap_lower (n := 12765) (a := (83380617827213 / 100000000000000 : ℝ)) (b := (32270696687 / 20000000000000 : ℝ)) (q := (448728557271 / 20000000000000 : ℝ))
      (E := (cell12765 ⟨20, by decide⟩).energy) (xi := (332336093560957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12765 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12765]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12765])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12765) (a := (83380617827213 / 100000000000000 : ℝ)) (b := (32270696687 / 20000000000000 : ℝ)) (q := (448728557271 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12765])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12765])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12765]

theorem cert12765_21 : CellCertificate 12765 (884883537582001 / 10000000000000000 : ℝ) (822733785247211 / 500000000000000000 : ℝ) (332336093560957 / 10000000000000000 : ℝ)
    (cell12765 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · have h := gap_lower (n := 12765) (a := (83346154940591 / 100000000000000 : ℝ)) (b := (32270696687 / 20000000000000 : ℝ)) (q := (560911705459 / 25000000000000 : ℝ))
      (E := (cell12765 ⟨21, by decide⟩).energy) (xi := (332336093560957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12765 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12765]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12765])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12765) (a := (83346154940591 / 100000000000000 : ℝ)) (b := (32270696687 / 20000000000000 : ℝ)) (q := (560911705459 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12765])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12765])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12765]

theorem cert12765_22 : CellCertificate 12765 (884883537582001 / 10000000000000000 : ℝ) (822733785247211 / 500000000000000000 : ℝ) (332336093560957 / 10000000000000000 : ℝ)
    (cell12765 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · have h := gap_lower (n := 12765) (a := (83311716265279 / 100000000000000 : ℝ)) (b := (32270696687 / 20000000000000 : ℝ)) (q := (280456353189 / 12500000000000 : ℝ))
      (E := (cell12765 ⟨22, by decide⟩).energy) (xi := (332336093560957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12765 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12765]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12765])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12765) (a := (83311716265279 / 100000000000000 : ℝ)) (b := (32270696687 / 20000000000000 : ℝ)) (q := (280456353189 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12765])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12765])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12765]

theorem cert12765_23 : CellCertificate 12765 (884883537582001 / 10000000000000000 : ℝ) (822733785247211 / 500000000000000000 : ℝ) (332336093560957 / 10000000000000000 : ℝ)
    (cell12765 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · have h := gap_lower (n := 12765) (a := (1665546035369 / 2000000000000 : ℝ)) (b := (32270696687 / 20000000000000 : ℝ)) (q := (2243654801007 / 100000000000000 : ℝ))
      (E := (cell12765 ⟨23, by decide⟩).energy) (xi := (332336093560957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12765 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12765]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12765])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12765) (a := (1665546035369 / 2000000000000 : ℝ)) (b := (32270696687 / 20000000000000 : ℝ)) (q := (2243654801007 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12765])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12765])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12765]

theorem cert12765_24 : CellCertificate 12765 (884883537582001 / 10000000000000000 : ℝ) (822733785247211 / 500000000000000000 : ℝ) (332336093560957 / 10000000000000000 : ℝ)
    (cell12765 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · have h := gap_lower (n := 12765) (a := (10405363927181 / 12500000000000 : ℝ)) (b := (32270696687 / 20000000000000 : ℝ)) (q := (1121829405043 / 50000000000000 : ℝ))
      (E := (cell12765 ⟨24, by decide⟩).energy) (xi := (332336093560957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12765 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12765]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12765])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12765) (a := (10405363927181 / 12500000000000 : ℝ)) (b := (32270696687 / 20000000000000 : ℝ)) (q := (1121829405043 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12765])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12765])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12765]

theorem cert12765_25 : CellCertificate 12765 (884883537582001 / 10000000000000000 : ℝ) (822733785247211 / 500000000000000000 : ℝ) (332336093560957 / 10000000000000000 : ℝ)
    (cell12765 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · have h := gap_lower (n := 12765) (a := (83208545179781 / 100000000000000 : ℝ)) (b := (32270696687 / 20000000000000 : ℝ)) (q := (2243662797571 / 100000000000000 : ℝ))
      (E := (cell12765 ⟨25, by decide⟩).energy) (xi := (332336093560957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12765 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12765]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12765])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12765) (a := (83208545179781 / 100000000000000 : ℝ)) (b := (32270696687 / 20000000000000 : ℝ)) (q := (2243662797571 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12765])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12765])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12765]

theorem cert12765_26 : CellCertificate 12765 (884883537582001 / 10000000000000000 : ℝ) (822733785247211 / 500000000000000000 : ℝ) (332336093560957 / 10000000000000000 : ℝ)
    (cell12765 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · have h := gap_lower (n := 12765) (a := (83174203023127 / 100000000000000 : ℝ)) (b := (32270696687 / 20000000000000 : ℝ)) (q := (448733364961 / 20000000000000 : ℝ))
      (E := (cell12765 ⟨26, by decide⟩).energy) (xi := (332336093560957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12765 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12765]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12765])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12765) (a := (83174203023127 / 100000000000000 : ℝ)) (b := (32270696687 / 20000000000000 : ℝ)) (q := (448733364961 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12765])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12765])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12765]

theorem cert12765_27 : CellCertificate 12765 (884883537582001 / 10000000000000000 : ℝ) (822733785247211 / 500000000000000000 : ℝ) (332336093560957 / 10000000000000000 : ℝ)
    (cell12765 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · have h := gap_lower (n := 12765) (a := (83139884915327 / 100000000000000 : ℝ)) (b := (32270696687 / 20000000000000 : ℝ)) (q := (448734167219 / 20000000000000 : ℝ))
      (E := (cell12765 ⟨27, by decide⟩).energy) (xi := (332336093560957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12765 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12765]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12765])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12765) (a := (83139884915327 / 100000000000000 : ℝ)) (b := (32270696687 / 20000000000000 : ℝ)) (q := (448734167219 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12765])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12765])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12765]

theorem cert12765_28 : CellCertificate 12765 (884883537582001 / 10000000000000000 : ℝ) (822733785247211 / 500000000000000000 : ℝ) (332336093560957 / 10000000000000000 : ℝ)
    (cell12765 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · have h := gap_lower (n := 12765) (a := (20776397706097 / 25000000000000 : ℝ)) (b := (32270696687 / 20000000000000 : ℝ)) (q := (448734966779 / 20000000000000 : ℝ))
      (E := (cell12765 ⟨28, by decide⟩).energy) (xi := (332336093560957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12765 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12765]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12765])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12765) (a := (20776397706097 / 25000000000000 : ℝ)) (b := (32270696687 / 20000000000000 : ℝ)) (q := (448734966779 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12765])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12765])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12765]

theorem cert12765_29 : CellCertificate 12765 (884883537582001 / 10000000000000000 : ℝ) (822733785247211 / 500000000000000000 : ℝ) (332336093560957 / 10000000000000000 : ℝ)
    (cell12765 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · have h := gap_lower (n := 12765) (a := (83071320718481 / 100000000000000 : ℝ)) (b := (32270696687 / 20000000000000 : ℝ)) (q := (89747152817 / 4000000000000 : ℝ))
      (E := (cell12765 ⟨29, by decide⟩).energy) (xi := (332336093560957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12765 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12765]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12765])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12765) (a := (83071320718481 / 100000000000000 : ℝ)) (b := (32270696687 / 20000000000000 : ℝ)) (q := (89747152817 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12765])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12765])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12765]

theorem cert12765_30 : CellCertificate 12765 (884883537582001 / 10000000000000000 : ℝ) (822733785247211 / 500000000000000000 : ℝ) (332336093560957 / 10000000000000000 : ℝ)
    (cell12765 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · have h := gap_lower (n := 12765) (a := (41518537282969 / 50000000000000 : ℝ)) (b := (32270696687 / 20000000000000 : ℝ)) (q := (1121841428099 / 50000000000000 : ℝ))
      (E := (cell12765 ⟨30, by decide⟩).energy) (xi := (332336093560957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12765 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12765]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12765])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12765) (a := (41518537282969 / 50000000000000 : ℝ)) (b := (32270696687 / 20000000000000 : ℝ)) (q := (1121841428099 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12765])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12765])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12765]

theorem cert12765_31 : CellCertificate 12765 (884883537582001 / 10000000000000000 : ℝ) (822733785247211 / 500000000000000000 : ℝ) (332336093560957 / 10000000000000000 : ℝ)
    (cell12765 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · have h := gap_lower (n := 12765) (a := (41501426167627 / 50000000000000 : ℝ)) (b := (32270696687 / 20000000000000 : ℝ)) (q := (56092170649 / 2500000000000 : ℝ))
      (E := (cell12765 ⟨31, by decide⟩).energy) (xi := (332336093560957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12765 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12765]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12765])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12765) (a := (41501426167627 / 50000000000000 : ℝ)) (b := (32270696687 / 20000000000000 : ℝ)) (q := (56092170649 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12765])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12765])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12765]

theorem cert12765_32 : CellCertificate 12765 (884883537582001 / 10000000000000000 : ℝ) (822733785247211 / 500000000000000000 : ℝ) (332336093560957 / 10000000000000000 : ℝ)
    (cell12765 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · have h := gap_lower (n := 12765) (a := (82968653995083 / 100000000000000 : ℝ)) (b := (32270696687 / 20000000000000 : ℝ)) (q := (560922712077 / 25000000000000 : ℝ))
      (E := (cell12765 ⟨32, by decide⟩).energy) (xi := (332336093560957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12765 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12765]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12765])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12765) (a := (82968653995083 / 100000000000000 : ℝ)) (b := (32270696687 / 20000000000000 : ℝ)) (q := (560922712077 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12765])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12765])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12765]

theorem cert12765_33 : CellCertificate 12765 (884883537582001 / 10000000000000000 : ℝ) (822733785247211 / 500000000000000000 : ℝ) (332336093560957 / 10000000000000000 : ℝ)
    (cell12765 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · have h := gap_lower (n := 12765) (a := (82934479514239 / 100000000000000 : ℝ)) (b := (32270696687 / 20000000000000 : ℝ)) (q := (224369486603 / 10000000000000 : ℝ))
      (E := (cell12765 ⟨33, by decide⟩).energy) (xi := (332336093560957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12765 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12765]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12765])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12765) (a := (82934479514239 / 100000000000000 : ℝ)) (b := (32270696687 / 20000000000000 : ℝ)) (q := (224369486603 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12765])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12765])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12765]

theorem cert12765_34 : CellCertificate 12765 (884883537582001 / 10000000000000000 : ℝ) (822733785247211 / 500000000000000000 : ℝ) (332336093560957 / 10000000000000000 : ℝ)
    (cell12765 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · have h := gap_lower (n := 12765) (a := (20239338101 / 24414062500 : ℝ)) (b := (32270696687 / 20000000000000 : ℝ)) (q := (448739776041 / 20000000000000 : ℝ))
      (E := (cell12765 ⟨34, by decide⟩).energy) (xi := (332336093560957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12765 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12765]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12765])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12765) (a := (20239338101 / 24414062500 : ℝ)) (b := (32270696687 / 20000000000000 : ℝ)) (q := (448739776041 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12765])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12765])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12765]

theorem cert12765_35 : CellCertificate 12765 (884883537582001 / 10000000000000000 : ℝ) (822733785247211 / 500000000000000000 : ℝ) (332336093560957 / 10000000000000000 : ℝ)
    (cell12765 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · have h := gap_lower (n := 12765) (a := (10358275250823 / 12500000000000 : ℝ)) (b := (32270696687 / 20000000000000 : ℝ)) (q := (560925708263 / 25000000000000 : ℝ))
      (E := (cell12765 ⟨35, by decide⟩).energy) (xi := (332336093560957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12765 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12765]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12765])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12765) (a := (10358275250823 / 12500000000000 : ℝ)) (b := (32270696687 / 20000000000000 : ℝ)) (q := (560925708263 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12765])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12765])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12765]

theorem cert12765_36 : CellCertificate 12765 (884883537582001 / 10000000000000000 : ℝ) (822733785247211 / 500000000000000000 : ℝ) (332336093560957 / 10000000000000000 : ℝ)
    (cell12765 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · have h := gap_lower (n := 12765) (a := (8283209891819 / 10000000000000 : ℝ)) (b := (32270696687 / 20000000000000 : ℝ)) (q := (2243706842451 / 100000000000000 : ℝ))
      (E := (cell12765 ⟨36, by decide⟩).energy) (xi := (332336093560957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12765 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12765]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12765])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12765) (a := (8283209891819 / 10000000000000 : ℝ)) (b := (32270696687 / 20000000000000 : ℝ)) (q := (2243706842451 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12765])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12765])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12765]

theorem cert12765_37 : CellCertificate 12765 (884883537582001 / 10000000000000000 : ℝ) (822733785247211 / 500000000000000000 : ℝ) (332336093560957 / 10000000000000000 : ℝ)
    (cell12765 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · have h := gap_lower (n := 12765) (a := (41399009782979 / 50000000000000 : ℝ)) (b := (32270696687 / 20000000000000 : ℝ)) (q := (2243710850193 / 100000000000000 : ℝ))
      (E := (cell12765 ⟨37, by decide⟩).energy) (xi := (332336093560957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12765 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12765]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12765])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12765) (a := (41399009782979 / 50000000000000 : ℝ)) (b := (32270696687 / 20000000000000 : ℝ)) (q := (2243710850193 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12765])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12765])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12765]

theorem cert12765_38 : CellCertificate 12765 (884883537582001 / 10000000000000000 : ℝ) (822733785247211 / 500000000000000000 : ℝ) (332336093560957 / 10000000000000000 : ℝ)
    (cell12765 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · have h := gap_lower (n := 12765) (a := (20690990979871 / 25000000000000 : ℝ)) (b := (32270696687 / 20000000000000 : ℝ)) (q := (448742971293 / 20000000000000 : ℝ))
      (E := (cell12765 ⟨38, by decide⟩).energy) (xi := (332336093560957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12765 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12765]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12765])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12765) (a := (20690990979871 / 25000000000000 : ℝ)) (b := (32270696687 / 20000000000000 : ℝ)) (q := (448742971293 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12765])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12765])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12765]

theorem cert12765_39 : CellCertificate 12765 (884883537582001 / 10000000000000000 : ℝ) (822733785247211 / 500000000000000000 : ℝ) (332336093560957 / 10000000000000000 : ℝ)
    (cell12765 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · have h := gap_lower (n := 12765) (a := (82729931948521 / 100000000000000 : ℝ)) (b := (32270696687 / 20000000000000 : ℝ)) (q := (89748754449 / 4000000000000 : ℝ))
      (E := (cell12765 ⟨39, by decide⟩).energy) (xi := (332336093560957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12765 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12765]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12765])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12765) (a := (82729931948521 / 100000000000000 : ℝ)) (b := (32270696687 / 20000000000000 : ℝ)) (q := (89748754449 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12765])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12765])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12765]

theorem cert12766_20 : CellCertificate 12766 (110606984424083 / 1250000000000000 : ℝ) (1645338633804069 / 1000000000000000000 : ℝ) (66461886516111 / 2000000000000000 : ℝ)
    (cell12766 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · have h := gap_lower (n := 12766) (a := (83380609119493 / 100000000000000 : ℝ)) (b := (161340691653 / 100000000000000 : ℝ)) (q := (2243522245607 / 100000000000000 : ℝ))
      (E := (cell12766 ⟨20, by decide⟩).energy) (xi := (66461886516111 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12766 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12766]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12766])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12766) (a := (83380609119493 / 100000000000000 : ℝ)) (b := (161340691653 / 100000000000000 : ℝ)) (q := (2243522245607 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12766])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12766])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12766]

theorem cert12766_21 : CellCertificate 12766 (110606984424083 / 1250000000000000 : ℝ) (1645338633804069 / 1000000000000000000 : ℝ) (66461886516111 / 2000000000000000 : ℝ)
    (cell12766 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · have h := gap_lower (n := 12766) (a := (10418268317701 / 12500000000000 : ℝ)) (b := (161340691653 / 100000000000000 : ℝ)) (q := (1121763103407 / 50000000000000 : ℝ))
      (E := (cell12766 ⟨21, by decide⟩).energy) (xi := (66461886516111 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12766 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12766]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12766])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12766) (a := (10418268317701 / 12500000000000 : ℝ)) (b := (161340691653 / 100000000000000 : ℝ)) (q := (1121763103407 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12766])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12766])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12766]

theorem cert12766_22 : CellCertificate 12766 (110606984424083 / 1250000000000000 : ℝ) (1645338633804069 / 1000000000000000000 : ℝ) (66461886516111 / 2000000000000000 : ℝ)
    (cell12766 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · have h := gap_lower (n := 12766) (a := (83311708174603 / 100000000000000 : ℝ)) (b := (161340691653 / 100000000000000 : ℝ)) (q := (1121765126769 / 50000000000000 : ℝ))
      (E := (cell12766 ⟨22, by decide⟩).energy) (xi := (66461886516111 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12766 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12766]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12766])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12766) (a := (83311708174603 / 100000000000000 : ℝ)) (b := (161340691653 / 100000000000000 : ℝ)) (q := (1121765126769 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12766])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12766])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12766]

theorem cert12766_23 : CellCertificate 12766 (110606984424083 / 1250000000000000 : ℝ) (1645338633804069 / 1000000000000000000 : ℝ) (66461886516111 / 2000000000000000 : ℝ)
    (cell12766 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · have h := gap_lower (n := 12766) (a := (20819323496413 / 25000000000000 : ℝ)) (b := (161340691653 / 100000000000000 : ℝ)) (q := (2243534214477 / 100000000000000 : ℝ))
      (E := (cell12766 ⟨23, by decide⟩).energy) (xi := (66461886516111 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12766 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12766]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12766])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12766) (a := (20819323496413 / 25000000000000 : ℝ)) (b := (161340691653 / 100000000000000 : ℝ)) (q := (2243534214477 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12766])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12766])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12766]

theorem cert12766_24 : CellCertificate 12766 (110606984424083 / 1250000000000000 : ℝ) (1645338633804069 / 1000000000000000000 : ℝ) (66461886516111 / 2000000000000000 : ℝ)
    (cell12766 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · have h := gap_lower (n := 12766) (a := (83242903942099 / 100000000000000 : ℝ)) (b := (161340691653 / 100000000000000 : ℝ)) (q := (448707641941 / 20000000000000 : ℝ))
      (E := (cell12766 ⟨24, by decide⟩).energy) (xi := (66461886516111 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12766 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12766]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12766])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12766) (a := (83242903942099 / 100000000000000 : ℝ)) (b := (161340691653 / 100000000000000 : ℝ)) (q := (448707641941 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12766])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12766])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12766]

theorem cert12766_25 : CellCertificate 12766 (110606984424083 / 1250000000000000 : ℝ) (1645338633804069 / 1000000000000000000 : ℝ) (66461886516111 / 2000000000000000 : ℝ)
    (cell12766 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · have h := gap_lower (n := 12766) (a := (83208538011453 / 100000000000000 : ℝ)) (b := (161340691653 / 100000000000000 : ℝ)) (q := (560885560611 / 25000000000000 : ℝ))
      (E := (cell12766 ⟨25, by decide⟩).energy) (xi := (66461886516111 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12766 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12766]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12766])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12766) (a := (83208538011453 / 100000000000000 : ℝ)) (b := (161340691653 / 100000000000000 : ℝ)) (q := (560885560611 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12766])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12766])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12766]

theorem cert12766_26 : CellCertificate 12766 (110606984424083 / 1250000000000000 : ℝ) (1645338633804069 / 1000000000000000000 : ℝ) (66461886516111 / 2000000000000000 : ℝ)
    (cell12766 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · have h := gap_lower (n := 12766) (a := (83174196161393 / 100000000000000 : ℝ)) (b := (161340691653 / 100000000000000 : ℝ)) (q := (280443282157 / 12500000000000 : ℝ))
      (E := (cell12766 ⟨26, by decide⟩).energy) (xi := (66461886516111 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12766 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12766]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12766])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12766) (a := (83174196161393 / 100000000000000 : ℝ)) (b := (161340691653 / 100000000000000 : ℝ)) (q := (280443282157 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12766])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12766])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12766]

theorem cert12766_27 : CellCertificate 12766 (110606984424083 / 1250000000000000 : ℝ) (1645338633804069 / 1000000000000000000 : ℝ) (66461886516111 / 2000000000000000 : ℝ)
    (cell12766 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · have h := gap_lower (n := 12766) (a := (41569939179881 / 50000000000000 : ℝ)) (b := (161340691653 / 100000000000000 : ℝ)) (q := (280443782103 / 12500000000000 : ℝ))
      (E := (cell12766 ⟨27, by decide⟩).energy) (xi := (66461886516111 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12766 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12766]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12766])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12766) (a := (41569939179881 / 50000000000000 : ℝ)) (b := (161340691653 / 100000000000000 : ℝ)) (q := (280443782103 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12766])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12766])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12766]

theorem cert12766_28 : CellCertificate 12766 (110606984424083 / 1250000000000000 : ℝ) (1645338633804069 / 1000000000000000000 : ℝ) (66461886516111 / 2000000000000000 : ℝ)
    (cell12766 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · have h := gap_lower (n := 12766) (a := (41552792287283 / 50000000000000 : ℝ)) (b := (161340691653 / 100000000000000 : ℝ)) (q := (560888560901 / 25000000000000 : ℝ))
      (E := (cell12766 ⟨28, by decide⟩).energy) (xi := (66461886516111 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12766 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12766]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12766])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12766) (a := (41552792287283 / 50000000000000 : ℝ)) (b := (161340691653 / 100000000000000 : ℝ)) (q := (560888560901 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12766])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12766])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12766]

theorem cert12766_29 : CellCertificate 12766 (110606984424083 / 1250000000000000 : ℝ) (1645338633804069 / 1000000000000000000 : ℝ) (66461886516111 / 2000000000000000 : ℝ)
    (cell12766 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · have h := gap_lower (n := 12766) (a := (41535657386989 / 50000000000000 : ℝ)) (b := (161340691653 / 100000000000000 : ℝ)) (q := (224355827831 / 10000000000000 : ℝ))
      (E := (cell12766 ⟨29, by decide⟩).energy) (xi := (66461886516111 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12766 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12766]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12766])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12766) (a := (41535657386989 / 50000000000000 : ℝ)) (b := (161340691653 / 100000000000000 : ℝ)) (q := (224355827831 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12766])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12766])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12766]

theorem cert12766_30 : CellCertificate 12766 (110606984424083 / 1250000000000000 : ℝ) (1645338633804069 / 1000000000000000000 : ℝ) (66461886516111 / 2000000000000000 : ℝ)
    (cell12766 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · have h := gap_lower (n := 12766) (a := (8303706892633 / 10000000000000 : ℝ)) (b := (161340691653 / 100000000000000 : ℝ)) (q := (1121781122983 / 50000000000000 : ℝ))
      (E := (cell12766 ⟨30, by decide⟩).energy) (xi := (66461886516111 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12766 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12766]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12766])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12766) (a := (8303706892633 / 10000000000000 : ℝ)) (b := (161340691653 / 100000000000000 : ℝ)) (q := (1121781122983 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12766])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12766])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12766]

theorem cert12766_31 : CellCertificate 12766 (110606984424083 / 1250000000000000 : ℝ) (1645338633804069 / 1000000000000000000 : ℝ) (66461886516111 / 2000000000000000 : ℝ)
    (cell12766 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · have h := gap_lower (n := 12766) (a := (41501423500059 / 50000000000000 : ℝ)) (b := (161340691653 / 100000000000000 : ℝ)) (q := (2243566265349 / 100000000000000 : ℝ))
      (E := (cell12766 ⟨31, by decide⟩).energy) (xi := (66461886516111 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12766 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12766]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12766])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12766) (a := (41501423500059 / 50000000000000 : ℝ)) (b := (161340691653 / 100000000000000 : ℝ)) (q := (2243566265349 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12766])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12766])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12766]

theorem cert12766_32 : CellCertificate 12766 (110606984424083 / 1250000000000000 : ℝ) (1645338633804069 / 1000000000000000000 : ℝ) (66461886516111 / 2000000000000000 : ℝ)
    (cell12766 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · have h := gap_lower (n := 12766) (a := (41484324481999 / 50000000000000 : ℝ)) (b := (161340691653 / 100000000000000 : ℝ)) (q := (448714055899 / 20000000000000 : ℝ))
      (E := (cell12766 ⟨32, by decide⟩).energy) (xi := (66461886516111 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12766 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12766]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12766])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12766) (a := (41484324481999 / 50000000000000 : ℝ)) (b := (161340691653 / 100000000000000 : ℝ)) (q := (448714055899 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12766])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12766])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12766]

theorem cert12766_33 : CellCertificate 12766 (110606984424083 / 1250000000000000 : ℝ) (1645338633804069 / 1000000000000000000 : ℝ) (66461886516111 / 2000000000000000 : ℝ)
    (cell12766 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · have h := gap_lower (n := 12766) (a := (82934474786783 / 100000000000000 : ℝ)) (b := (161340691653 / 100000000000000 : ℝ)) (q := (140223393107 / 6250000000000 : ℝ))
      (E := (cell12766 ⟨33, by decide⟩).energy) (xi := (66461886516111 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12766 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12766]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12766])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12766) (a := (82934474786783 / 100000000000000 : ℝ)) (b := (161340691653 / 100000000000000 : ℝ)) (q := (140223393107 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12766])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12766])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12766]

theorem cert12766_34 : CellCertificate 12766 (110606984424083 / 1250000000000000 : ℝ) (1645338633804069 / 1000000000000000000 : ℝ) (66461886516111 / 2000000000000000 : ℝ)
    (cell12766 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · have h := gap_lower (n := 12766) (a := (82900324437449 / 100000000000000 : ℝ)) (b := (161340691653 / 100000000000000 : ℝ)) (q := (2243578297079 / 100000000000000 : ℝ))
      (E := (cell12766 ⟨34, by decide⟩).energy) (xi := (66461886516111 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12766 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12766]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12766])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12766) (a := (82900324437449 / 100000000000000 : ℝ)) (b := (161340691653 / 100000000000000 : ℝ)) (q := (2243578297079 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12766])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12766])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12766]

theorem cert12766_35 : CellCertificate 12766 (110606984424083 / 1250000000000000 : ℝ) (1645338633804069 / 1000000000000000000 : ℝ) (66461886516111 / 2000000000000000 : ℝ)
    (cell12766 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · have h := gap_lower (n := 12766) (a := (82866197885127 / 100000000000000 : ℝ)) (b := (161340691653 / 100000000000000 : ℝ)) (q := (140223893903 / 6250000000000 : ℝ))
      (E := (cell12766 ⟨35, by decide⟩).energy) (xi := (66461886516111 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12766 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12766]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12766])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12766) (a := (82866197885127 / 100000000000000 : ℝ)) (b := (161340691653 / 100000000000000 : ℝ)) (q := (140223893903 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12766])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12766])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12766]

theorem cert12766_36 : CellCertificate 12766 (110606984424083 / 1250000000000000 : ℝ) (1645338633804069 / 1000000000000000000 : ℝ) (66461886516111 / 2000000000000000 : ℝ)
    (cell12766 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · have h := gap_lower (n := 12766) (a := (2588502971847 / 3125000000000 : ℝ)) (b := (161340691653 / 100000000000000 : ℝ)) (q := (2243586306451 / 100000000000000 : ℝ))
      (E := (cell12766 ⟨36, by decide⟩).energy) (xi := (66461886516111 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12766 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12766]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12766])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12766) (a := (2588502971847 / 3125000000000 : ℝ)) (b := (161340691653 / 100000000000000 : ℝ)) (q := (2243586306451 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12766])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12766])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12766]

theorem cert12766_37 : CellCertificate 12766 (110606984424083 / 1250000000000000 : ℝ) (1645338633804069 / 1000000000000000000 : ℝ) (66461886516111 / 2000000000000000 : ℝ)
    (cell12766 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · have h := gap_lower (n := 12766) (a := (10349752006103 / 12500000000000 : ℝ)) (b := (161340691653 / 100000000000000 : ℝ)) (q := (2243590309493 / 100000000000000 : ℝ))
      (E := (cell12766 ⟨37, by decide⟩).energy) (xi := (66461886516111 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12766 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12766]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12766])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12766) (a := (10349752006103 / 12500000000000 : ℝ)) (b := (161340691653 / 100000000000000 : ℝ)) (q := (2243590309493 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12766])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12766])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12766]

theorem cert12766_38 : CellCertificate 12766 (110606984424083 / 1250000000000000 : ℝ) (1645338633804069 / 1000000000000000000 : ℝ) (66461886516111 / 2000000000000000 : ℝ)
    (cell12766 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · have h := gap_lower (n := 12766) (a := (41381980351943 / 50000000000000 : ℝ)) (b := (161340691653 / 100000000000000 : ℝ)) (q := (448718862351 / 20000000000000 : ℝ))
      (E := (cell12766 ⟨38, by decide⟩).energy) (xi := (66461886516111 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12766 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12766]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12766])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12766) (a := (41381980351943 / 50000000000000 : ℝ)) (b := (161340691653 / 100000000000000 : ℝ)) (q := (448718862351 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12766])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12766])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12766]

theorem cert12766_39 : CellCertificate 12766 (110606984424083 / 1250000000000000 : ℝ) (1645338633804069 / 1000000000000000000 : ℝ) (66461886516111 / 2000000000000000 : ℝ)
    (cell12766 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · have h := gap_lower (n := 12766) (a := (41364964517021 / 50000000000000 : ℝ)) (b := (161340691653 / 100000000000000 : ℝ)) (q := (2243598313199 / 100000000000000 : ℝ))
      (E := (cell12766 ⟨39, by decide⟩).energy) (xi := (66461886516111 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12766 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12766]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12766])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12766) (a := (41364964517021 / 50000000000000 : ℝ)) (b := (161340691653 / 100000000000000 : ℝ)) (q := (2243598313199 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12766])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12766])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12766]

theorem cert12767_20 : CellCertificate 12767 (884828217361953 / 10000000000000000 : ℝ) (1645209717318753 / 1000000000000000000 : ℝ) (332282775931137 / 10000000000000000 : ℝ)
    (cell12767 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · have h := gap_lower (n := 12767) (a := (20845150103341 / 25000000000000 : ℝ)) (b := (161327901911 / 100000000000000 : ℝ)) (q := (17526575789 / 781250000000 : ℝ))
      (E := (cell12767 ⟨20, by decide⟩).energy) (xi := (332282775931137 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12767 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12767]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12767])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12767) (a := (20845150103341 / 25000000000000 : ℝ)) (b := (161327901911 / 100000000000000 : ℝ)) (q := (17526575789 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12767])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12767])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12767]

theorem cert12767_21 : CellCertificate 12767 (884828217361953 / 10000000000000000 : ℝ) (1645209717318753 / 1000000000000000000 : ℝ) (332282775931137 / 10000000000000000 : ℝ)
    (cell12767 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · have h := gap_lower (n := 12767) (a := (83346138144179 / 100000000000000 : ℝ)) (b := (161327901911 / 100000000000000 : ℝ)) (q := (112170285229 / 5000000000000 : ℝ))
      (E := (cell12767 ⟨21, by decide⟩).energy) (xi := (332282775931137 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12767 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12767]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12767])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12767) (a := (83346138144179 / 100000000000000 : ℝ)) (b := (161327901911 / 100000000000000 : ℝ)) (q := (112170285229 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12767])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12767])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12767]

theorem cert12767_22 : CellCertificate 12767 (884828217361953 / 10000000000000000 : ℝ) (1645209717318753 / 1000000000000000000 : ℝ) (332282775931137 / 10000000000000000 : ℝ)
    (cell12767 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · have h := gap_lower (n := 12767) (a := (20827925021361 / 25000000000000 : ℝ)) (b := (161327901911 / 100000000000000 : ℝ)) (q := (1121704838887 / 50000000000000 : ℝ))
      (E := (cell12767 ⟨22, by decide⟩).energy) (xi := (332282775931137 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12767 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12767]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12767])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12767) (a := (20827925021361 / 25000000000000 : ℝ)) (b := (161327901911 / 100000000000000 : ℝ)) (q := (1121704838887 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12767])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12767])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12767]

theorem cert12767_23 : CellCertificate 12767 (884828217361953 / 10000000000000000 : ℝ) (1645209717318753 / 1000000000000000000 : ℝ) (332282775931137 / 10000000000000000 : ℝ)
    (cell12767 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · have h := gap_lower (n := 12767) (a := (83277286204333 / 100000000000000 : ℝ)) (b := (161327901911 / 100000000000000 : ℝ)) (q := (2243413682551 / 100000000000000 : ℝ))
      (E := (cell12767 ⟨23, by decide⟩).energy) (xi := (332282775931137 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12767 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12767]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12767])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12767) (a := (83277286204333 / 100000000000000 : ℝ)) (b := (161327901911 / 100000000000000 : ℝ)) (q := (2243413682551 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12767])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12767])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12767]

theorem cert12767_24 : CellCertificate 12767 (884828217361953 / 10000000000000000 : ℝ) (1645209717318753 / 1000000000000000000 : ℝ) (332282775931137 / 10000000000000000 : ℝ)
    (cell12767 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · have h := gap_lower (n := 12767) (a := (2601340514631 / 3125000000000 : ℝ)) (b := (161327901911 / 100000000000000 : ℝ)) (q := (2243417663989 / 100000000000000 : ℝ))
      (E := (cell12767 ⟨24, by decide⟩).energy) (xi := (332282775931137 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12767 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12767]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12767])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12767) (a := (2601340514631 / 3125000000000 : ℝ)) (b := (161327901911 / 100000000000000 : ℝ)) (q := (2243417663989 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12767])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12767])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12767]

theorem cert12767_25 : CellCertificate 12767 (884828217361953 / 10000000000000000 : ℝ) (1645209717318753 / 1000000000000000000 : ℝ) (332282775931137 / 10000000000000000 : ℝ)
    (cell12767 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · have h := gap_lower (n := 12767) (a := (8320853084453 / 10000000000000 : ℝ)) (b := (161327901911 / 100000000000000 : ℝ)) (q := (2243421683641 / 100000000000000 : ℝ))
      (E := (cell12767 ⟨25, by decide⟩).energy) (xi := (332282775931137 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12767 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12767]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12767])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12767) (a := (8320853084453 / 10000000000000 : ℝ)) (b := (161327901911 / 100000000000000 : ℝ)) (q := (2243421683641 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12767])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12767])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12767]

theorem cert12767_26 : CellCertificate 12767 (884828217361953 / 10000000000000000 : ℝ) (1645209717318753 / 1000000000000000000 : ℝ) (332282775931137 / 10000000000000000 : ℝ)
    (cell12767 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · have h := gap_lower (n := 12767) (a := (20793547325257 / 25000000000000 : ℝ)) (b := (161327901911 / 100000000000000 : ℝ)) (q := (560856421517 / 25000000000000 : ℝ))
      (E := (cell12767 ⟨26, by decide⟩).energy) (xi := (332282775931137 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12767 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12767]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12767])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12767) (a := (20793547325257 / 25000000000000 : ℝ)) (b := (161327901911 / 100000000000000 : ℝ)) (q := (560856421517 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12767])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12767])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12767]

theorem cert12767_27 : CellCertificate 12767 (884828217361953 / 10000000000000000 : ℝ) (1645209717318753 / 1000000000000000000 : ℝ) (332282775931137 / 10000000000000000 : ℝ)
    (cell12767 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · have h := gap_lower (n := 12767) (a := (10392483975691 / 12500000000000 : ℝ)) (b := (161327901911 / 100000000000000 : ℝ)) (q := (1121714836977 / 50000000000000 : ℝ))
      (E := (cell12767 ⟨27, by decide⟩).energy) (xi := (332282775931137 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12767 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12767]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12767])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12767) (a := (10392483975691 / 12500000000000 : ℝ)) (b := (161327901911 / 100000000000000 : ℝ)) (q := (1121714836977 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12767])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12767])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12767]

theorem cert12767_28 : CellCertificate 12767 (884828217361953 / 10000000000000000 : ℝ) (1645209717318753 / 1000000000000000000 : ℝ) (332282775931137 / 10000000000000000 : ℝ)
    (cell12767 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · have h := gap_lower (n := 12767) (a := (41552789163019 / 50000000000000 : ℝ)) (b := (161327901911 / 100000000000000 : ℝ)) (q := (35053651691 / 1562500000000 : ℝ))
      (E := (cell12767 ⟨28, by decide⟩).energy) (xi := (332282775931137 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12767 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12767]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12767])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12767) (a := (41552789163019 / 50000000000000 : ℝ)) (b := (161327901911 / 100000000000000 : ℝ)) (q := (35053651691 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12767])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12767])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12767]

theorem cert12767_29 : CellCertificate 12767 (884828217361953 / 10000000000000000 : ℝ) (1645209717318753 / 1000000000000000000 : ℝ) (332282775931137 / 10000000000000000 : ℝ)
    (cell12767 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · have h := gap_lower (n := 12767) (a := (20767827207683 / 25000000000000 : ℝ)) (b := (161327901911 / 100000000000000 : ℝ)) (q := (2243437732671 / 100000000000000 : ℝ))
      (E := (cell12767 ⟨29, by decide⟩).energy) (xi := (332282775931137 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12767 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12767]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12767])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12767) (a := (20767827207683 / 25000000000000 : ℝ)) (b := (161327901911 / 100000000000000 : ℝ)) (q := (2243437732671 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12767])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12767])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12767]

theorem cert12767_30 : CellCertificate 12767 (884828217361953 / 10000000000000000 : ℝ) (1645209717318753 / 1000000000000000000 : ℝ) (332282775931137 / 10000000000000000 : ℝ)
    (cell12767 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · have h := gap_lower (n := 12767) (a := (83037063287943 / 100000000000000 : ℝ)) (b := (161327901911 / 100000000000000 : ℝ)) (q := (2243441690767 / 100000000000000 : ℝ))
      (E := (cell12767 ⟨30, by decide⟩).energy) (xi := (332282775931137 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12767 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12767]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12767])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12767) (a := (83037063287943 / 100000000000000 : ℝ)) (b := (161327901911 / 100000000000000 : ℝ)) (q := (2243441690767 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12767])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12767])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12767]

theorem cert12767_31 : CellCertificate 12767 (884828217361953 / 10000000000000000 : ℝ) (1645209717318753 / 1000000000000000000 : ℝ) (332282775931137 / 10000000000000000 : ℝ)
    (cell12767 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · have h := gap_lower (n := 12767) (a := (83002841666167 / 100000000000000 : ℝ)) (b := (161327901911 / 100000000000000 : ℝ)) (q := (2243445701287 / 100000000000000 : ℝ))
      (E := (cell12767 ⟨31, by decide⟩).energy) (xi := (332282775931137 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12767 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12767]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12767])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12767) (a := (83002841666167 / 100000000000000 : ℝ)) (b := (161327901911 / 100000000000000 : ℝ)) (q := (2243445701287 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12767])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12767])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12767]

theorem cert12767_32 : CellCertificate 12767 (884828217361953 / 10000000000000000 : ℝ) (1645209717318753 / 1000000000000000000 : ℝ) (332282775931137 / 10000000000000000 : ℝ)
    (cell12767 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · have h := gap_lower (n := 12767) (a := (4148432196703 / 5000000000000 : ℝ)) (b := (161327901911 / 100000000000000 : ℝ)) (q := (224344970727 / 10000000000000 : ℝ))
      (E := (cell12767 ⟨32, by decide⟩).energy) (xi := (332282775931137 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12767 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12767]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12767])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12767) (a := (4148432196703 / 5000000000000 : ℝ)) (b := (161327901911 / 100000000000000 : ℝ)) (q := (224344970727 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12767])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12767])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12767]

theorem cert12767_33 : CellCertificate 12767 (884828217361953 / 10000000000000000 : ℝ) (1645209717318753 / 1000000000000000000 : ℝ) (332282775931137 / 10000000000000000 : ℝ)
    (cell12767 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · have h := gap_lower (n := 12767) (a := (41467235030219 / 50000000000000 : ℝ)) (b := (161327901911 / 100000000000000 : ℝ)) (q := (112172685501 / 5000000000000 : ℝ))
      (E := (cell12767 ⟨33, by decide⟩).energy) (xi := (332282775931137 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12767 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12767]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12767])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12767) (a := (41467235030219 / 50000000000000 : ℝ)) (b := (161327901911 / 100000000000000 : ℝ)) (q := (112172685501 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12767])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12767])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12767]

theorem cert12767_34 : CellCertificate 12767 (884828217361953 / 10000000000000000 : ℝ) (1645209717318753 / 1000000000000000000 : ℝ) (332282775931137 / 10000000000000000 : ℝ)
    (cell12767 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · have h := gap_lower (n := 12767) (a := (82900320014277 / 100000000000000 : ℝ)) (b := (161327901911 / 100000000000000 : ℝ)) (q := (1121728855307 / 50000000000000 : ℝ))
      (E := (cell12767 ⟨34, by decide⟩).energy) (xi := (332282775931137 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12767 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12767]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12767])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12767) (a := (82900320014277 / 100000000000000 : ℝ)) (b := (161327901911 / 100000000000000 : ℝ)) (q := (1121728855307 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12767])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12767])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12767]

theorem cert12767_35 : CellCertificate 12767 (884828217361953 / 10000000000000000 : ℝ) (1645209717318753 / 1000000000000000000 : ℝ) (332282775931137 / 10000000000000000 : ℝ)
    (cell12767 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · have h := gap_lower (n := 12767) (a := (82866193764707 / 100000000000000 : ℝ)) (b := (161327901911 / 100000000000000 : ℝ)) (q := (2243461709909 / 100000000000000 : ℝ))
      (E := (cell12767 ⟨35, by decide⟩).energy) (xi := (332282775931137 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12767 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12767]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12767])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12767) (a := (82866193764707 / 100000000000000 : ℝ)) (b := (161327901911 / 100000000000000 : ℝ)) (q := (2243461709909 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12767])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12767])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12767]

theorem cert12767_36 : CellCertificate 12767 (884828217361953 / 10000000000000000 : ℝ) (1645209717318753 / 1000000000000000000 : ℝ) (332282775931137 / 10000000000000000 : ℝ)
    (cell12767 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · have h := gap_lower (n := 12767) (a := (82832091281019 / 100000000000000 : ℝ)) (b := (161327901911 / 100000000000000 : ℝ)) (q := (224346576719 / 10000000000000 : ℝ))
      (E := (cell12767 ⟨36, by decide⟩).energy) (xi := (332282775931137 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12767 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12767]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12767])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12767) (a := (82832091281019 / 100000000000000 : ℝ)) (b := (161327901911 / 100000000000000 : ℝ)) (q := (224346576719 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12767])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12767])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12767]

theorem cert12767_37 : CellCertificate 12767 (884828217361953 / 10000000000000000 : ℝ) (1645209717318753 / 1000000000000000000 : ℝ) (332282775931137 / 10000000000000000 : ℝ)
    (cell12767 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · have h := gap_lower (n := 12767) (a := (16559602506531 / 20000000000000 : ℝ)) (b := (161327901911 / 100000000000000 : ℝ)) (q := (2243469765567 / 100000000000000 : ℝ))
      (E := (cell12767 ⟨37, by decide⟩).energy) (xi := (332282775931137 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12767 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12767]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12767])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12767) (a := (16559602506531 / 20000000000000 : ℝ)) (b := (161327901911 / 100000000000000 : ℝ)) (q := (2243469765567 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12767])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12767])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12767]

theorem cert12767_38 : CellCertificate 12767 (884828217361953 / 10000000000000000 : ℝ) (1645209717318753 / 1000000000000000000 : ℝ) (332282775931137 / 10000000000000000 : ℝ)
    (cell12767 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · have h := gap_lower (n := 12767) (a := (82763957489217 / 100000000000000 : ℝ)) (b := (161327901911 / 100000000000000 : ℝ)) (q := (2243473763857 / 100000000000000 : ℝ))
      (E := (cell12767 ⟨38, by decide⟩).energy) (xi := (332282775931137 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12767 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12767]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12767])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12767) (a := (82763957489217 / 100000000000000 : ℝ)) (b := (161327901911 / 100000000000000 : ℝ)) (q := (2243473763857 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12767])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12767])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12767]

theorem cert12767_39 : CellCertificate 12767 (884828217361953 / 10000000000000000 : ℝ) (1645209717318753 / 1000000000000000000 : ℝ) (332282775931137 / 10000000000000000 : ℝ)
    (cell12767 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · have h := gap_lower (n := 12767) (a := (10341240765057 / 12500000000000 : ℝ)) (b := (161327901911 / 100000000000000 : ℝ)) (q := (1121738881011 / 50000000000000 : ℝ))
      (E := (cell12767 ⟨39, by decide⟩).energy) (xi := (332282775931137 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12767 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12767]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12767])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12767) (a := (10341240765057 / 12500000000000 : ℝ)) (b := (161327901911 / 100000000000000 : ℝ)) (q := (1121738881011 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12767])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12767])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12767]

theorem cert12768_20 : CellCertificate 12768 (176960112697777 / 2000000000000000 : ℝ) (411270205258431 / 250000000000000000 : ℝ) (166128061805781 / 5000000000000000 : ℝ)
    (cell12768 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · have h := gap_lower (n := 12768) (a := (41690295854413 / 50000000000000 : ℝ)) (b := (16131511421 / 10000000000000 : ℝ)) (q := (2243281152511 / 100000000000000 : ℝ))
      (E := (cell12768 ⟨20, by decide⟩).energy) (xi := (166128061805781 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12768 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12768]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12768])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12768) (a := (41690295854413 / 50000000000000 : ℝ)) (b := (16131511421 / 10000000000000 : ℝ)) (q := (2243281152511 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12768])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12768])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12768]

theorem cert12768_21 : CellCertificate 12768 (176960112697777 / 2000000000000000 : ℝ) (411270205258431 / 250000000000000000 : ℝ) (166128061805781 / 5000000000000000 : ℝ)
    (cell12768 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · have h := gap_lower (n := 12768) (a := (5209133109269 / 6250000000000 : ℝ)) (b := (16131511421 / 10000000000000 : ℝ)) (q := (1121642599259 / 50000000000000 : ℝ))
      (E := (cell12768 ⟨21, by decide⟩).energy) (xi := (166128061805781 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12768 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12768]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12768])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12768) (a := (5209133109269 / 6250000000000 : ℝ)) (b := (16131511421 / 10000000000000 : ℝ)) (q := (1121642599259 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12768])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12768])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12768]

theorem cert12768_22 : CellCertificate 12768 (176960112697777 / 2000000000000000 : ℝ) (411270205258431 / 250000000000000000 : ℝ) (166128061805781 / 5000000000000000 : ℝ)
    (cell12768 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · have h := gap_lower (n := 12768) (a := (83311691997801 / 100000000000000 : ℝ)) (b := (16131511421 / 10000000000000 : ℝ)) (q := (2243289156551 / 100000000000000 : ℝ))
      (E := (cell12768 ⟨22, by decide⟩).energy) (xi := (166128061805781 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12768 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12768]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12768])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12768) (a := (83311691997801 / 100000000000000 : ℝ)) (b := (16131511421 / 10000000000000 : ℝ)) (q := (2243289156551 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12768])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12768])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12768]

theorem cert12768_23 : CellCertificate 12768 (176960112697777 / 2000000000000000 : ℝ) (411270205258431 / 250000000000000000 : ℝ) (166128061805781 / 5000000000000000 : ℝ)
    (cell12768 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · have h := gap_lower (n := 12768) (a := (83277278424493 / 100000000000000 : ℝ)) (b := (16131511421 / 10000000000000 : ℝ)) (q := (2243293146873 / 100000000000000 : ℝ))
      (E := (cell12768 ⟨23, by decide⟩).energy) (xi := (166128061805781 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12768 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12768]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12768])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12768) (a := (83277278424493 / 100000000000000 : ℝ)) (b := (16131511421 / 10000000000000 : ℝ)) (q := (2243293146873 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12768])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12768])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12768]

theorem cert12768_24 : CellCertificate 12768 (176960112697777 / 2000000000000000 : ℝ) (411270205258431 / 250000000000000000 : ℝ) (166128061805781 / 5000000000000000 : ℝ)
    (cell12768 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · have h := gap_lower (n := 12768) (a := (41621444497863 / 50000000000000 : ℝ)) (b := (16131511421 / 10000000000000 : ℝ)) (q := (1121648586469 / 50000000000000 : ℝ))
      (E := (cell12768 ⟨24, by decide⟩).energy) (xi := (166128061805781 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12768 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12768]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12768])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12768) (a := (41621444497863 / 50000000000000 : ℝ)) (b := (16131511421 / 10000000000000 : ℝ)) (q := (1121648586469 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12768])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12768])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12768]

theorem cert12768_25 : CellCertificate 12768 (176960112697777 / 2000000000000000 : ℝ) (411270205258431 / 250000000000000000 : ℝ) (166128061805781 / 5000000000000000 : ℝ)
    (cell12768 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · have h := gap_lower (n := 12768) (a := (20802130919753 / 25000000000000 : ℝ)) (b := (16131511421 / 10000000000000 : ℝ)) (q := (560825294891 / 25000000000000 : ℝ))
      (E := (cell12768 ⟨25, by decide⟩).energy) (xi := (166128061805781 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12768 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12768]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12768])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12768) (a := (20802130919753 / 25000000000000 : ℝ)) (b := (16131511421 / 10000000000000 : ℝ)) (q := (560825294891 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12768])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12768])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12768]

theorem cert12768_26 : CellCertificate 12768 (176960112697777 / 2000000000000000 : ℝ) (411270205258431 / 250000000000000000 : ℝ) (166128061805781 / 5000000000000000 : ℝ)
    (cell12768 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · have h := gap_lower (n := 12768) (a := (8317418244203 / 10000000000000 : ℝ)) (b := (16131511421 / 10000000000000 : ℝ)) (q := (560826292417 / 25000000000000 : ℝ))
      (E := (cell12768 ⟨26, by decide⟩).energy) (xi := (166128061805781 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12768 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12768]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12768])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12768) (a := (8317418244203 / 10000000000000 : ℝ)) (b := (16131511421 / 10000000000000 : ℝ)) (q := (560826292417 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12768])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12768])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12768]

theorem cert12768_27 : CellCertificate 12768 (176960112697777 / 2000000000000000 : ℝ) (411270205258431 / 250000000000000000 : ℝ) (166128061805781 / 5000000000000000 : ℝ)
    (cell12768 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · have h := gap_lower (n := 12768) (a := (5196241578289 / 6250000000000 : ℝ)) (b := (16131511421 / 10000000000000 : ℝ)) (q := (1121654602191 / 50000000000000 : ℝ))
      (E := (cell12768 ⟨27, by decide⟩).energy) (xi := (166128061805781 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12768 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12768]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12768])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12768) (a := (5196241578289 / 6250000000000 : ℝ)) (b := (16131511421 / 10000000000000 : ℝ)) (q := (1121654602191 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12768])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12768])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12768]

theorem cert12768_28 : CellCertificate 12768 (176960112697777 / 2000000000000000 : ℝ) (411270205258431 / 250000000000000000 : ℝ) (166128061805781 / 5000000000000000 : ℝ)
    (cell12768 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · have h := gap_lower (n := 12768) (a := (16621114415761 / 20000000000000 : ℝ)) (b := (16131511421 / 10000000000000 : ℝ)) (q := (3505176827 / 156250000000 : ℝ))
      (E := (cell12768 ⟨28, by decide⟩).energy) (xi := (166128061805781 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12768 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12768]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12768])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12768) (a := (16621114415761 / 20000000000000 : ℝ)) (b := (16131511421 / 10000000000000 : ℝ)) (q := (3505176827 / 156250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12768])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12768])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12768]

theorem cert12768_29 : CellCertificate 12768 (176960112697777 / 2000000000000000 : ℝ) (411270205258431 / 250000000000000000 : ℝ) (166128061805781 / 5000000000000000 : ℝ)
    (cell12768 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · have h := gap_lower (n := 12768) (a := (83071302888743 / 100000000000000 : ℝ)) (b := (16131511421 / 10000000000000 : ℝ)) (q := (2243317183507 / 100000000000000 : ℝ))
      (E := (cell12768 ⟨29, by decide⟩).energy) (xi := (166128061805781 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12768 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12768]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12768])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12768) (a := (83071302888743 / 100000000000000 : ℝ)) (b := (16131511421 / 10000000000000 : ℝ)) (q := (2243317183507 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12768])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12768])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12768]

theorem cert12768_30 : CellCertificate 12768 (176960112697777 / 2000000000000000 : ℝ) (411270205258431 / 250000000000000000 : ℝ) (166128061805781 / 5000000000000000 : ℝ)
    (cell12768 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · have h := gap_lower (n := 12768) (a := (10379632206347 / 12500000000000 : ℝ)) (b := (16131511421 / 10000000000000 : ℝ)) (q := (2243321190599 / 100000000000000 : ℝ))
      (E := (cell12768 ⟨30, by decide⟩).energy) (xi := (166128061805781 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12768 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12768]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12768])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12768) (a := (10379632206347 / 12500000000000 : ℝ)) (b := (16131511421 / 10000000000000 : ℝ)) (q := (2243321190599 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12768])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12768])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12768]

theorem cert12768_31 : CellCertificate 12768 (176960112697777 / 2000000000000000 : ℝ) (411270205258431 / 250000000000000000 : ℝ) (166128061805781 / 5000000000000000 : ℝ)
    (cell12768 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · have h := gap_lower (n := 12768) (a := (41501418166699 / 50000000000000 : ℝ)) (b := (16131511421 / 10000000000000 : ℝ)) (q := (3505195613 / 156250000000 : ℝ))
      (E := (cell12768 ⟨31, by decide⟩).energy) (xi := (166128061805781 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12768 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12768]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12768])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12768) (a := (41501418166699 / 50000000000000 : ℝ)) (b := (16131511421 / 10000000000000 : ℝ)) (q := (3505195613 / 156250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12768])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12768])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12768]

theorem cert12768_32 : CellCertificate 12768 (176960112697777 / 2000000000000000 : ℝ) (411270205258431 / 250000000000000000 : ℝ) (166128061805781 / 5000000000000000 : ℝ)
    (cell12768 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · have h := gap_lower (n := 12768) (a := (82968638905269 / 100000000000000 : ℝ)) (b := (16131511421 / 10000000000000 : ℝ)) (q := (2243329190199 / 100000000000000 : ℝ))
      (E := (cell12768 ⟨32, by decide⟩).energy) (xi := (166128061805781 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12768 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12768]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12768])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12768) (a := (82968638905269 / 100000000000000 : ℝ)) (b := (16131511421 / 10000000000000 : ℝ)) (q := (2243329190199 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12768])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12768])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12768]

theorem cert12768_33 : CellCertificate 12768 (176960112697777 / 2000000000000000 : ℝ) (411270205258431 / 250000000000000000 : ℝ) (166128061805781 / 5000000000000000 : ℝ)
    (cell12768 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · have h := gap_lower (n := 12768) (a := (82934465335203 / 100000000000000 : ℝ)) (b := (16131511421 / 10000000000000 : ℝ)) (q := (2243333185543 / 100000000000000 : ℝ))
      (E := (cell12768 ⟨33, by decide⟩).energy) (xi := (166128061805781 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12768 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12768]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12768])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12768) (a := (82934465335203 / 100000000000000 : ℝ)) (b := (16131511421 / 10000000000000 : ℝ)) (q := (2243333185543 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12768])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12768])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12768]

theorem cert12768_34 : CellCertificate 12768 (176960112697777 / 2000000000000000 : ℝ) (411270205258431 / 250000000000000000 : ℝ) (166128061805781 / 5000000000000000 : ℝ)
    (cell12768 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · have h := gap_lower (n := 12768) (a := (41450157796089 / 50000000000000 : ℝ)) (b := (16131511421 / 10000000000000 : ℝ)) (q := (56083430951 / 2500000000000 : ℝ))
      (E := (cell12768 ⟨34, by decide⟩).energy) (xi := (166128061805781 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12768 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12768]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12768])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12768) (a := (41450157796089 / 50000000000000 : ℝ)) (b := (16131511421 / 10000000000000 : ℝ)) (q := (56083430951 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12768])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12768])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12768]

theorem cert12768_35 : CellCertificate 12768 (176960112697777 / 2000000000000000 : ℝ) (411270205258431 / 250000000000000000 : ℝ) (166128061805781 / 5000000000000000 : ℝ)
    (cell12768 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · have h := gap_lower (n := 12768) (a := (3314647585813 / 4000000000000 : ℝ)) (b := (16131511421 / 10000000000000 : ℝ)) (q := (1121670615671 / 50000000000000 : ℝ))
      (E := (cell12768 ⟨35, by decide⟩).energy) (xi := (166128061805781 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12768 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12768]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12768])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12768) (a := (3314647585813 / 4000000000000 : ℝ)) (b := (16131511421 / 10000000000000 : ℝ)) (q := (1121670615671 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12768])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12768])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12768]

theorem cert12768_36 : CellCertificate 12768 (176960112697777 / 2000000000000000 : ℝ) (411270205258431 / 250000000000000000 : ℝ) (166128061805781 / 5000000000000000 : ℝ)
    (cell12768 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · have h := gap_lower (n := 12768) (a := (41416043731967 / 50000000000000 : ℝ)) (b := (16131511421 / 10000000000000 : ℝ)) (q := (1121672612333 / 50000000000000 : ℝ))
      (E := (cell12768 ⟨36, by decide⟩).energy) (xi := (166128061805781 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12768 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12768]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12768])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12768) (a := (41416043731967 / 50000000000000 : ℝ)) (b := (16131511421 / 10000000000000 : ℝ)) (q := (1121672612333 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12768])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12768])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12768]

theorem cert12768_37 : CellCertificate 12768 (176960112697777 / 2000000000000000 : ℝ) (411270205258431 / 250000000000000000 : ℝ) (166128061805781 / 5000000000000000 : ℝ)
    (cell12768 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · have h := gap_lower (n := 12768) (a := (82798009017451 / 100000000000000 : ℝ)) (b := (16131511421 / 10000000000000 : ℝ)) (q := (140209326151 / 6250000000000 : ℝ))
      (E := (cell12768 ⟨37, by decide⟩).energy) (xi := (166128061805781 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12768 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12768]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12768])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12768) (a := (82798009017451 / 100000000000000 : ℝ)) (b := (16131511421 / 10000000000000 : ℝ)) (q := (140209326151 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12768])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12768])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12768]

theorem cert12768_38 : CellCertificate 12768 (176960112697777 / 2000000000000000 : ℝ) (411270205258431 / 250000000000000000 : ℝ) (166128061805781 / 5000000000000000 : ℝ)
    (cell12768 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · have h := gap_lower (n := 12768) (a := (3310558171019 / 4000000000000 : ℝ)) (b := (16131511421 / 10000000000000 : ℝ)) (q := (2243353212773 / 100000000000000 : ℝ))
      (E := (cell12768 ⟨38, by decide⟩).energy) (xi := (166128061805781 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12768 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12768]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12768])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12768) (a := (3310558171019 / 4000000000000 : ℝ)) (b := (16131511421 / 10000000000000 : ℝ)) (q := (2243353212773 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12768])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12768])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12768]

theorem cert12768_39 : CellCertificate 12768 (176960112697777 / 2000000000000000 : ℝ) (411270205258431 / 250000000000000000 : ℝ) (166128061805781 / 5000000000000000 : ℝ)
    (cell12768 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · have h := gap_lower (n := 12768) (a := (82729923207761 / 100000000000000 : ℝ)) (b := (16131511421 / 10000000000000 : ℝ)) (q := (1121678633213 / 50000000000000 : ℝ))
      (E := (cell12768 ⟨39, by decide⟩).energy) (xi := (166128061805781 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12768 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12768]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12768])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12768) (a := (82729923207761 / 100000000000000 : ℝ)) (b := (16131511421 / 10000000000000 : ℝ)) (q := (1121678633213 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12768])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12768])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12768]

theorem cert12769_20 : CellCertificate 12769 (442386456886239 / 5000000000000000 : ℝ) (328990388988847 / 200000000000000000 : ℝ) (332229475620691 / 10000000000000000 : ℝ)
    (cell12769 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · have h := gap_lower (n := 12769) (a := (83380583005877 / 100000000000000 : ℝ)) (b := (161302328549 / 100000000000000 : ℝ)) (q := (44863213169 / 2000000000000 : ℝ))
      (E := (cell12769 ⟨20, by decide⟩).energy) (xi := (332229475620691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12769 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12769]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12769])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12769) (a := (83380583005877 / 100000000000000 : ℝ)) (b := (161302328549 / 100000000000000 : ℝ)) (q := (44863213169 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12769])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12769])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12769]

theorem cert12769_21 : CellCertificate 12769 (442386456886239 / 5000000000000000 : ℝ) (328990388988847 / 200000000000000000 : ℝ) (332229475620691 / 10000000000000000 : ℝ)
    (cell12769 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · have h := gap_lower (n := 12769) (a := (83346121353981 / 100000000000000 : ℝ)) (b := (161302328549 / 100000000000000 : ℝ)) (q := (2243164688629 / 100000000000000 : ℝ))
      (E := (cell12769 ⟨21, by decide⟩).energy) (xi := (332229475620691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12769 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12769]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12769])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12769) (a := (83346121353981 / 100000000000000 : ℝ)) (b := (161302328549 / 100000000000000 : ℝ)) (q := (2243164688629 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12769])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12769])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12769]

theorem cert12769_22 : CellCertificate 12769 (442386456886239 / 5000000000000000 : ℝ) (328990388988847 / 200000000000000000 : ℝ) (332229475620691 / 10000000000000000 : ℝ)
    (cell12769 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · have h := gap_lower (n := 12769) (a := (41655841955837 / 50000000000000 : ℝ)) (b := (161302328549 / 100000000000000 : ℝ)) (q := (2243168689871 / 100000000000000 : ℝ))
      (E := (cell12769 ⟨22, by decide⟩).energy) (xi := (332229475620691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12769 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12769]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12769])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12769) (a := (41655841955837 / 50000000000000 : ℝ)) (b := (161302328549 / 100000000000000 : ℝ)) (q := (2243168689871 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12769])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12769])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12769]

theorem cert12769_23 : CellCertificate 12769 (442386456886239 / 5000000000000000 : ℝ) (328990388988847 / 200000000000000000 : ℝ) (332229475620691 / 10000000000000000 : ℝ)
    (cell12769 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · have h := gap_lower (n := 12769) (a := (20819317661533 / 25000000000000 : ℝ)) (b := (161302328549 / 100000000000000 : ℝ)) (q := (2243172665799 / 100000000000000 : ℝ))
      (E := (cell12769 ⟨23, by decide⟩).energy) (xi := (332229475620691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12769 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12769]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12769])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12769) (a := (20819317661533 / 25000000000000 : ℝ)) (b := (161302328549 / 100000000000000 : ℝ)) (q := (2243172665799 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12769])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12769])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12769]

theorem cert12769_24 : CellCertificate 12769 (442386456886239 / 5000000000000000 : ℝ) (328990388988847 / 200000000000000000 : ℝ) (332229475620691 / 10000000000000000 : ℝ)
    (cell12769 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · have h := gap_lower (n := 12769) (a := (83242881524703 / 100000000000000 : ℝ)) (b := (161302328549 / 100000000000000 : ℝ)) (q := (2243176678173 / 100000000000000 : ℝ))
      (E := (cell12769 ⟨24, by decide⟩).energy) (xi := (332229475620691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12769 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12769]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12769])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12769) (a := (83242881524703 / 100000000000000 : ℝ)) (b := (161302328549 / 100000000000000 : ℝ)) (q := (2243176678173 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12769])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12769])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12769]

theorem cert12769_25 : CellCertificate 12769 (442386456886239 / 5000000000000000 : ℝ) (328990388988847 / 200000000000000000 : ℝ) (332229475620691 / 10000000000000000 : ℝ)
    (cell12769 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · have h := gap_lower (n := 12769) (a := (83208516514899 / 100000000000000 : ℝ)) (b := (161302328549 / 100000000000000 : ℝ)) (q := (560795167953 / 25000000000000 : ℝ))
      (E := (cell12769 ⟨25, by decide⟩).energy) (xi := (332229475620691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12769 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12769]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12769])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12769) (a := (83208516514899 / 100000000000000 : ℝ)) (b := (161302328549 / 100000000000000 : ℝ)) (q := (560795167953 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12769])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12769])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12769]

theorem cert12769_26 : CellCertificate 12769 (442386456886239 / 5000000000000000 : ℝ) (328990388988847 / 200000000000000000 : ℝ) (332229475620691 / 10000000000000000 : ℝ)
    (cell12769 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · have h := gap_lower (n := 12769) (a := (207935438961 / 250000000000 : ℝ)) (b := (161302328549 / 100000000000000 : ℝ)) (q := (2243184708057 / 100000000000000 : ℝ))
      (E := (cell12769 ⟨26, by decide⟩).energy) (xi := (332229475620691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12769 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12769]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12769])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12769) (a := (207935438961 / 250000000000 : ℝ)) (b := (161302328549 / 100000000000000 : ℝ)) (q := (2243184708057 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12769])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12769])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12769]

theorem cert12769_27 : CellCertificate 12769 (442386456886239 / 5000000000000000 : ℝ) (328990388988847 / 200000000000000000 : ℝ) (332229475620691 / 10000000000000000 : ℝ)
    (cell12769 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · have h := gap_lower (n := 12769) (a := (20784964675263 / 25000000000000 : ℝ)) (b := (161302328549 / 100000000000000 : ℝ)) (q := (224318873121 / 10000000000000 : ℝ))
      (E := (cell12769 ⟨27, by decide⟩).energy) (xi := (332229475620691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12769 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12769]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12769])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12769) (a := (20784964675263 / 25000000000000 : ℝ)) (b := (161302328549 / 100000000000000 : ℝ)) (q := (224318873121 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12769])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12769])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12769]

theorem cert12769_28 : CellCertificate 12769 (442386456886239 / 5000000000000000 : ℝ) (328990388988847 / 200000000000000000 : ℝ) (332229475620691 / 10000000000000000 : ℝ)
    (cell12769 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · have h := gap_lower (n := 12769) (a := (2597048932277 / 3125000000000 : ℝ)) (b := (161302328549 / 100000000000000 : ℝ)) (q := (2243192685249 / 100000000000000 : ℝ))
      (E := (cell12769 ⟨28, by decide⟩).energy) (xi := (332229475620691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12769 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12769]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12769])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12769) (a := (2597048932277 / 3125000000000 : ℝ)) (b := (161302328549 / 100000000000000 : ℝ)) (q := (2243192685249 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12769])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12769])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12769]

theorem cert12769_29 : CellCertificate 12769 (442386456886239 / 5000000000000000 : ℝ) (328990388988847 / 200000000000000000 : ℝ) (332229475620691 / 10000000000000000 : ℝ)
    (cell12769 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · have h := gap_lower (n := 12769) (a := (83071296948011 / 100000000000000 : ℝ)) (b := (161302328549 / 100000000000000 : ℝ)) (q := (448639337863 / 20000000000000 : ℝ))
      (E := (cell12769 ⟨29, by decide⟩).energy) (xi := (332229475620691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12769 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12769]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12769])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12769) (a := (83071296948011 / 100000000000000 : ℝ)) (b := (161302328549 / 100000000000000 : ℝ)) (q := (448639337863 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12769])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12769])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12769]

theorem cert12769_30 : CellCertificate 12769 (442386456886239 / 5000000000000000 : ℝ) (328990388988847 / 200000000000000000 : ℝ) (332229475620691 / 10000000000000000 : ℝ)
    (cell12769 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · have h := gap_lower (n := 12769) (a := (20759263003707 / 25000000000000 : ℝ)) (b := (161302328549 / 100000000000000 : ℝ)) (q := (2243200745467 / 100000000000000 : ℝ))
      (E := (cell12769 ⟨30, by decide⟩).energy) (xi := (332229475620691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12769 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12769]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12769])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12769) (a := (20759263003707 / 25000000000000 : ℝ)) (b := (161302328549 / 100000000000000 : ℝ)) (q := (2243200745467 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12769])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12769])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12769]

theorem cert12769_31 : CellCertificate 12769 (442386456886239 / 5000000000000000 : ℝ) (328990388988847 / 200000000000000000 : ℝ) (332229475620691 / 10000000000000000 : ℝ)
    (cell12769 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · have h := gap_lower (n := 12769) (a := (83002831001813 / 100000000000000 : ℝ)) (b := (161302328549 / 100000000000000 : ℝ)) (q := (2243204738447 / 100000000000000 : ℝ))
      (E := (cell12769 ⟨31, by decide⟩).energy) (xi := (332229475620691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12769 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12769]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12769])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12769) (a := (83002831001813 / 100000000000000 : ℝ)) (b := (161302328549 / 100000000000000 : ℝ)) (q := (2243204738447 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12769])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12769])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12769]

theorem cert12769_32 : CellCertificate 12769 (442386456886239 / 5000000000000000 : ℝ) (328990388988847 / 200000000000000000 : ℝ) (332229475620691 / 10000000000000000 : ℝ)
    (cell12769 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · have h := gap_lower (n := 12769) (a := (10371079234703 / 12500000000000 : ℝ)) (b := (161302328549 / 100000000000000 : ℝ)) (q := (448641745657 / 20000000000000 : ℝ))
      (E := (cell12769 ⟨32, by decide⟩).energy) (xi := (332229475620691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12769 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12769]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12769])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12769) (a := (10371079234703 / 12500000000000 : ℝ)) (b := (161302328549 / 100000000000000 : ℝ)) (q := (448641745657 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12769])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12769])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12769]

theorem cert12769_33 : CellCertificate 12769 (442386456886239 / 5000000000000000 : ℝ) (328990388988847 / 200000000000000000 : ℝ) (332229475620691 / 10000000000000000 : ℝ)
    (cell12769 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · have h := gap_lower (n := 12769) (a := (41467230305539 / 50000000000000 : ℝ)) (b := (161302328549 / 100000000000000 : ℝ)) (q := (2243212716283 / 100000000000000 : ℝ))
      (E := (cell12769 ⟨33, by decide⟩).energy) (xi := (332229475620691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12769 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12769]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12769])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12769) (a := (41467230305539 / 50000000000000 : ℝ)) (b := (161302328549 / 100000000000000 : ℝ)) (q := (2243212716283 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12769])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12769])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12769]

theorem cert12769_34 : CellCertificate 12769 (442386456886239 / 5000000000000000 : ℝ) (328990388988847 / 200000000000000000 : ℝ) (332229475620691 / 10000000000000000 : ℝ)
    (cell12769 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · have h := gap_lower (n := 12769) (a := (5181269448197 / 6250000000000 : ℝ)) (b := (161302328549 / 100000000000000 : ℝ)) (q := (2243216762131 / 100000000000000 : ℝ))
      (E := (cell12769 ⟨34, by decide⟩).energy) (xi := (332229475620691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12769 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12769]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12769])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12769) (a := (5181269448197 / 6250000000000 : ℝ)) (b := (161302328549 / 100000000000000 : ℝ)) (q := (2243216762131 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12769])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12769])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12769]

theorem cert12769_35 : CellCertificate 12769 (442386456886239 / 5000000000000000 : ℝ) (328990388988847 / 200000000000000000 : ℝ) (332229475620691 / 10000000000000000 : ℝ)
    (cell12769 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · have h := gap_lower (n := 12769) (a := (82866185526979 / 100000000000000 : ℝ)) (b := (161302328549 / 100000000000000 : ℝ)) (q := (1121610374739 / 50000000000000 : ℝ))
      (E := (cell12769 ⟨35, by decide⟩).energy) (xi := (332229475620691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12769 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12769]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12769])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12769) (a := (82866185526979 / 100000000000000 : ℝ)) (b := (161302328549 / 100000000000000 : ℝ)) (q := (1121610374739 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12769])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12769])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12769]

theorem cert12769_36 : CellCertificate 12769 (442386456886239 / 5000000000000000 : ℝ) (328990388988847 / 200000000000000000 : ℝ) (332229475620691 / 10000000000000000 : ℝ)
    (cell12769 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · have h := gap_lower (n := 12769) (a := (1656641672957 / 2000000000000 : ℝ)) (b := (161302328549 / 100000000000000 : ℝ)) (q := (1121612368771 / 50000000000000 : ℝ))
      (E := (cell12769 ⟨36, by decide⟩).energy) (xi := (332229475620691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12769 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12769]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12769])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12769) (a := (1656641672957 / 2000000000000 : ℝ)) (b := (161302328549 / 100000000000000 : ℝ)) (q := (1121612368771 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12769])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12769])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12769]

theorem cert12769_37 : CellCertificate 12769 (442386456886239 / 5000000000000000 : ℝ) (328990388988847 / 200000000000000000 : ℝ) (332229475620691 / 10000000000000000 : ℝ)
    (cell12769 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · have h := gap_lower (n := 12769) (a := (8279800550321 / 10000000000000 : ℝ)) (b := (161302328549 / 100000000000000 : ℝ)) (q := (1121614363363 / 50000000000000 : ℝ))
      (E := (cell12769 ⟨37, by decide⟩).energy) (xi := (332229475620691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12769 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12769]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12769])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12769) (a := (8279800550321 / 10000000000000 : ℝ)) (b := (161302328549 / 100000000000000 : ℝ)) (q := (1121614363363 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12769])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12769])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12769]

theorem cert12769_38 : CellCertificate 12769 (442386456886239 / 5000000000000000 : ℝ) (328990388988847 / 200000000000000000 : ℝ) (332229475620691 / 10000000000000000 : ℝ)
    (cell12769 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · have h := gap_lower (n := 12769) (a := (82763951062661 / 100000000000000 : ℝ)) (b := (161302328549 / 100000000000000 : ℝ)) (q := (560808193979 / 25000000000000 : ℝ))
      (E := (cell12769 ⟨38, by decide⟩).energy) (xi := (332229475620691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12769 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12769]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12769])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12769) (a := (82763951062661 / 100000000000000 : ℝ)) (b := (161302328549 / 100000000000000 : ℝ)) (q := (560808193979 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12769])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12769])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12769]

theorem cert12769_39 : CellCertificate 12769 (442386456886239 / 5000000000000000 : ℝ) (328990388988847 / 200000000000000000 : ℝ) (332229475620691 / 10000000000000000 : ℝ)
    (cell12769 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · have h := gap_lower (n := 12769) (a := (82729920295957 / 100000000000000 : ℝ)) (b := (161302328549 / 100000000000000 : ℝ)) (q := (2243236767681 / 100000000000000 : ℝ))
      (E := (cell12769 ⟨39, by decide⟩).energy) (xi := (332229475620691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12769 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12769]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12769])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12769) (a := (82729920295957 / 100000000000000 : ℝ)) (b := (161302328549 / 100000000000000 : ℝ)) (q := (2243236767681 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12769])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12769])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12769]

theorem cert12770_20 : CellCertificate 12770 (884745268211749 / 10000000000000000 : ℝ) (82241154452277 / 50000000000000000 : ℝ) (332202831957383 / 10000000000000000 : ℝ)
    (cell12770 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · have h := gap_lower (n := 12770) (a := (83380574304519 / 100000000000000 : ℝ)) (b := (5040298279 / 3125000000000 : ℝ)) (q := (2243040218809 / 100000000000000 : ℝ))
      (E := (cell12770 ⟨20, by decide⟩).energy) (xi := (332202831957383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12770 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12770]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12770])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12770) (a := (83380574304519 / 100000000000000 : ℝ)) (b := (5040298279 / 3125000000000 : ℝ)) (q := (2243040218809 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12770])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12770])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12770]

theorem cert12770_21 : CellCertificate 12770 (884745268211749 / 10000000000000000 : ℝ) (82241154452277 / 50000000000000000 : ℝ) (332202831957383 / 10000000000000000 : ℝ)
    (cell12770 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · have h := gap_lower (n := 12770) (a := (83346112961211 / 100000000000000 : ℝ)) (b := (5040298279 / 3125000000000 : ℝ)) (q := (1121522116611 / 50000000000000 : ℝ))
      (E := (cell12770 ⟨21, by decide⟩).energy) (xi := (332202831957383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12770 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12770]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12770])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12770) (a := (83346112961211 / 100000000000000 : ℝ)) (b := (5040298279 / 3125000000000 : ℝ)) (q := (1121522116611 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12770])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12770])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12770]

theorem cert12770_22 : CellCertificate 12770 (884745268211749 / 10000000000000000 : ℝ) (82241154452277 / 50000000000000000 : ℝ) (332202831957383 / 10000000000000000 : ℝ)
    (cell12770 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · have h := gap_lower (n := 12770) (a := (41655837913531 / 50000000000000 : ℝ)) (b := (5040298279 / 3125000000000 : ℝ)) (q := (2243048219403 / 100000000000000 : ℝ))
      (E := (cell12770 ⟨22, by decide⟩).energy) (xi := (332202831957383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12770 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12770]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12770])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12770) (a := (41655837913531 / 50000000000000 : ℝ)) (b := (5040298279 / 3125000000000 : ℝ)) (q := (2243048219403 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12770])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12770])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12770]

theorem cert12770_23 : CellCertificate 12770 (884745268211749 / 10000000000000000 : ℝ) (82241154452277 / 50000000000000000 : ℝ) (332202831957383 / 10000000000000000 : ℝ)
    (cell12770 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · have h := gap_lower (n := 12770) (a := (83277262869249 / 100000000000000 : ℝ)) (b := (5040298279 / 3125000000000 : ℝ)) (q := (224305223933 / 10000000000000 : ℝ))
      (E := (cell12770 ⟨23, by decide⟩).energy) (xi := (332202831957383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12770 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12770]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12770])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12770) (a := (83277262869249 / 100000000000000 : ℝ)) (b := (5040298279 / 3125000000000 : ℝ)) (q := (224305223933 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12770])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12770])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12770]

theorem cert12770_24 : CellCertificate 12770 (884745268211749 / 10000000000000000 : ℝ) (82241154452277 / 50000000000000000 : ℝ) (332202831957383 / 10000000000000000 : ℝ)
    (cell12770 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · have h := gap_lower (n := 12770) (a := (1040535925689 / 1250000000000 : ℝ)) (b := (5040298279 / 3125000000000 : ℝ)) (q := (560764059519 / 25000000000000 : ℝ))
      (E := (cell12770 ⟨24, by decide⟩).energy) (xi := (332202831957383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12770 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12770]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12770])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12770) (a := (1040535925689 / 1250000000000 : ℝ)) (b := (5040298279 / 3125000000000 : ℝ)) (q := (560764059519 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12770])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12770])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12770]

theorem cert12770_25 : CellCertificate 12770 (884745268211749 / 10000000000000000 : ℝ) (82241154452277 / 50000000000000000 : ℝ) (332202831957383 / 10000000000000000 : ℝ)
    (cell12770 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · have h := gap_lower (n := 12770) (a := (83208509352189 / 100000000000000 : ℝ)) (b := (5040298279 / 3125000000000 : ℝ)) (q := (2243060218789 / 100000000000000 : ℝ))
      (E := (cell12770 ⟨25, by decide⟩).energy) (xi := (332202831957383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12770 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12770]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12770])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12770) (a := (83208509352189 / 100000000000000 : ℝ)) (b := (5040298279 / 3125000000000 : ℝ)) (q := (2243060218789 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12770])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12770])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12770]

theorem cert12770_26 : CellCertificate 12770 (884745268211749 / 10000000000000000 : ℝ) (82241154452277 / 50000000000000000 : ℝ) (332202831957383 / 10000000000000000 : ℝ)
    (cell12770 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · have h := gap_lower (n := 12770) (a := (83174168728137 / 100000000000000 : ℝ)) (b := (5040298279 / 3125000000000 : ℝ)) (q := (2243064242809 / 100000000000000 : ℝ))
      (E := (cell12770 ⟨26, by decide⟩).energy) (xi := (332202831957383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12770 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12770]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12770])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12770) (a := (83174168728137 / 100000000000000 : ℝ)) (b := (5040298279 / 3125000000000 : ℝ)) (q := (2243064242809 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12770])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12770])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12770]

theorem cert12770_27 : CellCertificate 12770 (884745268211749 / 10000000000000000 : ℝ) (82241154452277 / 50000000000000000 : ℝ) (332202831957383 / 10000000000000000 : ℝ)
    (cell12770 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · have h := gap_lower (n := 12770) (a := (83139852150809 / 100000000000000 : ℝ)) (b := (5040298279 / 3125000000000 : ℝ)) (q := (56076706361 / 2500000000000 : ℝ))
      (E := (cell12770 ⟨27, by decide⟩).energy) (xi := (332202831957383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12770 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12770]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12770])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12770) (a := (83139852150809 / 100000000000000 : ℝ)) (b := (5040298279 / 3125000000000 : ℝ)) (q := (56076706361 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12770])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12770])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12770]

theorem cert12770_28 : CellCertificate 12770 (884745268211749 / 10000000000000000 : ℝ) (82241154452277 / 50000000000000000 : ℝ) (332202831957383 / 10000000000000000 : ℝ)
    (cell12770 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · have h := gap_lower (n := 12770) (a := (83105559588217 / 100000000000000 : ℝ)) (b := (5040298279 / 3125000000000 : ℝ)) (q := (224307225613 / 10000000000000 : ℝ))
      (E := (cell12770 ⟨28, by decide⟩).energy) (xi := (332202831957383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12770 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12770]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12770])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12770) (a := (83105559588217 / 100000000000000 : ℝ)) (b := (5040298279 / 3125000000000 : ℝ)) (q := (224307225613 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12770])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12770])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12770]

theorem cert12770_29 : CellCertificate 12770 (884745268211749 / 10000000000000000 : ℝ) (82241154452277 / 50000000000000000 : ℝ) (332202831957383 / 10000000000000000 : ℝ)
    (cell12770 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · have h := gap_lower (n := 12770) (a := (10383911376067 / 12500000000000 : ℝ)) (b := (5040298279 / 3125000000000 : ℝ)) (q := (140192265631 / 6250000000000 : ℝ))
      (E := (cell12770 ⟨29, by decide⟩).energy) (xi := (332202831957383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12770 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12770]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12770])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12770) (a := (10383911376067 / 12500000000000 : ℝ)) (b := (5040298279 / 3125000000000 : ℝ)) (q := (140192265631 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12770])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12770])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12770]

theorem cert12770_30 : CellCertificate 12770 (884745268211749 / 10000000000000000 : ℝ) (82241154452277 / 50000000000000000 : ℝ) (332202831957383 / 10000000000000000 : ℝ)
    (cell12770 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · have h := gap_lower (n := 12770) (a := (83037046380101 / 100000000000000 : ℝ)) (b := (5040298279 / 3125000000000 : ℝ)) (q := (280385029791 / 12500000000000 : ℝ))
      (E := (cell12770 ⟨30, by decide⟩).energy) (xi := (332202831957383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12770 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12770]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12770])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12770) (a := (83037046380101 / 100000000000000 : ℝ)) (b := (5040298279 / 3125000000000 : ℝ)) (q := (280385029791 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12770])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12770])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12770]

theorem cert12770_31 : CellCertificate 12770 (884745268211749 / 10000000000000000 : ℝ) (82241154452277 / 50000000000000000 : ℝ) (332202831957383 / 10000000000000000 : ℝ)
    (cell12770 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · have h := gap_lower (n := 12770) (a := (83002825671411 / 100000000000000 : ℝ)) (b := (5040298279 / 3125000000000 : ℝ)) (q := (2243084281127 / 100000000000000 : ℝ))
      (E := (cell12770 ⟨31, by decide⟩).energy) (xi := (332202831957383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12770 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12770]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12770])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12770) (a := (83002825671411 / 100000000000000 : ℝ)) (b := (5040298279 / 3125000000000 : ℝ)) (q := (2243084281127 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12770])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12770])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12770]

theorem cert12770_32 : CellCertificate 12770 (884745268211749 / 10000000000000000 : ℝ) (82241154452277 / 50000000000000000 : ℝ) (332202831957383 / 10000000000000000 : ℝ)
    (cell12770 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · have h := gap_lower (n := 12770) (a := (41484314425563 / 50000000000000 : ℝ)) (b := (5040298279 / 3125000000000 : ℝ)) (q := (2243088262959 / 100000000000000 : ℝ))
      (E := (cell12770 ⟨32, by decide⟩).energy) (xi := (332202831957383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12770 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12770]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12770])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12770) (a := (41484314425563 / 50000000000000 : ℝ)) (b := (5040298279 / 3125000000000 : ℝ)) (q := (2243088262959 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12770])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12770])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12770]

theorem cert12770_33 : CellCertificate 12770 (884745268211749 / 10000000000000000 : ℝ) (82241154452277 / 50000000000000000 : ℝ) (332202831957383 / 10000000000000000 : ℝ)
    (cell12770 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · have h := gap_lower (n := 12770) (a := (82934455888063 / 100000000000000 : ℝ)) (b := (5040298279 / 3125000000000 : ℝ)) (q := (2243092302239 / 100000000000000 : ℝ))
      (E := (cell12770 ⟨33, by decide⟩).energy) (xi := (332202831957383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12770 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12770]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12770])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12770) (a := (82934455888063 / 100000000000000 : ℝ)) (b := (5040298279 / 3125000000000 : ℝ)) (q := (2243092302239 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12770])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12770])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12770]

theorem cert12770_34 : CellCertificate 12770 (884745268211749 / 10000000000000000 : ℝ) (82241154452277 / 50000000000000000 : ℝ) (332202831957383 / 10000000000000000 : ℝ)
    (cell12770 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · have h := gap_lower (n := 12770) (a := (103625383439 / 125000000000 : ℝ)) (b := (5040298279 / 3125000000000 : ℝ)) (q := (448619256577 / 20000000000000 : ℝ))
      (E := (cell12770 ⟨34, by decide⟩).energy) (xi := (332202831957383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12770 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12770]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12770])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12770) (a := (103625383439 / 125000000000 : ℝ)) (b := (5040298279 / 3125000000000 : ℝ)) (q := (448619256577 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12770])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12770])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12770]

theorem cert12770_35 : CellCertificate 12770 (884745268211749 / 10000000000000000 : ℝ) (82241154452277 / 50000000000000000 : ℝ) (332202831957383 / 10000000000000000 : ℝ)
    (cell12770 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · have h := gap_lower (n := 12770) (a := (8286618140967 / 10000000000000 : ℝ)) (b := (5040298279 / 3125000000000 : ℝ)) (q := (560775066079 / 25000000000000 : ℝ))
      (E := (cell12770 ⟨35, by decide⟩).energy) (xi := (332202831957383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12770 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12770]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12770])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12770) (a := (8286618140967 / 10000000000000 : ℝ)) (b := (5040298279 / 3125000000000 : ℝ)) (q := (560775066079 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12770])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12770])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12770]

theorem cert12770_36 : CellCertificate 12770 (884745268211749 / 10000000000000000 : ℝ) (82241154452277 / 50000000000000000 : ℝ) (332202831957383 / 10000000000000000 : ℝ)
    (cell12770 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · have h := gap_lower (n := 12770) (a := (41416039916383 / 50000000000000 : ℝ)) (b := (5040298279 / 3125000000000 : ℝ)) (q := (2243104305817 / 100000000000000 : ℝ))
      (E := (cell12770 ⟨36, by decide⟩).energy) (xi := (332202831957383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12770 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12770]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12770])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12770) (a := (41416039916383 / 50000000000000 : ℝ)) (b := (5040298279 / 3125000000000 : ℝ)) (q := (2243104305817 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12770])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12770])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12770]

theorem cert12770_37 : CellCertificate 12770 (884745268211749 / 10000000000000000 : ℝ) (82241154452277 / 50000000000000000 : ℝ) (332202831957383 / 10000000000000000 : ℝ)
    (cell12770 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · have h := gap_lower (n := 12770) (a := (82798001989933 / 100000000000000 : ℝ)) (b := (5040298279 / 3125000000000 : ℝ)) (q := (35048567039 / 1562500000000 : ℝ))
      (E := (cell12770 ⟨37, by decide⟩).energy) (xi := (332202831957383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12770 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12770]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12770])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12770) (a := (82798001989933 / 100000000000000 : ℝ)) (b := (5040298279 / 3125000000000 : ℝ)) (q := (35048567039 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12770])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12770])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12770]

theorem cert12770_38 : CellCertificate 12770 (884745268211749 / 10000000000000000 : ℝ) (82241154452277 / 50000000000000000 : ℝ) (332202831957383 / 10000000000000000 : ℝ)
    (cell12770 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · have h := gap_lower (n := 12770) (a := (41381973925387 / 50000000000000 : ℝ)) (b := (5040298279 / 3125000000000 : ℝ)) (q := (1121556138583 / 50000000000000 : ℝ))
      (E := (cell12770 ⟨38, by decide⟩).energy) (xi := (332202831957383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12770 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12770]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12770])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12770) (a := (41381973925387 / 50000000000000 : ℝ)) (b := (5040298279 / 3125000000000 : ℝ)) (q := (1121556138583 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12770])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12770])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12770]

theorem cert12770_39 : CellCertificate 12770 (884745268211749 / 10000000000000000 : ℝ) (82241154452277 / 50000000000000000 : ℝ) (332202831957383 / 10000000000000000 : ℝ)
    (cell12770 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · have h := gap_lower (n := 12770) (a := (16545983477009 / 20000000000000 : ℝ)) (b := (5040298279 / 3125000000000 : ℝ)) (q := (2243116324517 / 100000000000000 : ℝ))
      (E := (cell12770 ⟨39, by decide⟩).energy) (xi := (332202831957383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12770 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12770]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12770])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12770) (a := (16545983477009 / 20000000000000 : ℝ)) (b := (5040298279 / 3125000000000 : ℝ)) (q := (2243116324517 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12770])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12770])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12770]

theorem cert12771_20 : CellCertificate 12771 (221179406701429 / 2500000000000000 : ℝ) (328938850666579 / 200000000000000000 : ℝ) (664352385241 / 20000000000000 : ℝ)
    (cell12771 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · have h := gap_lower (n := 12771) (a := (333522262419 / 400000000000 : ℝ)) (b := (80638381673 / 50000000000000 : ℝ)) (q := (2242919833591 / 100000000000000 : ℝ))
      (E := (cell12771 ⟨20, by decide⟩).energy) (xi := (664352385241 / 20000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12771 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12771]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12771])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12771) (a := (333522262419 / 400000000000 : ℝ)) (b := (80638381673 / 50000000000000 : ℝ)) (q := (2242919833591 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12771])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12771])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12771]

theorem cert12771_21 : CellCertificate 12771 (221179406701429 / 2500000000000000 : ℝ) (328938850666579 / 200000000000000000 : ℝ) (664352385241 / 20000000000000 : ℝ)
    (cell12771 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · have h := gap_lower (n := 12771) (a := (83346104569993 / 100000000000000 : ℝ)) (b := (80638381673 / 50000000000000 : ℝ)) (q := (1121461916149 / 50000000000000 : ℝ))
      (E := (cell12771 ⟨21, by decide⟩).energy) (xi := (664352385241 / 20000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12771 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12771]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12771])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12771) (a := (83346104569993 / 100000000000000 : ℝ)) (b := (80638381673 / 50000000000000 : ℝ)) (q := (1121461916149 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12771])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12771])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12771]

theorem cert12771_22 : CellCertificate 12771 (221179406701429 / 2500000000000000 : ℝ) (328938850666579 / 200000000000000000 : ℝ) (664352385241 / 20000000000000 : ℝ)
    (cell12771 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · have h := gap_lower (n := 12771) (a := (16662333548793 / 20000000000000 : ℝ)) (b := (80638381673 / 50000000000000 : ℝ)) (q := (2242927803481 / 100000000000000 : ℝ))
      (E := (cell12771 ⟨22, by decide⟩).energy) (xi := (664352385241 / 20000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12771 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12771]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12771])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12771) (a := (16662333548793 / 20000000000000 : ℝ)) (b := (80638381673 / 50000000000000 : ℝ)) (q := (2242927803481 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12771])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12771])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12771]

theorem cert12771_23 : CellCertificate 12771 (221179406701429 / 2500000000000000 : ℝ) (328938850666579 / 200000000000000000 : ℝ) (664352385241 / 20000000000000 : ℝ)
    (cell12771 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · have h := gap_lower (n := 12771) (a := (20819313773461 / 25000000000000 : ℝ)) (b := (80638381673 / 50000000000000 : ℝ)) (q := (280366476139 / 12500000000000 : ℝ))
      (E := (cell12771 ⟨23, by decide⟩).energy) (xi := (664352385241 / 20000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12771 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12771]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12771])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12771) (a := (20819313773461 / 25000000000000 : ℝ)) (b := (80638381673 / 50000000000000 : ℝ)) (q := (280366476139 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12771])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12771])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12771]

theorem cert12771_24 : CellCertificate 12771 (221179406701429 / 2500000000000000 : ℝ) (328938850666579 / 200000000000000000 : ℝ) (664352385241 / 20000000000000 : ℝ)
    (cell12771 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · have h := gap_lower (n := 12771) (a := (41621433293489 / 50000000000000 : ℝ)) (b := (80638381673 / 50000000000000 : ℝ)) (q := (2242935852647 / 100000000000000 : ℝ))
      (E := (cell12771 ⟨24, by decide⟩).energy) (xi := (664352385241 / 20000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12771 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12771]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12771])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12771) (a := (41621433293489 / 50000000000000 : ℝ)) (b := (80638381673 / 50000000000000 : ℝ)) (q := (2242935852647 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12771])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12771])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12771]

theorem cert12771_25 : CellCertificate 12771 (221179406701429 / 2500000000000000 : ℝ) (328938850666579 / 200000000000000000 : ℝ) (664352385241 / 20000000000000 : ℝ)
    (cell12771 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · have h := gap_lower (n := 12771) (a := (83208502190883 / 100000000000000 : ℝ)) (b := (80638381673 / 50000000000000 : ℝ)) (q := (448587964099 / 20000000000000 : ℝ))
      (E := (cell12771 ⟨25, by decide⟩).energy) (xi := (664352385241 / 20000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12771 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12771]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12771])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12771) (a := (83208502190883 / 100000000000000 : ℝ)) (b := (80638381673 / 50000000000000 : ℝ)) (q := (448587964099 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12771])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12771])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12771]

theorem cert12771_26 : CellCertificate 12771 (221179406701429 / 2500000000000000 : ℝ) (328938850666579 / 200000000000000000 : ℝ) (664352385241 / 20000000000000 : ℝ)
    (cell12771 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · have h := gap_lower (n := 12771) (a := (2079354046831 / 2500000000000 : ℝ)) (b := (80638381673 / 50000000000000 : ℝ)) (q := (70091994761 / 3125000000000 : ℝ))
      (E := (cell12771 ⟨26, by decide⟩).energy) (xi := (664352385241 / 20000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12771 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12771]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12771])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12771) (a := (2079354046831 / 2500000000000 : ℝ)) (b := (80638381673 / 50000000000000 : ℝ)) (q := (70091994761 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12771])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12771])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12771]

theorem cert12771_27 : CellCertificate 12771 (221179406701429 / 2500000000000000 : ℝ) (328938850666579 / 200000000000000000 : ℝ) (664352385241 / 20000000000000 : ℝ)
    (cell12771 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · have h := gap_lower (n := 12771) (a := (10392480700237 / 12500000000000 : ℝ)) (b := (80638381673 / 50000000000000 : ℝ)) (q := (1121473916261 / 50000000000000 : ℝ))
      (E := (cell12771 ⟨27, by decide⟩).energy) (xi := (664352385241 / 20000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12771 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12771]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12771])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12771) (a := (10392480700237 / 12500000000000 : ℝ)) (b := (80638381673 / 50000000000000 : ℝ)) (q := (1121473916261 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12771])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12771])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12771]

theorem cert12771_28 : CellCertificate 12771 (221179406701429 / 2500000000000000 : ℝ) (328938850666579 / 200000000000000000 : ℝ) (664352385241 / 20000000000000 : ℝ)
    (cell12771 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · have h := gap_lower (n := 12771) (a := (83105553344863 / 100000000000000 : ℝ)) (b := (80638381673 / 50000000000000 : ℝ)) (q := (44859036469 / 2000000000000 : ℝ))
      (E := (cell12771 ⟨28, by decide⟩).energy) (xi := (664352385241 / 20000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12771 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12771]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12771])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12771) (a := (83105553344863 / 100000000000000 : ℝ)) (b := (80638381673 / 50000000000000 : ℝ)) (q := (44859036469 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12771])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12771])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12771]

theorem cert12771_29 : CellCertificate 12771 (221179406701429 / 2500000000000000 : ℝ) (328938850666579 / 200000000000000000 : ℝ) (664352385241 / 20000000000000 : ℝ)
    (cell12771 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · have h := gap_lower (n := 12771) (a := (20767821267579 / 25000000000000 : ℝ)) (b := (80638381673 / 50000000000000 : ℝ)) (q := (560738966463 / 25000000000000 : ℝ))
      (E := (cell12771 ⟨29, by decide⟩).energy) (xi := (664352385241 / 20000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12771 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12771]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12771])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12771) (a := (20767821267579 / 25000000000000 : ℝ)) (b := (80638381673 / 50000000000000 : ℝ)) (q := (560738966463 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12771])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12771])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12771]

theorem cert12771_30 : CellCertificate 12771 (221179406701429 / 2500000000000000 : ℝ) (328938850666579 / 200000000000000000 : ℝ) (664352385241 / 20000000000000 : ℝ)
    (cell12771 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · have h := gap_lower (n := 12771) (a := (2594907523331 / 3125000000000 : ℝ)) (b := (80638381673 / 50000000000000 : ℝ)) (q := (448591968949 / 20000000000000 : ℝ))
      (E := (cell12771 ⟨30, by decide⟩).energy) (xi := (664352385241 / 20000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12771 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12771]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12771])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12771) (a := (2594907523331 / 3125000000000 : ℝ)) (b := (80638381673 / 50000000000000 : ℝ)) (q := (448591968949 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12771])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12771])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12771]

theorem cert12771_31 : CellCertificate 12771 (221179406701429 / 2500000000000000 : ℝ) (328938850666579 / 200000000000000000 : ℝ) (664352385241 / 20000000000000 : ℝ)
    (cell12771 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · have h := gap_lower (n := 12771) (a := (5187676271387 / 6250000000000 : ℝ)) (b := (80638381673 / 50000000000000 : ℝ)) (q := (2242963820359 / 100000000000000 : ℝ))
      (E := (cell12771 ⟨31, by decide⟩).energy) (xi := (664352385241 / 20000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12771 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12771]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12771])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12771) (a := (5187676271387 / 6250000000000 : ℝ)) (b := (80638381673 / 50000000000000 : ℝ)) (q := (2242963820359 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12771])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12771])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12771]

theorem cert12771_32 : CellCertificate 12771 (221179406701429 / 2500000000000000 : ℝ) (328938850666579 / 200000000000000000 : ℝ) (664352385241 / 20000000000000 : ℝ)
    (cell12771 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · have h := gap_lower (n := 12771) (a := (41484311912887 / 50000000000000 : ℝ)) (b := (80638381673 / 50000000000000 : ℝ)) (q := (2242967852791 / 100000000000000 : ℝ))
      (E := (cell12771 ⟨32, by decide⟩).energy) (xi := (664352385241 / 20000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12771 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12771]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12771])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12771) (a := (41484311912887 / 50000000000000 : ℝ)) (b := (80638381673 / 50000000000000 : ℝ)) (q := (2242967852791 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12771])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12771])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12771]

theorem cert12771_33 : CellCertificate 12771 (221179406701429 / 2500000000000000 : ℝ) (328938850666579 / 200000000000000000 : ℝ) (664352385241 / 20000000000000 : ℝ)
    (cell12771 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · have h := gap_lower (n := 12771) (a := (82934451166157 / 100000000000000 : ℝ)) (b := (80638381673 / 50000000000000 : ℝ)) (q := (89718875393 / 4000000000000 : ℝ))
      (E := (cell12771 ⟨33, by decide⟩).energy) (xi := (664352385241 / 20000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12771 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12771]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12771])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12771) (a := (82934451166157 / 100000000000000 : ℝ)) (b := (80638381673 / 50000000000000 : ℝ)) (q := (89718875393 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12771])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12771])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12771]

theorem cert12771_34 : CellCertificate 12771 (221179406701429 / 2500000000000000 : ℝ) (328938850666579 / 200000000000000000 : ℝ) (664352385241 / 20000000000000 : ℝ)
    (cell12771 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · have h := gap_lower (n := 12771) (a := (518126889577 / 625000000000 : ℝ)) (b := (80638381673 / 50000000000000 : ℝ)) (q := (56074396473 / 2500000000000 : ℝ))
      (E := (cell12771 ⟨34, by decide⟩).energy) (xi := (664352385241 / 20000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12771 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12771]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12771])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12771) (a := (518126889577 / 625000000000 : ℝ)) (b := (80638381673 / 50000000000000 : ℝ)) (q := (56074396473 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12771])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12771])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12771]

theorem cert12771_35 : CellCertificate 12771 (221179406701429 / 2500000000000000 : ℝ) (328938850666579 / 200000000000000000 : ℝ) (664352385241 / 20000000000000 : ℝ)
    (cell12771 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · have h := gap_lower (n := 12771) (a := (82866177293397 / 100000000000000 : ℝ)) (b := (80638381673 / 50000000000000 : ℝ)) (q := (560744973283 / 25000000000000 : ℝ))
      (E := (cell12771 ⟨35, by decide⟩).energy) (xi := (664352385241 / 20000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12771 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12771]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12771])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12771) (a := (82866177293397 / 100000000000000 : ℝ)) (b := (80638381673 / 50000000000000 : ℝ)) (q := (560744973283 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12771])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12771])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12771]

theorem cert12771_36 : CellCertificate 12771 (221179406701429 / 2500000000000000 : ℝ) (328938850666579 / 200000000000000000 : ℝ) (664352385241 / 20000000000000 : ℝ)
    (cell12771 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · have h := gap_lower (n := 12771) (a := (41416038009341 / 50000000000000 : ℝ)) (b := (80638381673 / 50000000000000 : ℝ)) (q := (2242983870833 / 100000000000000 : ℝ))
      (E := (cell12771 ⟨36, by decide⟩).energy) (xi := (664352385241 / 20000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12771 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12771]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12771])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12771) (a := (41416038009341 / 50000000000000 : ℝ)) (b := (80638381673 / 50000000000000 : ℝ)) (q := (2242983870833 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12771])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12771])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12771]

theorem cert12771_37 : CellCertificate 12771 (221179406701429 / 2500000000000000 : ℝ) (328938850666579 / 200000000000000000 : ℝ) (664352385241 / 20000000000000 : ℝ)
    (cell12771 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · have h := gap_lower (n := 12771) (a := (4139899923881 / 5000000000000 : ℝ)) (b := (80638381673 / 50000000000000 : ℝ)) (q := (2242987851043 / 100000000000000 : ℝ))
      (E := (cell12771 ⟨37, by decide⟩).energy) (xi := (664352385241 / 20000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12771 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12771]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12771])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12771) (a := (4139899923881 / 5000000000000 : ℝ)) (b := (80638381673 / 50000000000000 : ℝ)) (q := (2242987851043 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12771])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12771])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12771]

theorem cert12771_38 : CellCertificate 12771 (221179406701429 / 2500000000000000 : ℝ) (328938850666579 / 200000000000000000 : ℝ) (664352385241 / 20000000000000 : ℝ)
    (cell12771 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · have h := gap_lower (n := 12771) (a := (16552788927963 / 20000000000000 : ℝ)) (b := (80638381673 / 50000000000000 : ℝ)) (q := (448598378529 / 20000000000000 : ℝ))
      (E := (cell12771 ⟨38, by decide⟩).energy) (xi := (664352385241 / 20000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12771 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12771]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12771])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12771) (a := (16552788927963 / 20000000000000 : ℝ)) (b := (80638381673 / 50000000000000 : ℝ)) (q := (448598378529 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12771])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12771])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12771]

theorem cert12771_39 : CellCertificate 12771 (221179406701429 / 2500000000000000 : ℝ) (328938850666579 / 200000000000000000 : ℝ) (664352385241 / 20000000000000 : ℝ)
    (cell12771 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · have h := gap_lower (n := 12771) (a := (82729914475023 / 100000000000000 : ℝ)) (b := (80638381673 / 50000000000000 : ℝ)) (q := (448599175641 / 20000000000000 : ℝ))
      (E := (cell12771 ⟨39, by decide⟩).energy) (xi := (664352385241 / 20000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12771 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12771]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12771])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12771) (a := (82729914475023 / 100000000000000 : ℝ)) (b := (80638381673 / 50000000000000 : ℝ)) (q := (448599175641 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12771])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12771])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12771]

theorem cert12772_20 : CellCertificate 12772 (884689989553397 / 10000000000000000 : ℝ) (328913087560311 / 200000000000000000 : ℝ) (332149557608903 / 10000000000000000 : ℝ)
    (cell12772 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · have h := gap_lower (n := 12772) (a := (83380556906571 / 100000000000000 : ℝ)) (b := (161263983803 / 100000000000000 : ℝ)) (q := (560699861127 / 25000000000000 : ℝ))
      (E := (cell12772 ⟨20, by decide⟩).energy) (xi := (332149557608903 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12772 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12772]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12772])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12772) (a := (83380556906571 / 100000000000000 : ℝ)) (b := (161263983803 / 100000000000000 : ℝ)) (q := (560699861127 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12772])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12772])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12772]

theorem cert12772_21 : CellCertificate 12772 (884689989553397 / 10000000000000000 : ℝ) (328913087560311 / 200000000000000000 : ℝ) (332149557608903 / 10000000000000000 : ℝ)
    (cell12772 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · have h := gap_lower (n := 12772) (a := (83346096180327 / 100000000000000 : ℝ)) (b := (161263983803 / 100000000000000 : ℝ)) (q := (44856068551 / 2000000000000 : ℝ))
      (E := (cell12772 ⟨21, by decide⟩).energy) (xi := (332149557608903 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12772 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12772]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12772])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12772) (a := (83346096180327 / 100000000000000 : ℝ)) (b := (161263983803 / 100000000000000 : ℝ)) (q := (44856068551 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12772])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12772])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12772]

theorem cert12772_22 : CellCertificate 12772 (884689989553397 / 10000000000000000 : ℝ) (328913087560311 / 200000000000000000 : ℝ) (332149557608903 / 10000000000000000 : ℝ)
    (cell12772 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · have h := gap_lower (n := 12772) (a := (41655829831191 / 50000000000000 : ℝ)) (b := (161263983803 / 100000000000000 : ℝ)) (q := (280350930263 / 12500000000000 : ℝ))
      (E := (cell12772 ⟨22, by decide⟩).energy) (xi := (332149557608903 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12772 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12772]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12772])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12772) (a := (41655829831191 / 50000000000000 : ℝ)) (b := (161263983803 / 100000000000000 : ℝ)) (q := (280350930263 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12772])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12772])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12772]

theorem cert12772_23 : CellCertificate 12772 (884689989553397 / 10000000000000000 : ℝ) (328913087560311 / 200000000000000000 : ℝ) (332149557608903 / 10000000000000000 : ℝ)
    (cell12772 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · have h := gap_lower (n := 12772) (a := (20819311829979 / 25000000000000 : ℝ)) (b := (161263983803 / 100000000000000 : ℝ)) (q := (2242811433503 / 100000000000000 : ℝ))
      (E := (cell12772 ⟨23, by decide⟩).energy) (xi := (332149557608903 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12772 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12772]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12772])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12772) (a := (20819311829979 / 25000000000000 : ℝ)) (b := (161263983803 / 100000000000000 : ℝ)) (q := (2242811433503 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12772])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12772])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12772]

theorem cert12772_24 : CellCertificate 12772 (884689989553397 / 10000000000000000 : ℝ) (328913087560311 / 200000000000000000 : ℝ) (332149557608903 / 10000000000000000 : ℝ)
    (cell12772 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · have h := gap_lower (n := 12772) (a := (83242859120277 / 100000000000000 : ℝ)) (b := (161263983803 / 100000000000000 : ℝ)) (q := (1121407731753 / 50000000000000 : ℝ))
      (E := (cell12772 ⟨24, by decide⟩).energy) (xi := (332149557608903 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12772 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12772]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12772])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12772) (a := (83242859120277 / 100000000000000 : ℝ)) (b := (161263983803 / 100000000000000 : ℝ)) (q := (1121407731753 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12772])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12772])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12772]

theorem cert12772_25 : CellCertificate 12772 (884689989553397 / 10000000000000000 : ℝ) (328913087560311 / 200000000000000000 : ℝ) (332149557608903 / 10000000000000000 : ℝ)
    (cell12772 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · have h := gap_lower (n := 12772) (a := (83208495030981 / 100000000000000 : ℝ)) (b := (161263983803 / 100000000000000 : ℝ)) (q := (70088106829 / 3125000000000 : ℝ))
      (E := (cell12772 ⟨25, by decide⟩).energy) (xi := (332149557608903 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12772 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12772]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12772])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12772) (a := (83208495030981 / 100000000000000 : ℝ)) (b := (161263983803 / 100000000000000 : ℝ)) (q := (70088106829 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12772])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12772])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12772]

theorem cert12772_26 : CellCertificate 12772 (884689989553397 / 10000000000000000 : ℝ) (328913087560311 / 200000000000000000 : ℝ) (332149557608903 / 10000000000000000 : ℝ)
    (cell12772 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · have h := gap_lower (n := 12772) (a := (8317415501971 / 10000000000000 : ℝ)) (b := (161263983803 / 100000000000000 : ℝ)) (q := (2242823418261 / 100000000000000 : ℝ))
      (E := (cell12772 ⟨26, by decide⟩).energy) (xi := (332149557608903 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12772 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12772]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12772])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12772) (a := (8317415501971 / 10000000000000 : ℝ)) (b := (161263983803 / 100000000000000 : ℝ)) (q := (2242823418261 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12772])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12772])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12772]

theorem cert12772_27 : CellCertificate 12772 (884689989553397 / 10000000000000000 : ℝ) (328913087560311 / 200000000000000000 : ℝ) (332149557608903 / 10000000000000000 : ℝ)
    (cell12772 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · have h := gap_lower (n := 12772) (a := (83139839054313 / 100000000000000 : ℝ)) (b := (161263983803 / 100000000000000 : ℝ)) (q := (140176716591 / 6250000000000 : ℝ))
      (E := (cell12772 ⟨27, by decide⟩).energy) (xi := (332149557608903 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12772 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12772]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12772])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12772) (a := (83139839054313 / 100000000000000 : ℝ)) (b := (161263983803 / 100000000000000 : ℝ)) (q := (140176716591 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12772])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12772])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12772]

theorem cert12772_28 : CellCertificate 12772 (884689989553397 / 10000000000000000 : ℝ) (328913087560311 / 200000000000000000 : ℝ) (332149557608903 / 10000000000000000 : ℝ)
    (cell12772 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · have h := gap_lower (n := 12772) (a := (41552773551401 / 50000000000000 : ℝ)) (b := (161263983803 / 100000000000000 : ℝ)) (q := (560707861421 / 25000000000000 : ℝ))
      (E := (cell12772 ⟨28, by decide⟩).energy) (xi := (332149557608903 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12772 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12772]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12772])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12772) (a := (41552773551401 / 50000000000000 : ℝ)) (b := (161263983803 / 100000000000000 : ℝ)) (q := (560707861421 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12772])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12772])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12772]

theorem cert12772_29 : CellCertificate 12772 (884689989553397 / 10000000000000000 : ℝ) (328913087560311 / 200000000000000000 : ℝ) (332149557608903 / 10000000000000000 : ℝ)
    (cell12772 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · have h := gap_lower (n := 12772) (a := (10383909891669 / 12500000000000 : ℝ)) (b := (161263983803 / 100000000000000 : ℝ)) (q := (2242835478087 / 100000000000000 : ℝ))
      (E := (cell12772 ⟨29, by decide⟩).energy) (xi := (332149557608903 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12772 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12772]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12772])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12772) (a := (10383909891669 / 12500000000000 : ℝ)) (b := (161263983803 / 100000000000000 : ℝ)) (q := (2242835478087 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12772])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12772])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12772]

theorem cert12772_30 : CellCertificate 12772 (884689989553397 / 10000000000000000 : ℝ) (328913087560311 / 200000000000000000 : ℝ) (332149557608903 / 10000000000000000 : ℝ)
    (cell12772 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · have h := gap_lower (n := 12772) (a := (83037035114303 / 100000000000000 : ℝ)) (b := (161263983803 / 100000000000000 : ℝ)) (q := (1121419723839 / 50000000000000 : ℝ))
      (E := (cell12772 ⟨30, by decide⟩).energy) (xi := (332149557608903 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12772 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12772]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12772])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12772) (a := (83037035114303 / 100000000000000 : ℝ)) (b := (161263983803 / 100000000000000 : ℝ)) (q := (1121419723839 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12772])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12772])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12772]

theorem cert12772_31 : CellCertificate 12772 (884689989553397 / 10000000000000000 : ℝ) (328913087560311 / 200000000000000000 : ℝ) (332149557608903 / 10000000000000000 : ℝ)
    (cell12772 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · have h := gap_lower (n := 12772) (a := (16600563002831 / 20000000000000 : ℝ)) (b := (161263983803 / 100000000000000 : ℝ)) (q := (140177717077 / 6250000000000 : ℝ))
      (E := (cell12772 ⟨31, by decide⟩).energy) (xi := (332149557608903 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12772 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12772]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12772])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12772) (a := (16600563002831 / 20000000000000 : ℝ)) (b := (161263983803 / 100000000000000 : ℝ)) (q := (140177717077 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12772])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12772])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12772]

theorem cert12772_32 : CellCertificate 12772 (884689989553397 / 10000000000000000 : ℝ) (328913087560311 / 200000000000000000 : ℝ) (332149557608903 / 10000000000000000 : ℝ)
    (cell12772 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · have h := gap_lower (n := 12772) (a := (82968618801567 / 100000000000000 : ℝ)) (b := (161263983803 / 100000000000000 : ℝ)) (q := (140177964951 / 6250000000000 : ℝ))
      (E := (cell12772 ⟨32, by decide⟩).energy) (xi := (332149557608903 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12772 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12772]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12772])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12772) (a := (82968618801567 / 100000000000000 : ℝ)) (b := (161263983803 / 100000000000000 : ℝ)) (q := (140177964951 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12772])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12772])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12772]

theorem cert12772_33 : CellCertificate 12772 (884689989553397 / 10000000000000000 : ℝ) (328913087560311 / 200000000000000000 : ℝ) (332149557608903 / 10000000000000000 : ℝ)
    (cell12772 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · have h := gap_lower (n := 12772) (a := (1036680580567 / 1250000000000 : ℝ)) (b := (161263983803 / 100000000000000 : ℝ)) (q := (2242851464039 / 100000000000000 : ℝ))
      (E := (cell12772 ⟨33, by decide⟩).energy) (xi := (332149557608903 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12772 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12772]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12772])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12772) (a := (1036680580567 / 1250000000000 : ℝ)) (b := (161263983803 / 100000000000000 : ℝ)) (q := (2242851464039 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12772])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12772])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12772]

theorem cert12772_34 : CellCertificate 12772 (884689989553397 / 10000000000000000 : ℝ) (328913087560311 / 200000000000000000 : ℝ) (332149557608903 / 10000000000000000 : ℝ)
    (cell12772 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · have h := gap_lower (n := 12772) (a := (82900297914513 / 100000000000000 : ℝ)) (b := (161263983803 / 100000000000000 : ℝ)) (q := (1121427745117 / 50000000000000 : ℝ))
      (E := (cell12772 ⟨34, by decide⟩).energy) (xi := (332149557608903 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12772 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12772]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12772])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12772) (a := (82900297914513 / 100000000000000 : ℝ)) (b := (161263983803 / 100000000000000 : ℝ)) (q := (1121427745117 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12772])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12772])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12772]

theorem cert12772_35 : CellCertificate 12772 (884689989553397 / 10000000000000000 : ℝ) (328913087560311 / 200000000000000000 : ℝ) (332149557608903 / 10000000000000000 : ℝ)
    (cell12772 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · have h := gap_lower (n := 12772) (a := (82866173178161 / 100000000000000 : ℝ)) (b := (161263983803 / 100000000000000 : ℝ)) (q := (2242859460013 / 100000000000000 : ℝ))
      (E := (cell12772 ⟨35, by decide⟩).energy) (xi := (332149557608903 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12772 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12772]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12772])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12772) (a := (82866173178161 / 100000000000000 : ℝ)) (b := (161263983803 / 100000000000000 : ℝ)) (q := (2242859460013 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12772])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12772])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12772]

theorem cert12772_36 : CellCertificate 12772 (884689989553397 / 10000000000000000 : ℝ) (328913087560311 / 200000000000000000 : ℝ) (332149557608903 / 10000000000000000 : ℝ)
    (cell12772 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · have h := gap_lower (n := 12772) (a := (82832072205597 / 100000000000000 : ℝ)) (b := (161263983803 / 100000000000000 : ℝ)) (q := (560715872813 / 25000000000000 : ℝ))
      (E := (cell12772 ⟨36, by decide⟩).energy) (xi := (332149557608903 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12772 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12772]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12772])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12772) (a := (82832072205597 / 100000000000000 : ℝ)) (b := (161263983803 / 100000000000000 : ℝ)) (q := (560715872813 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12772])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12772])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12772]

theorem cert12772_37 : CellCertificate 12772 (884689989553397 / 10000000000000000 : ℝ) (328913087560311 / 200000000000000000 : ℝ) (332149557608903 / 10000000000000000 : ℝ)
    (cell12772 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · have h := gap_lower (n := 12772) (a := (8279799496627 / 10000000000000 : ℝ)) (b := (161263983803 / 100000000000000 : ℝ)) (q := (2242867467053 / 100000000000000 : ℝ))
      (E := (cell12772 ⟨37, by decide⟩).energy) (xi := (332149557608903 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12772 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12772]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12772])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12772) (a := (8279799496627 / 10000000000000 : ℝ)) (b := (161263983803 / 100000000000000 : ℝ)) (q := (2242867467053 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12772])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12772])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12772]

theorem cert12772_38 : CellCertificate 12772 (884689989553397 / 10000000000000000 : ℝ) (328913087560311 / 200000000000000000 : ℝ) (332149557608903 / 10000000000000000 : ℝ)
    (cell12772 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · have h := gap_lower (n := 12772) (a := (41381970714891 / 50000000000000 : ℝ)) (b := (161263983803 / 100000000000000 : ℝ)) (q := (2242871504941 / 100000000000000 : ℝ))
      (E := (cell12772 ⟨38, by decide⟩).energy) (xi := (332149557608903 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12772 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12772]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12772])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12772) (a := (41381970714891 / 50000000000000 : ℝ)) (b := (161263983803 / 100000000000000 : ℝ)) (q := (2242871504941 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12772])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12772])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12772]

theorem cert12772_39 : CellCertificate 12772 (884689989553397 / 10000000000000000 : ℝ) (328913087560311 / 200000000000000000 : ℝ) (332149557608903 / 10000000000000000 : ℝ)
    (cell12772 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · have h := gap_lower (n := 12772) (a := (20682477891473 / 25000000000000 : ℝ)) (b := (161263983803 / 100000000000000 : ℝ)) (q := (1121437743739 / 50000000000000 : ℝ))
      (E := (cell12772 ⟨39, by decide⟩).energy) (xi := (332149557608903 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12772 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12772]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12772])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12772) (a := (20682477891473 / 25000000000000 : ℝ)) (b := (161263983803 / 100000000000000 : ℝ)) (q := (1121437743739 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12772])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12772])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12772]

theorem cert12773_20 : CellCertificate 12773 (884662356453811 / 10000000000000000 : ℝ) (1644436642446781 / 1000000000000000000 : ℝ) (332122926921453 / 10000000000000000 : ℝ)
    (cell12773 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · have h := gap_lower (n := 12773) (a := (4169027410499 / 5000000000000 : ℝ)) (b := (80625603149 / 50000000000000 : ℝ)) (q := (1121339525783 / 50000000000000 : ℝ))
      (E := (cell12773 ⟨20, by decide⟩).energy) (xi := (332122926921453 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12773 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12773]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12773])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12773) (a := (4169027410499 / 5000000000000 : ℝ)) (b := (80625603149 / 50000000000000 : ℝ)) (q := (1121339525783 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12773])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12773])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12773]

theorem cert12773_21 : CellCertificate 12773 (884662356453811 / 10000000000000000 : ℝ) (1644436642446781 / 1000000000000000000 : ℝ) (332122926921453 / 10000000000000000 : ℝ)
    (cell12773 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · have h := gap_lower (n := 12773) (a := (20836521948053 / 25000000000000 : ℝ)) (b := (80625603149 / 50000000000000 : ℝ)) (q := (280335384661 / 12500000000000 : ℝ))
      (E := (cell12773 ⟨21, by decide⟩).energy) (xi := (332122926921453 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12773 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12773]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12773])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12773) (a := (20836521948053 / 25000000000000 : ℝ)) (b := (80625603149 / 50000000000000 : ℝ)) (q := (280335384661 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12773])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12773])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12773]

theorem cert12773_22 : CellCertificate 12773 (884662356453811 / 10000000000000000 : ℝ) (1644436642446781 / 1000000000000000000 : ℝ) (332122926921453 / 10000000000000000 : ℝ)
    (cell12773 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · have h := gap_lower (n := 12773) (a := (41655825791157 / 50000000000000 : ℝ)) (b := (80625603149 / 50000000000000 : ℝ)) (q := (1121343538471 / 50000000000000 : ℝ))
      (E := (cell12773 ⟨22, by decide⟩).energy) (xi := (332122926921453 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12773 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12773]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12773])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12773) (a := (41655825791157 / 50000000000000 : ℝ)) (b := (80625603149 / 50000000000000 : ℝ)) (q := (1121343538471 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12773])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12773])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12773]

theorem cert12773_23 : CellCertificate 12773 (884662356453811 / 10000000000000000 : ℝ) (1644436642446781 / 1000000000000000000 : ℝ) (332122926921453 / 10000000000000000 : ℝ)
    (cell12773 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · have h := gap_lower (n := 12773) (a := (16655447909493 / 20000000000000 : ℝ)) (b := (80625603149 / 50000000000000 : ℝ)) (q := (1121345527073 / 50000000000000 : ℝ))
      (E := (cell12773 ⟨23, by decide⟩).energy) (xi := (332122926921453 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12773 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12773]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12773])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12773) (a := (16655447909493 / 20000000000000 : ℝ)) (b := (80625603149 / 50000000000000 : ℝ)) (q := (1121345527073 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12773])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12773])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12773]

theorem cert12773_24 : CellCertificate 12773 (884662356453811 / 10000000000000000 : ℝ) (1644436642446781 / 1000000000000000000 : ℝ) (332122926921453 / 10000000000000000 : ℝ)
    (cell12773 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · have h := gap_lower (n := 12773) (a := (10405356456877 / 12500000000000 : ℝ)) (b := (80625603149 / 50000000000000 : ℝ)) (q := (2242695070657 / 100000000000000 : ℝ))
      (E := (cell12773 ⟨24, by decide⟩).energy) (xi := (332122926921453 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12773 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12773]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12773])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12773) (a := (10405356456877 / 12500000000000 : ℝ)) (b := (80625603149 / 50000000000000 : ℝ)) (q := (2242695070657 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12773])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12773])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12773]

theorem cert12773_25 : CellCertificate 12773 (884662356453811 / 10000000000000000 : ℝ) (1644436642446781 / 1000000000000000000 : ℝ) (332122926921453 / 10000000000000000 : ℝ)
    (cell12773 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · have h := gap_lower (n := 12773) (a := (83208487872481 / 100000000000000 : ℝ)) (b := (80625603149 / 50000000000000 : ℝ)) (q := (2242699071293 / 100000000000000 : ℝ))
      (E := (cell12773 ⟨25, by decide⟩).energy) (xi := (332122926921453 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12773 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12773]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12773])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12773) (a := (83208487872481 / 100000000000000 : ℝ)) (b := (80625603149 / 50000000000000 : ℝ)) (q := (2242699071293 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12773])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12773])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12773]

theorem cert12773_26 : CellCertificate 12773 (884662356453811 / 10000000000000000 : ℝ) (1644436642446781 / 1000000000000000000 : ℝ) (332122926921453 / 10000000000000000 : ℝ)
    (cell12773 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · have h := gap_lower (n := 12773) (a := (41587074083773 / 50000000000000 : ℝ)) (b := (80625603149 / 50000000000000 : ℝ)) (q := (1121351529481 / 50000000000000 : ℝ))
      (E := (cell12773 ⟨26, by decide⟩).energy) (xi := (332122926921453 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12773 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12773]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12773])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12773) (a := (41587074083773 / 50000000000000 : ℝ)) (b := (80625603149 / 50000000000000 : ℝ)) (q := (1121351529481 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12773])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12773])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12773]

theorem cert12773_27 : CellCertificate 12773 (884662356453811 / 10000000000000000 : ℝ) (1644436642446781 / 1000000000000000000 : ℝ) (332122926921453 / 10000000000000000 : ℝ)
    (cell12773 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · have h := gap_lower (n := 12773) (a := (83139832508059 / 100000000000000 : ℝ)) (b := (80625603149 / 50000000000000 : ℝ)) (q := (448541418959 / 20000000000000 : ℝ))
      (E := (cell12773 ⟨27, by decide⟩).energy) (xi := (332122926921453 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12773 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12773]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12773])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12773) (a := (83139832508059 / 100000000000000 : ℝ)) (b := (80625603149 / 50000000000000 : ℝ)) (q := (448541418959 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12773])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12773])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12773]

theorem cert12773_28 : CellCertificate 12773 (884662356453811 / 10000000000000000 : ℝ) (1644436642446781 / 1000000000000000000 : ℝ) (332122926921453 / 10000000000000000 : ℝ)
    (cell12773 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · have h := gap_lower (n := 12773) (a := (5194096303877 / 6250000000000 : ℝ)) (b := (80625603149 / 50000000000000 : ℝ)) (q := (1121355532181 / 50000000000000 : ℝ))
      (E := (cell12773 ⟨28, by decide⟩).energy) (xi := (332122926921453 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12773 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12773]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12773])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12773) (a := (5194096303877 / 6250000000000 : ℝ)) (b := (80625603149 / 50000000000000 : ℝ)) (q := (1121355532181 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12773])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12773])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12773]

theorem cert12773_29 : CellCertificate 12773 (884662356453811 / 10000000000000000 : ℝ) (1644436642446781 / 1000000000000000000 : ℝ) (332122926921453 / 10000000000000000 : ℝ)
    (cell12773 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · have h := gap_lower (n := 12773) (a := (20767818299411 / 25000000000000 : ℝ)) (b := (80625603149 / 50000000000000 : ℝ)) (q := (2242715086801 / 100000000000000 : ℝ))
      (E := (cell12773 ⟨29, by decide⟩).energy) (xi := (332122926921453 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12773 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12773]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12773])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12773) (a := (20767818299411 / 25000000000000 : ℝ)) (b := (80625603149 / 50000000000000 : ℝ)) (q := (2242715086801 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12773])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12773])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12773]

theorem cert12773_30 : CellCertificate 12773 (884662356453811 / 10000000000000000 : ℝ) (1644436642446781 / 1000000000000000000 : ℝ) (332122926921453 / 10000000000000000 : ℝ)
    (cell12773 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · have h := gap_lower (n := 12773) (a := (83037029483233 / 100000000000000 : ℝ)) (b := (80625603149 / 50000000000000 : ℝ)) (q := (2242719105649 / 100000000000000 : ℝ))
      (E := (cell12773 ⟨30, by decide⟩).energy) (xi := (332122926921453 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12773 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12773]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12773])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12773) (a := (83037029483233 / 100000000000000 : ℝ)) (b := (80625603149 / 50000000000000 : ℝ)) (q := (2242719105649 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12773])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12773])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12773]

theorem cert12773_31 : CellCertificate 12773 (884662356453811 / 10000000000000000 : ℝ) (1644436642446781 / 1000000000000000000 : ℝ) (332122926921453 / 10000000000000000 : ℝ)
    (cell12773 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · have h := gap_lower (n := 12773) (a := (83002809687299 / 100000000000000 : ℝ)) (b := (80625603149 / 50000000000000 : ℝ)) (q := (1121361561331 / 50000000000000 : ℝ))
      (E := (cell12773 ⟨31, by decide⟩).energy) (xi := (332122926921453 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12773 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12773]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12773])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12773) (a := (83002809687299 / 100000000000000 : ℝ)) (b := (80625603149 / 50000000000000 : ℝ)) (q := (1121361561331 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12773])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12773])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12773]

theorem cert12773_32 : CellCertificate 12773 (884662356453811 / 10000000000000000 : ℝ) (1644436642446781 / 1000000000000000000 : ℝ) (332122926921453 / 10000000000000000 : ℝ)
    (cell12773 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · have h := gap_lower (n := 12773) (a := (41484306889253 / 50000000000000 : ℝ)) (b := (80625603149 / 50000000000000 : ℝ)) (q := (2242727080799 / 100000000000000 : ℝ))
      (E := (cell12773 ⟨32, by decide⟩).energy) (xi := (332122926921453 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12773 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12773]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12773])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12773) (a := (41484306889253 / 50000000000000 : ℝ)) (b := (80625603149 / 50000000000000 : ℝ)) (q := (2242727080799 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12773])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12773])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12773]

theorem cert12773_33 : CellCertificate 12773 (884662356453811 / 10000000000000000 : ℝ) (1644436642446781 / 1000000000000000000 : ℝ) (332122926921453 / 10000000000000000 : ℝ)
    (cell12773 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · have h := gap_lower (n := 12773) (a := (10366805215709 / 12500000000000 : ℝ)) (b := (80625603149 / 50000000000000 : ℝ)) (q := (1121365549237 / 50000000000000 : ℝ))
      (E := (cell12773 ⟨33, by decide⟩).energy) (xi := (332122926921453 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12773 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12773]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12773])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12773) (a := (10366805215709 / 12500000000000 : ℝ)) (b := (80625603149 / 50000000000000 : ℝ)) (q := (1121365549237 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12773])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12773])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12773]

theorem cert12773_34 : CellCertificate 12773 (884662356453811 / 10000000000000000 : ℝ) (1644436642446781 / 1000000000000000000 : ℝ) (332122926921453 / 10000000000000000 : ℝ)
    (cell12773 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · have h := gap_lower (n := 12773) (a := (41450146748889 / 50000000000000 : ℝ)) (b := (80625603149 / 50000000000000 : ℝ)) (q := (280341889777 / 12500000000000 : ℝ))
      (E := (cell12773 ⟨34, by decide⟩).energy) (xi := (332122926921453 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12773 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12773]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12773])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12773) (a := (41450146748889 / 50000000000000 : ℝ)) (b := (80625603149 / 50000000000000 : ℝ)) (q := (280341889777 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12773])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12773])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12773]

theorem cert12773_35 : CellCertificate 12773 (884662356453811 / 10000000000000000 : ℝ) (1644436642446781 / 1000000000000000000 : ℝ) (332122926921453 / 10000000000000000 : ℝ)
    (cell12773 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · have h := gap_lower (n := 12773) (a := (2071654226599 / 2500000000000 : ℝ)) (b := (80625603149 / 50000000000000 : ℝ)) (q := (1121369570437 / 50000000000000 : ℝ))
      (E := (cell12773 ⟨35, by decide⟩).energy) (xi := (332122926921453 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12773 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12773]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12773])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12773) (a := (2071654226599 / 2500000000000 : ℝ)) (b := (80625603149 / 50000000000000 : ℝ)) (q := (1121369570437 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12773])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12773])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12773]

theorem cert12773_36 : CellCertificate 12773 (884662356453811 / 10000000000000000 : ℝ) (1644436642446781 / 1000000000000000000 : ℝ) (332122926921453 / 10000000000000000 : ℝ)
    (cell12773 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · have h := gap_lower (n := 12773) (a := (82832068393511 / 100000000000000 : ℝ)) (b := (80625603149 / 50000000000000 : ℝ)) (q := (2242743108413 / 100000000000000 : ℝ))
      (E := (cell12773 ⟨36, by decide⟩).energy) (xi := (332122926921453 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12773 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12773]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12773])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12773) (a := (82832068393511 / 100000000000000 : ℝ)) (b := (80625603149 / 50000000000000 : ℝ)) (q := (2242743108413 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12773])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12773])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12773]

theorem cert12773_37 : CellCertificate 12773 (884662356453811 / 10000000000000000 : ℝ) (1644436642446781 / 1000000000000000000 : ℝ) (332122926921453 / 10000000000000000 : ℝ)
    (cell12773 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · have h := gap_lower (n := 12773) (a := (41398995727941 / 50000000000000 : ℝ)) (b := (80625603149 / 50000000000000 : ℝ)) (q := (70085848079 / 3125000000000 : ℝ))
      (E := (cell12773 ⟨37, by decide⟩).energy) (xi := (332122926921453 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12773 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12773]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12773])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12773) (a := (41398995727941 / 50000000000000 : ℝ)) (b := (80625603149 / 50000000000000 : ℝ)) (q := (70085848079 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12773])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12773])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12773]

theorem cert12773_38 : CellCertificate 12773 (884662356453811 / 10000000000000000 : ℝ) (1644436642446781 / 1000000000000000000 : ℝ) (332122926921453 / 10000000000000000 : ℝ)
    (cell12773 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · have h := gap_lower (n := 12773) (a := (20690984555169 / 25000000000000 : ℝ)) (b := (80625603149 / 50000000000000 : ℝ)) (q := (2242751114053 / 100000000000000 : ℝ))
      (E := (cell12773 ⟨38, by decide⟩).energy) (xi := (332122926921453 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12773 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12773]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12773])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12773) (a := (20690984555169 / 25000000000000 : ℝ)) (b := (80625603149 / 50000000000000 : ℝ)) (q := (2242751114053 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12773])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12773])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12773]

theorem cert12773_39 : CellCertificate 12773 (884662356453811 / 10000000000000000 : ℝ) (1644436642446781 / 1000000000000000000 : ℝ) (332122926921453 / 10000000000000000 : ℝ)
    (cell12773 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · have h := gap_lower (n := 12773) (a := (82729908657651 / 100000000000000 : ℝ)) (b := (80625603149 / 50000000000000 : ℝ)) (q := (448551030467 / 20000000000000 : ℝ))
      (E := (cell12773 ⟨39, by decide⟩).energy) (xi := (332122926921453 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12773 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12773]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12773])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12773) (a := (82729908657651 / 100000000000000 : ℝ)) (b := (80625603149 / 50000000000000 : ℝ)) (q := (448551030467 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12773])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12773])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12773]

theorem cert12774_20 : CellCertificate 12774 (442317363752989 / 5000000000000000 : ℝ) (1644307867263831 / 1000000000000000000 : ℝ) (332096300557013 / 10000000000000000 : ℝ)
    (cell12774 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · have h := gap_lower (n := 12774) (a := (83380539514977 / 100000000000000 : ℝ)) (b := (16123843083 / 10000000000000 : ℝ)) (q := (2242558713049 / 100000000000000 : ℝ))
      (E := (cell12774 ⟨20, by decide⟩).energy) (xi := (332096300557013 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12774 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12774]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12774])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12774) (a := (83380539514977 / 100000000000000 : ℝ)) (b := (16123843083 / 10000000000000 : ℝ)) (q := (2242558713049 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12774])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12774])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12774]

theorem cert12774_21 : CellCertificate 12774 (442317363752989 / 5000000000000000 : ℝ) (1644307867263831 / 1000000000000000000 : ℝ) (332096300557013 / 10000000000000000 : ℝ)
    (cell12774 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · have h := gap_lower (n := 12774) (a := (83346079405649 / 100000000000000 : ℝ)) (b := (16123843083 / 10000000000000 : ℝ)) (q := (560640680801 / 25000000000000 : ℝ))
      (E := (cell12774 ⟨21, by decide⟩).energy) (xi := (332096300557013 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12774 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12774]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12774])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12774) (a := (83346079405649 / 100000000000000 : ℝ)) (b := (16123843083 / 10000000000000 : ℝ)) (q := (560640680801 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12774])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12774])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12774]

theorem cert12774_22 : CellCertificate 12774 (442317363752989 / 5000000000000000 : ℝ) (1644307867263831 / 1000000000000000000 : ℝ) (332096300557013 / 10000000000000000 : ℝ)
    (cell12774 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · have h := gap_lower (n := 12774) (a := (1041395543797 / 1250000000000 : ℝ)) (b := (16123843083 / 10000000000000 : ℝ)) (q := (2242566766329 / 100000000000000 : ℝ))
      (E := (cell12774 ⟨22, by decide⟩).energy) (xi := (332096300557013 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12774 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12774]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12774])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12774) (a := (1041395543797 / 1250000000000 : ℝ)) (b := (16123843083 / 10000000000000 : ℝ)) (q := (2242566766329 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12774])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12774])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12774]

theorem cert12774_23 : CellCertificate 12774 (442317363752989 / 5000000000000000 : ℝ) (1644307867263831 / 1000000000000000000 : ℝ) (332096300557013 / 10000000000000000 : ℝ)
    (cell12774 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · have h := gap_lower (n := 12774) (a := (83277231776491 / 100000000000000 : ℝ)) (b := (16123843083 / 10000000000000 : ℝ)) (q := (2242570729399 / 100000000000000 : ℝ))
      (E := (cell12774 ⟨23, by decide⟩).energy) (xi := (332096300557013 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12774 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12774]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12774])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12774) (a := (83277231776491 / 100000000000000 : ℝ)) (b := (16123843083 / 10000000000000 : ℝ)) (q := (2242570729399 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12774])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12774])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12774]

theorem cert12774_24 : CellCertificate 12774 (442317363752989 / 5000000000000000 : ℝ) (1644307867263831 / 1000000000000000000 : ℝ) (332096300557013 / 10000000000000000 : ℝ)
    (cell12774 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · have h := gap_lower (n := 12774) (a := (41621422095597 / 50000000000000 : ℝ)) (b := (16123843083 / 10000000000000 : ℝ)) (q := (2242574732481 / 100000000000000 : ℝ))
      (E := (cell12774 ⟨24, by decide⟩).energy) (xi := (332096300557013 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12774 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12774]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12774])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12774) (a := (41621422095597 / 50000000000000 : ℝ)) (b := (16123843083 / 10000000000000 : ℝ)) (q := (2242574732481 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12774])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12774])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12774]

theorem cert12774_25 : CellCertificate 12774 (442317363752989 / 5000000000000000 : ℝ) (1644307867263831 / 1000000000000000000 : ℝ) (332096300557013 / 10000000000000000 : ℝ)
    (cell12774 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · have h := gap_lower (n := 12774) (a := (16641696143077 / 20000000000000 : ℝ)) (b := (16123843083 / 10000000000000 : ℝ)) (q := (2242578778791 / 100000000000000 : ℝ))
      (E := (cell12774 ⟨25, by decide⟩).energy) (xi := (332096300557013 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12774 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12774]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12774])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12774) (a := (16641696143077 / 20000000000000 : ℝ)) (b := (16123843083 / 10000000000000 : ℝ)) (q := (2242578778791 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12774])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12774])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12774]

theorem cert12774_26 : CellCertificate 12774 (442317363752989 / 5000000000000000 : ℝ) (1644307867263831 / 1000000000000000000 : ℝ) (332096300557013 / 10000000000000000 : ℝ)
    (cell12774 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · have h := gap_lower (n := 12774) (a := (20793535329187 / 25000000000000 : ℝ)) (b := (16123843083 / 10000000000000 : ℝ)) (q := (1121291377229 / 50000000000000 : ℝ))
      (E := (cell12774 ⟨26, by decide⟩).energy) (xi := (332096300557013 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12774 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12774]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12774])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12774) (a := (20793535329187 / 25000000000000 : ℝ)) (b := (16123843083 / 10000000000000 : ℝ)) (q := (1121291377229 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12774])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12774])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12774]

theorem cert12774_27 : CellCertificate 12774 (442317363752989 / 5000000000000000 : ℝ) (1644307867263831 / 1000000000000000000 : ℝ) (332096300557013 / 10000000000000000 : ℝ)
    (cell12774 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · have h := gap_lower (n := 12774) (a := (83139825963133 / 100000000000000 : ℝ)) (b := (16123843083 / 10000000000000 : ℝ)) (q := (224258677899 / 10000000000000 : ℝ))
      (E := (cell12774 ⟨27, by decide⟩).energy) (xi := (332096300557013 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12774 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12774]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12774])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12774) (a := (83139825963133 / 100000000000000 : ℝ)) (b := (16123843083 / 10000000000000 : ℝ)) (q := (224258677899 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12774])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12774])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12774]

theorem cert12774_28 : CellCertificate 12774 (442317363752989 / 5000000000000000 : ℝ) (1644307867263831 / 1000000000000000000 : ℝ) (332096300557013 / 10000000000000000 : ℝ)
    (cell12774 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · have h := gap_lower (n := 12774) (a := (16621106924511 / 20000000000000 : ℝ)) (b := (16123843083 / 10000000000000 : ℝ)) (q := (560647684489 / 25000000000000 : ℝ))
      (E := (cell12774 ⟨28, by decide⟩).energy) (xi := (332096300557013 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12774 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12774]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12774])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12774) (a := (16621106924511 / 20000000000000 : ℝ)) (b := (16123843083 / 10000000000000 : ℝ)) (q := (560647684489 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12774])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12774])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12774]

theorem cert12774_29 : CellCertificate 12774 (442317363752989 / 5000000000000000 : ℝ) (1644307867263831 / 1000000000000000000 : ℝ) (332096300557013 / 10000000000000000 : ℝ)
    (cell12774 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · have h := gap_lower (n := 12774) (a := (8307126726319 / 10000000000000 : ℝ)) (b := (16123843083 / 10000000000000 : ℝ)) (q := (448518950099 / 20000000000000 : ℝ))
      (E := (cell12774 ⟨29, by decide⟩).energy) (xi := (332096300557013 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12774 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12774]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12774])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12774) (a := (8307126726319 / 10000000000000 : ℝ)) (b := (16123843083 / 10000000000000 : ℝ)) (q := (448518950099 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12774])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12774])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12774]

theorem cert12774_30 : CellCertificate 12774 (442317363752989 / 5000000000000000 : ℝ) (1644307867263831 / 1000000000000000000 : ℝ) (332096300557013 / 10000000000000000 : ℝ)
    (cell12774 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · have h := gap_lower (n := 12774) (a := (4151851192669 / 5000000000000 : ℝ)) (b := (16123843083 / 10000000000000 : ℝ)) (q := (112129938007 / 5000000000000 : ℝ))
      (E := (cell12774 ⟨30, by decide⟩).energy) (xi := (332096300557013 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12774 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12774]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12774])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12774) (a := (4151851192669 / 5000000000000 : ℝ)) (b := (16123843083 / 10000000000000 : ℝ)) (q := (112129938007 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12774])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12774])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12774]

theorem cert12774_31 : CellCertificate 12774 (442317363752989 / 5000000000000000 : ℝ) (1644307867263831 / 1000000000000000000 : ℝ) (332096300557013 / 10000000000000000 : ℝ)
    (cell12774 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · have h := gap_lower (n := 12774) (a := (41501402180813 / 50000000000000 : ℝ)) (b := (16123843083 / 10000000000000 : ℝ)) (q := (2242602768647 / 100000000000000 : ℝ))
      (E := (cell12774 ⟨31, by decide⟩).energy) (xi := (332096300557013 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12774 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12774]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12774])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12774) (a := (41501402180813 / 50000000000000 : ℝ)) (b := (16123843083 / 10000000000000 : ℝ)) (q := (2242602768647 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12774])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12774])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12774]

theorem cert12774_32 : CellCertificate 12774 (442317363752989 / 5000000000000000 : ℝ) (1644307867263831 / 1000000000000000000 : ℝ) (332096300557013 / 10000000000000000 : ℝ)
    (cell12774 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · have h := gap_lower (n := 12774) (a := (82968608756589 / 100000000000000 : ℝ)) (b := (16123843083 / 10000000000000 : ℝ)) (q := (448521355509 / 20000000000000 : ℝ))
      (E := (cell12774 ⟨32, by decide⟩).energy) (xi := (332096300557013 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12774 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12774]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12774])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12774) (a := (82968608756589 / 100000000000000 : ℝ)) (b := (16123843083 / 10000000000000 : ℝ)) (q := (448521355509 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12774])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12774])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12774]

theorem cert12774_33 : CellCertificate 12774 (442317363752989 / 5000000000000000 : ℝ) (1644307867263831 / 1000000000000000000 : ℝ) (332096300557013 / 10000000000000000 : ℝ)
    (cell12774 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · have h := gap_lower (n := 12774) (a := (20733609251773 / 25000000000000 : ℝ)) (b := (16123843083 / 10000000000000 : ℝ)) (q := (560652697033 / 25000000000000 : ℝ))
      (E := (cell12774 ⟨33, by decide⟩).energy) (xi := (332096300557013 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12774 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12774]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12774])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12774) (a := (20733609251773 / 25000000000000 : ℝ)) (b := (16123843083 / 10000000000000 : ℝ)) (q := (560652697033 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12774])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12774])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12774]

theorem cert12774_34 : CellCertificate 12774 (442317363752989 / 5000000000000000 : ℝ) (1644307867263831 / 1000000000000000000 : ℝ) (332096300557013 / 10000000000000000 : ℝ)
    (cell12774 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · have h := gap_lower (n := 12774) (a := (41450144541057 / 50000000000000 : ℝ)) (b := (16123843083 / 10000000000000 : ℝ)) (q := (1121307400741 / 50000000000000 : ℝ))
      (E := (cell12774 ⟨34, by decide⟩).energy) (xi := (332096300557013 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12774 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12774]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12774])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12774) (a := (41450144541057 / 50000000000000 : ℝ)) (b := (16123843083 / 10000000000000 : ℝ)) (q := (1121307400741 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12774])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12774])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12774]

theorem cert12774_35 : CellCertificate 12774 (442317363752989 / 5000000000000000 : ℝ) (1644307867263831 / 1000000000000000000 : ℝ) (332096300557013 / 10000000000000000 : ℝ)
    (cell12774 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · have h := gap_lower (n := 12774) (a := (41433082475397 / 50000000000000 : ℝ)) (b := (16123843083 / 10000000000000 : ℝ)) (q := (2242618818443 / 100000000000000 : ℝ))
      (E := (cell12774 ⟨35, by decide⟩).energy) (xi := (332096300557013 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12774 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12774]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12774])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12774) (a := (41433082475397 / 50000000000000 : ℝ)) (b := (16123843083 / 10000000000000 : ℝ)) (q := (2242618818443 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12774])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12774])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12774]

theorem cert12774_36 : CellCertificate 12774 (442317363752989 / 5000000000000000 : ℝ) (1644307867263831 / 1000000000000000000 : ℝ) (332096300557013 / 10000000000000000 : ℝ)
    (cell12774 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · have h := gap_lower (n := 12774) (a := (3313282583297 / 4000000000000 : ℝ)) (b := (16123843083 / 10000000000000 : ℝ)) (q := (1121311390489 / 50000000000000 : ℝ))
      (E := (cell12774 ⟨36, by decide⟩).energy) (xi := (332096300557013 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12774 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12774]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12774])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12774) (a := (3313282583297 / 4000000000000 : ℝ)) (b := (16123843083 / 10000000000000 : ℝ)) (q := (1121311390489 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12774])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12774])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12774]

theorem cert12774_37 : CellCertificate 12774 (442317363752989 / 5000000000000000 : ℝ) (1644307867263831 / 1000000000000000000 : ℝ) (332096300557013 / 10000000000000000 : ℝ)
    (cell12774 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · have h := gap_lower (n := 12774) (a := (41398993973229 / 50000000000000 : ℝ)) (b := (16123843083 / 10000000000000 : ℝ)) (q := (2242626806783 / 100000000000000 : ℝ))
      (E := (cell12774 ⟨37, by decide⟩).energy) (xi := (332096300557013 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12774 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12774]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12774])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12774) (a := (41398993973229 / 50000000000000 : ℝ)) (b := (16123843083 / 10000000000000 : ℝ)) (q := (2242626806783 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12774])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12774])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12774]

theorem cert12774_38 : CellCertificate 12774 (442317363752989 / 5000000000000000 : ℝ) (1644307867263831 / 1000000000000000000 : ℝ) (332096300557013 / 10000000000000000 : ℝ)
    (cell12774 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · have h := gap_lower (n := 12774) (a := (82763935012497 / 100000000000000 : ℝ)) (b := (16123843083 / 10000000000000 : ℝ)) (q := (2242630778691 / 100000000000000 : ℝ))
      (E := (cell12774 ⟨38, by decide⟩).energy) (xi := (332096300557013 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12774 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12774]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12774])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12774) (a := (82763935012497 / 100000000000000 : ℝ)) (b := (16123843083 / 10000000000000 : ℝ)) (q := (2242630778691 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12774])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12774])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12774]

theorem cert12774_39 : CellCertificate 12774 (442317363752989 / 5000000000000000 : ℝ) (1644307867263831 / 1000000000000000000 : ℝ) (332096300557013 / 10000000000000000 : ℝ)
    (cell12774 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · have h := gap_lower (n := 12774) (a := (827299057503 / 1000000000000 : ℝ)) (b := (16123843083 / 10000000000000 : ℝ)) (q := (2242634814049 / 100000000000000 : ℝ))
      (E := (cell12774 ⟨39, by decide⟩).energy) (xi := (332096300557013 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12774 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12774]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12774])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12774) (a := (827299057503 / 1000000000000 : ℝ)) (b := (16123843083 / 10000000000000 : ℝ)) (q := (2242634814049 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12774])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12774])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12774]

end BstLean.Part268
