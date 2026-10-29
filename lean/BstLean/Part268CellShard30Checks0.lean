import BstLean.Part268CellShard30Data

/-! Twenty scalar cells per dimension in a 25-dimension shard. -/
namespace BstLean.Part268
open Real BstLean.Part263

theorem cert13100_0 : CellCertificate 13100 (875843412266401 / 10000000000000000 : ℝ) (320675081395459 / 200000000000000000 : ℝ) (323640126141257 / 10000000000000000 : ℝ)
    (cell13100 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · have h := gap_lower (n := 13100) (a := (84070123725719 / 100000000000000 : ℝ)) (b := (78589683071 / 50000000000000 : ℝ)) (q := (2204690845569 / 100000000000000 : ℝ))
      (E := (cell13100 ⟨0, by decide⟩).energy) (xi := (323640126141257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13100 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13100]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13100])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13100) (a := (84070123725719 / 100000000000000 : ℝ)) (b := (78589683071 / 50000000000000 : ℝ)) (q := (2204690845569 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13100])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13100])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13100]

theorem cert13100_1 : CellCertificate 13100 (875843412266401 / 10000000000000000 : ℝ) (320675081395459 / 200000000000000000 : ℝ) (323640126141257 / 10000000000000000 : ℝ)
    (cell13100 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · have h := gap_lower (n := 13100) (a := (8403523489617 / 10000000000000 : ℝ)) (b := (78589683071 / 50000000000000 : ℝ)) (q := (440938973513 / 20000000000000 : ℝ))
      (E := (cell13100 ⟨1, by decide⟩).energy) (xi := (323640126141257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13100 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13100]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13100])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13100) (a := (8403523489617 / 10000000000000 : ℝ)) (b := (78589683071 / 50000000000000 : ℝ)) (q := (440938973513 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13100])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13100])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13100]

theorem cert13100_2 : CellCertificate 13100 (875843412266401 / 10000000000000000 : ℝ) (320675081395459 / 200000000000000000 : ℝ) (323640126141257 / 10000000000000000 : ℝ)
    (cell13100 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · have h := gap_lower (n := 13100) (a := (10500046359947 / 12500000000000 : ℝ)) (b := (78589683071 / 50000000000000 : ℝ)) (q := (1102349445637 / 50000000000000 : ℝ))
      (E := (cell13100 ⟨2, by decide⟩).energy) (xi := (323640126141257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13100 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13100]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13100])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13100) (a := (10500046359947 / 12500000000000 : ℝ)) (b := (78589683071 / 50000000000000 : ℝ)) (q := (1102349445637 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13100])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13100])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13100]

theorem cert13100_3 : CellCertificate 13100 (875843412266401 / 10000000000000000 : ℝ) (320675081395459 / 200000000000000000 : ℝ) (323640126141257 / 10000000000000000 : ℝ)
    (cell13100 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · have h := gap_lower (n := 13100) (a := (16793106327941 / 20000000000000 : ℝ)) (b := (78589683071 / 50000000000000 : ℝ)) (q := (220470292507 / 10000000000000 : ℝ))
      (E := (cell13100 ⟨3, by decide⟩).energy) (xi := (323640126141257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13100 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13100]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13100])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13100) (a := (16793106327941 / 20000000000000 : ℝ)) (b := (78589683071 / 50000000000000 : ℝ)) (q := (220470292507 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13100])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13100])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13100]

theorem cert13100_4 : CellCertificate 13100 (875843412266401 / 10000000000000000 : ℝ) (320675081395459 / 200000000000000000 : ℝ) (323640126141257 / 10000000000000000 : ℝ)
    (cell13100 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · have h := gap_lower (n := 13100) (a := (16786143428103 / 20000000000000 : ℝ)) (b := (78589683071 / 50000000000000 : ℝ)) (q := (2204706919129 / 100000000000000 : ℝ))
      (E := (cell13100 ⟨4, by decide⟩).energy) (xi := (323640126141257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13100 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13100]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13100])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13100) (a := (16786143428103 / 20000000000000 : ℝ)) (b := (78589683071 / 50000000000000 : ℝ)) (q := (2204706919129 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13100])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13100])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13100]

theorem cert13100_5 : CellCertificate 13100 (875843412266401 / 10000000000000000 : ℝ) (320675081395459 / 200000000000000000 : ℝ) (323640126141257 / 10000000000000000 : ℝ)
    (cell13100 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · have h := gap_lower (n := 13100) (a := (83895927346151 / 100000000000000 : ℝ)) (b := (78589683071 / 50000000000000 : ℝ)) (q := (220471093921 / 10000000000000 : ℝ))
      (E := (cell13100 ⟨5, by decide⟩).energy) (xi := (323640126141257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13100 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13100]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13100])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13100) (a := (83895927346151 / 100000000000000 : ℝ)) (b := (78589683071 / 50000000000000 : ℝ)) (q := (220471093921 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13100])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13100])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13100]

theorem cert13100_6 : CellCertificate 13100 (875843412266401 / 10000000000000000 : ℝ) (320675081395459 / 200000000000000000 : ℝ) (323640126141257 / 10000000000000000 : ℝ)
    (cell13100 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · have h := gap_lower (n := 13100) (a := (1677223244419 / 2000000000000 : ℝ)) (b := (78589683071 / 50000000000000 : ℝ)) (q := (2204714934931 / 100000000000000 : ℝ))
      (E := (cell13100 ⟨6, by decide⟩).energy) (xi := (323640126141257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13100 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13100]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13100])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13100) (a := (1677223244419 / 2000000000000 : ℝ)) (b := (78589683071 / 50000000000000 : ℝ)) (q := (2204714934931 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13100])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13100])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13100]

theorem cert13100_7 : CellCertificate 13100 (875843412266401 / 10000000000000000 : ℝ) (320675081395459 / 200000000000000000 : ℝ) (323640126141257 / 10000000000000000 : ℝ)
    (cell13100 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · have h := gap_lower (n := 13100) (a := (10478302716179 / 12500000000000 : ℝ)) (b := (78589683071 / 50000000000000 : ℝ)) (q := (1102359456789 / 50000000000000 : ℝ))
      (E := (cell13100 ⟨7, by decide⟩).energy) (xi := (323640126141257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13100 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13100]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13100])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13100) (a := (10478302716179 / 12500000000000 : ℝ)) (b := (78589683071 / 50000000000000 : ℝ)) (q := (1102359456789 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13100])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13100])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13100]

theorem cert13100_8 : CellCertificate 13100 (875843412266401 / 10000000000000000 : ℝ) (320675081395459 / 200000000000000000 : ℝ) (323640126141257 / 10000000000000000 : ℝ)
    (cell13100 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · have h := gap_lower (n := 13100) (a := (5236981614769 / 6250000000000 : ℝ)) (b := (78589683071 / 50000000000000 : ℝ)) (q := (2204722940219 / 100000000000000 : ℝ))
      (E := (cell13100 ⟨8, by decide⟩).energy) (xi := (323640126141257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13100 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13100]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13100])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13100) (a := (5236981614769 / 6250000000000 : ℝ)) (b := (78589683071 / 50000000000000 : ℝ)) (q := (2204722940219 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13100])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13100])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13100]

theorem cert13100_9 : CellCertificate 13100 (875843412266401 / 10000000000000000 : ℝ) (320675081395459 / 200000000000000000 : ℝ) (323640126141257 / 10000000000000000 : ℝ)
    (cell13100 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · have h := gap_lower (n := 13100) (a := (41878507253229 / 50000000000000 : ℝ)) (b := (78589683071 / 50000000000000 : ℝ)) (q := (34448858807 / 1562500000000 : ℝ))
      (E := (cell13100 ⟨9, by decide⟩).energy) (xi := (323640126141257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13100 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13100]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13100])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13100) (a := (41878507253229 / 50000000000000 : ℝ)) (b := (78589683071 / 50000000000000 : ℝ)) (q := (34448858807 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13100])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13100])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13100]

theorem cert13100_10 : CellCertificate 13100 (875843412266401 / 10000000000000000 : ℝ) (320675081395459 / 200000000000000000 : ℝ) (323640126141257 / 10000000000000000 : ℝ)
    (cell13100 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · have h := gap_lower (n := 13100) (a := (83722347704969 / 100000000000000 : ℝ)) (b := (78589683071 / 50000000000000 : ℝ)) (q := (440946198079 / 20000000000000 : ℝ))
      (E := (cell13100 ⟨10, by decide⟩).energy) (xi := (323640126141257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13100 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13100]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13100])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13100) (a := (83722347704969 / 100000000000000 : ℝ)) (b := (78589683071 / 50000000000000 : ℝ)) (q := (440946198079 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13100])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13100])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13100]

theorem cert13100_11 : CellCertificate 13100 (875843412266401 / 10000000000000000 : ℝ) (320675081395459 / 200000000000000000 : ℝ) (323640126141257 / 10000000000000000 : ℝ)
    (cell13100 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · have h := gap_lower (n := 13100) (a := (20921926349273 / 25000000000000 : ℝ)) (b := (78589683071 / 50000000000000 : ℝ)) (q := (2204734968639 / 100000000000000 : ℝ))
      (E := (cell13100 ⟨11, by decide⟩).energy) (xi := (323640126141257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13100 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13100]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13100])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13100) (a := (20921926349273 / 25000000000000 : ℝ)) (b := (78589683071 / 50000000000000 : ℝ)) (q := (2204734968639 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13100])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13100])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13100]

theorem cert13100_12 : CellCertificate 13100 (875843412266401 / 10000000000000000 : ℝ) (320675081395459 / 200000000000000000 : ℝ) (323640126141257 / 10000000000000000 : ℝ)
    (cell13100 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · have h := gap_lower (n := 13100) (a := (41826543774133 / 50000000000000 : ℝ)) (b := (78589683071 / 50000000000000 : ℝ)) (q := (2204739020603 / 100000000000000 : ℝ))
      (E := (cell13100 ⟨12, by decide⟩).energy) (xi := (323640126141257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13100 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13100]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13100])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13100) (a := (41826543774133 / 50000000000000 : ℝ)) (b := (78589683071 / 50000000000000 : ℝ)) (q := (2204739020603 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13100])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13100])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13100]

theorem cert13100_13 : CellCertificate 13100 (875843412266401 / 10000000000000000 : ℝ) (320675081395459 / 200000000000000000 : ℝ) (323640126141257 / 10000000000000000 : ℝ)
    (cell13100 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · have h := gap_lower (n := 13100) (a := (83618494124107 / 100000000000000 : ℝ)) (b := (78589683071 / 50000000000000 : ℝ)) (q := (2204743035841 / 100000000000000 : ℝ))
      (E := (cell13100 ⟨13, by decide⟩).energy) (xi := (323640126141257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13100 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13100]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13100])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13100) (a := (83618494124107 / 100000000000000 : ℝ)) (b := (78589683071 / 50000000000000 : ℝ)) (q := (2204743035841 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13100])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13100])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13100]

theorem cert13100_14 : CellCertificate 13100 (875843412266401 / 10000000000000000 : ℝ) (320675081395459 / 200000000000000000 : ℝ) (323640126141257 / 10000000000000000 : ℝ)
    (cell13100 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · have h := gap_lower (n := 13100) (a := (8358392509041 / 10000000000000 : ℝ)) (b := (78589683071 / 50000000000000 : ℝ)) (q := (551186754957 / 25000000000000 : ℝ))
      (E := (cell13100 ⟨14, by decide⟩).energy) (xi := (323640126141257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13100 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13100]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13100])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13100) (a := (8358392509041 / 10000000000000 : ℝ)) (b := (78589683071 / 50000000000000 : ℝ)) (q := (551186754957 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13100])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13100])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13100]

theorem cert13100_15 : CellCertificate 13100 (875843412266401 / 10000000000000000 : ℝ) (320675081395459 / 200000000000000000 : ℝ) (323640126141257 / 10000000000000000 : ℝ)
    (cell13100 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · have h := gap_lower (n := 13100) (a := (20887345103287 / 25000000000000 : ℝ)) (b := (78589683071 / 50000000000000 : ℝ)) (q := (275593879499 / 12500000000000 : ℝ))
      (E := (cell13100 ⟨15, by decide⟩).energy) (xi := (323640126141257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13100 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13100]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13100])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13100) (a := (20887345103287 / 25000000000000 : ℝ)) (b := (78589683071 / 50000000000000 : ℝ)) (q := (275593879499 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13100])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13100])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13100]

theorem cert13100_16 : CellCertificate 13100 (875843412266401 / 10000000000000000 : ℝ) (320675081395459 / 200000000000000000 : ℝ) (323640126141257 / 10000000000000000 : ℝ)
    (cell13100 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · have h := gap_lower (n := 13100) (a := (83514860058469 / 100000000000000 : ℝ)) (b := (78589683071 / 50000000000000 : ℝ)) (q := (2204755031167 / 100000000000000 : ℝ))
      (E := (cell13100 ⟨16, by decide⟩).energy) (xi := (323640126141257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13100 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13100]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13100])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13100) (a := (83514860058469 / 100000000000000 : ℝ)) (b := (78589683071 / 50000000000000 : ℝ)) (q := (2204755031167 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13100])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13100])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13100]

theorem cert13100_17 : CellCertificate 13100 (875843412266401 / 10000000000000000 : ℝ) (320675081395459 / 200000000000000000 : ℝ) (323640126141257 / 10000000000000000 : ℝ)
    (cell13100 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · have h := gap_lower (n := 13100) (a := (83480363992699 / 100000000000000 : ℝ)) (b := (78589683071 / 50000000000000 : ℝ)) (q := (1102379534171 / 50000000000000 : ℝ))
      (E := (cell13100 ⟨17, by decide⟩).energy) (xi := (323640126141257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13100 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13100]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13100])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13100) (a := (83480363992699 / 100000000000000 : ℝ)) (b := (78589683071 / 50000000000000 : ℝ)) (q := (1102379534171 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13100])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13100])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13100]

theorem cert13100_18 : CellCertificate 13100 (875843412266401 / 10000000000000000 : ℝ) (320675081395459 / 200000000000000000 : ℝ) (323640126141257 / 10000000000000000 : ℝ)
    (cell13100 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · have h := gap_lower (n := 13100) (a := (41722946091167 / 50000000000000 : ℝ)) (b := (78589683071 / 50000000000000 : ℝ)) (q := (68898844861 / 3125000000000 : ℝ))
      (E := (cell13100 ⟨18, by decide⟩).energy) (xi := (323640126141257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13100 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13100]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13100])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13100) (a := (41722946091167 / 50000000000000 : ℝ)) (b := (78589683071 / 50000000000000 : ℝ)) (q := (68898844861 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13100])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13100])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13100]

theorem cert13100_19 : CellCertificate 13100 (875843412266401 / 10000000000000000 : ℝ) (320675081395459 / 200000000000000000 : ℝ) (323640126141257 / 10000000000000000 : ℝ)
    (cell13100 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · have h := gap_lower (n := 13100) (a := (41705722297023 / 50000000000000 : ℝ)) (b := (78589683071 / 50000000000000 : ℝ)) (q := (88190682143 / 4000000000000 : ℝ))
      (E := (cell13100 ⟨19, by decide⟩).energy) (xi := (323640126141257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13100 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13100]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13100])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13100) (a := (41705722297023 / 50000000000000 : ℝ)) (b := (78589683071 / 50000000000000 : ℝ)) (q := (88190682143 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13100])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13100])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13100]

theorem cert13101_0 : CellCertificate 13101 (13684642033051 / 156250000000000 : ℝ) (320650596448507 / 200000000000000000 : ℝ) (323614855171903 / 10000000000000000 : ℝ)
    (cell13101 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · have h := gap_lower (n := 13101) (a := (84070109508483 / 100000000000000 : ℝ)) (b := (78583615413 / 50000000000000 : ℝ)) (q := (551144705831 / 25000000000000 : ℝ))
      (E := (cell13101 ⟨0, by decide⟩).energy) (xi := (323614855171903 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13101 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13101]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13101])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13101) (a := (84070109508483 / 100000000000000 : ℝ)) (b := (78583615413 / 50000000000000 : ℝ)) (q := (551144705831 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13101])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13101])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13101]

theorem cert13101_1 : CellCertificate 13101 (13684642033051 / 156250000000000 : ℝ) (320650596448507 / 200000000000000000 : ℝ) (323614855171903 / 10000000000000000 : ℝ)
    (cell13101 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · have h := gap_lower (n := 13101) (a := (21008805171311 / 25000000000000 : ℝ)) (b := (78583615413 / 50000000000000 : ℝ)) (q := (2204582841011 / 100000000000000 : ℝ))
      (E := (cell13101 ⟨1, by decide⟩).energy) (xi := (323614855171903 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13101 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13101]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13101])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13101) (a := (21008805171311 / 25000000000000 : ℝ)) (b := (78583615413 / 50000000000000 : ℝ)) (q := (2204582841011 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13101])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13101])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13101]

theorem cert13101_2 : CellCertificate 13101 (13684642033051 / 156250000000000 : ℝ) (320650596448507 / 200000000000000000 : ℝ) (323614855171903 / 10000000000000000 : ℝ)
    (cell13101 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · have h := gap_lower (n := 13101) (a := (84000356674957 / 100000000000000 : ℝ)) (b := (78583615413 / 50000000000000 : ℝ)) (q := (440917372091 / 20000000000000 : ℝ))
      (E := (cell13101 ⟨2, by decide⟩).energy) (xi := (323614855171903 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13101 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13101]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13101])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13101) (a := (84000356674957 / 100000000000000 : ℝ)) (b := (78583615413 / 50000000000000 : ℝ)) (q := (440917372091 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13101])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13101])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13101]

theorem cert13101_3 : CellCertificate 13101 (13684642033051 / 156250000000000 : ℝ) (320650596448507 / 200000000000000000 : ℝ) (323614855171903 / 10000000000000000 : ℝ)
    (cell13101 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · have h := gap_lower (n := 13101) (a := (41982758720693 / 50000000000000 : ℝ)) (b := (78583615413 / 50000000000000 : ℝ)) (q := (1102295445017 / 50000000000000 : ℝ))
      (E := (cell13101 ⟨3, by decide⟩).energy) (xi := (323614855171903 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13101 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13101]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13101])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13101) (a := (41982758720693 / 50000000000000 : ℝ)) (b := (78583615413 / 50000000000000 : ℝ)) (q := (1102295445017 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13101])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13101])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13101]

theorem cert13101_4 : CellCertificate 13101 (13684642033051 / 156250000000000 : ℝ) (320650596448507 / 200000000000000000 : ℝ) (323614855171903 / 10000000000000000 : ℝ)
    (cell13101 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · have h := gap_lower (n := 13101) (a := (8393070294849 / 10000000000000 : ℝ)) (b := (78583615413 / 50000000000000 : ℝ)) (q := (2204594879923 / 100000000000000 : ℝ))
      (E := (cell13101 ⟨4, by decide⟩).energy) (xi := (323614855171903 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13101 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13101]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13101])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13101) (a := (8393070294849 / 10000000000000 : ℝ)) (b := (78583615413 / 50000000000000 : ℝ)) (q := (2204594879923 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13101])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13101])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13101]

theorem cert13101_5 : CellCertificate 13101 (13684642033051 / 156250000000000 : ℝ) (320650596448507 / 200000000000000000 : ℝ) (323614855171903 / 10000000000000000 : ℝ)
    (cell13101 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · have h := gap_lower (n := 13101) (a := (2621747286263 / 3125000000000 : ℝ)) (b := (78583615413 / 50000000000000 : ℝ)) (q := (55114972397 / 2500000000000 : ℝ))
      (E := (cell13101 ⟨5, by decide⟩).energy) (xi := (323614855171903 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13101 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13101]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13101])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13101) (a := (2621747286263 / 3125000000000 : ℝ)) (b := (78583615413 / 50000000000000 : ℝ)) (q := (55114972397 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13101])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13101])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13101]

theorem cert13101_6 : CellCertificate 13101 (13684642033051 / 156250000000000 : ℝ) (320650596448507 / 200000000000000000 : ℝ) (323614855171903 / 10000000000000000 : ℝ)
    (cell13101 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · have h := gap_lower (n := 13101) (a := (83861148041497 / 100000000000000 : ℝ)) (b := (78583615413 / 50000000000000 : ℝ)) (q := (88184115501 / 4000000000000 : ℝ))
      (E := (cell13101 ⟨6, by decide⟩).energy) (xi := (323614855171903 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13101 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13101]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13101])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13101) (a := (83861148041497 / 100000000000000 : ℝ)) (b := (78583615413 / 50000000000000 : ℝ)) (q := (88184115501 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13101])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13101])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13101]

theorem cert13101_7 : CellCertificate 13101 (13684642033051 / 156250000000000 : ℝ) (320650596448507 / 200000000000000000 : ℝ) (323614855171903 / 10000000000000000 : ℝ)
    (cell13101 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · have h := gap_lower (n := 13101) (a := (83826407556257 / 100000000000000 : ℝ)) (b := (78583615413 / 50000000000000 : ℝ)) (q := (440921384031 / 20000000000000 : ℝ))
      (E := (cell13101 ⟨7, by decide⟩).energy) (xi := (323614855171903 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13101 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13101]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13101])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13101) (a := (83826407556257 / 100000000000000 : ℝ)) (b := (78583615413 / 50000000000000 : ℝ)) (q := (440921384031 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13101])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13101])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13101]

theorem cert13101_8 : CellCertificate 13101 (13684642033051 / 156250000000000 : ℝ) (320650596448507 / 200000000000000000 : ℝ) (323614855171903 / 10000000000000000 : ℝ)
    (cell13101 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · have h := gap_lower (n := 13101) (a := (83791691669401 / 100000000000000 : ℝ)) (b := (78583615413 / 50000000000000 : ℝ)) (q := (1102305471419 / 50000000000000 : ℝ))
      (E := (cell13101 ⟨8, by decide⟩).energy) (xi := (323614855171903 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13101 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13101]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13101])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13101) (a := (83791691669401 / 100000000000000 : ℝ)) (b := (78583615413 / 50000000000000 : ℝ)) (q := (1102305471419 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13101])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13101])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13101]

theorem cert13101_9 : CellCertificate 13101 (13684642033051 / 156250000000000 : ℝ) (320650596448507 / 200000000000000000 : ℝ) (323614855171903 / 10000000000000000 : ℝ)
    (cell13101 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · have h := gap_lower (n := 13101) (a := (41878500172911 / 50000000000000 : ℝ)) (b := (78583615413 / 50000000000000 : ℝ)) (q := (1102307481177 / 50000000000000 : ℝ))
      (E := (cell13101 ⟨9, by decide⟩).energy) (xi := (323614855171903 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13101 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13101]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13101])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13101) (a := (41878500172911 / 50000000000000 : ℝ)) (b := (78583615413 / 50000000000000 : ℝ)) (q := (1102307481177 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13101])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13101])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13101]

theorem cert13101_10 : CellCertificate 13101 (13684642033051 / 156250000000000 : ℝ) (320650596448507 / 200000000000000000 : ℝ) (323614855171903 / 10000000000000000 : ℝ)
    (cell13101 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · have h := gap_lower (n := 13101) (a := (83722333550593 / 100000000000000 : ℝ)) (b := (78583615413 / 50000000000000 : ℝ)) (q := (1102309463577 / 50000000000000 : ℝ))
      (E := (cell13101 ⟨10, by decide⟩).energy) (xi := (323614855171903 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13101 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13101]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13101])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13101) (a := (83722333550593 / 100000000000000 : ℝ)) (b := (78583615413 / 50000000000000 : ℝ)) (q := (1102309463577 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13101])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13101])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13101]

theorem cert13101_11 : CellCertificate 13101 (13684642033051 / 156250000000000 : ℝ) (320650596448507 / 200000000000000000 : ℝ) (323614855171903 / 10000000000000000 : ℝ)
    (cell13101 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · have h := gap_lower (n := 13101) (a := (20921922812243 / 25000000000000 : ℝ)) (b := (78583615413 / 50000000000000 : ℝ)) (q := (1102311479831 / 50000000000000 : ℝ))
      (E := (cell13101 ⟨11, by decide⟩).energy) (xi := (323614855171903 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13101 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13101]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13101])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13101) (a := (20921922812243 / 25000000000000 : ℝ)) (b := (78583615413 / 50000000000000 : ℝ)) (q := (1102311479831 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13101])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13101])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13101]

theorem cert13101_12 : CellCertificate 13101 (13684642033051 / 156250000000000 : ℝ) (320650596448507 / 200000000000000000 : ℝ) (323614855171903 / 10000000000000000 : ℝ)
    (cell13101 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · have h := gap_lower (n := 13101) (a := (20913268351599 / 25000000000000 : ℝ)) (b := (78583615413 / 50000000000000 : ℝ)) (q := (551156737431 / 25000000000000 : ℝ))
      (E := (cell13101 ⟨12, by decide⟩).energy) (xi := (323614855171903 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13101 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13101]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13101])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13101) (a := (20913268351599 / 25000000000000 : ℝ)) (b := (78583615413 / 50000000000000 : ℝ)) (q := (551156737431 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13101])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13101])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13101]

theorem cert13101_13 : CellCertificate 13101 (13684642033051 / 156250000000000 : ℝ) (320650596448507 / 200000000000000000 : ℝ) (323614855171903 / 10000000000000000 : ℝ)
    (cell13101 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · have h := gap_lower (n := 13101) (a := (83618479988481 / 100000000000000 : ℝ)) (b := (78583615413 / 50000000000000 : ℝ)) (q := (440926192243 / 20000000000000 : ℝ))
      (E := (cell13101 ⟨13, by decide⟩).energy) (xi := (323614855171903 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13101 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13101]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13101])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13101) (a := (83618479988481 / 100000000000000 : ℝ)) (b := (78583615413 / 50000000000000 : ℝ)) (q := (440926192243 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13101])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13101])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13101]

theorem cert13101_14 : CellCertificate 13101 (13684642033051 / 156250000000000 : ℝ) (320650596448507 / 200000000000000000 : ℝ) (323614855171903 / 10000000000000000 : ℝ)
    (cell13101 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · have h := gap_lower (n := 13101) (a := (83583910961023 / 100000000000000 : ℝ)) (b := (78583615413 / 50000000000000 : ℝ)) (q := (551158749919 / 25000000000000 : ℝ))
      (E := (cell13101 ⟨14, by decide⟩).energy) (xi := (323614855171903 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13101 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13101]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13101])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13101) (a := (83583910961023 / 100000000000000 : ℝ)) (b := (78583615413 / 50000000000000 : ℝ)) (q := (551158749919 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13101])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13101])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13101]

theorem cert13101_15 : CellCertificate 13101 (13684642033051 / 156250000000000 : ℝ) (320650596448507 / 200000000000000000 : ℝ) (323614855171903 / 10000000000000000 : ℝ)
    (cell13101 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · have h := gap_lower (n := 13101) (a := (41774683144997 / 50000000000000 : ℝ)) (b := (78583615413 / 50000000000000 : ℝ)) (q := (2204639012209 / 100000000000000 : ℝ))
      (E := (cell13101 ⟨15, by decide⟩).energy) (xi := (323614855171903 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13101 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13101]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13101])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13101) (a := (41774683144997 / 50000000000000 : ℝ)) (b := (78583615413 / 50000000000000 : ℝ)) (q := (2204639012209 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13101])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13101])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13101]

theorem cert13101_16 : CellCertificate 13101 (13684642033051 / 156250000000000 : ℝ) (320650596448507 / 200000000000000000 : ℝ) (323614855171903 / 10000000000000000 : ℝ)
    (cell13101 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · have h := gap_lower (n := 13101) (a := (10439355742693 / 12500000000000 : ℝ)) (b := (78583615413 / 50000000000000 : ℝ)) (q := (2204643003799 / 100000000000000 : ℝ))
      (E := (cell13101 ⟨16, by decide⟩).energy) (xi := (323614855171903 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13101 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13101]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13101])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13101) (a := (10439355742693 / 12500000000000 : ℝ)) (b := (78583615413 / 50000000000000 : ℝ)) (q := (2204643003799 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13101])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13101])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13101]

theorem cert13101_17 : CellCertificate 13101 (13684642033051 / 156250000000000 : ℝ) (320650596448507 / 200000000000000000 : ℝ) (323614855171903 / 10000000000000000 : ℝ)
    (cell13101 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · have h := gap_lower (n := 13101) (a := (20870087470499 / 25000000000000 : ℝ)) (b := (78583615413 / 50000000000000 : ℝ)) (q := (551161759359 / 25000000000000 : ℝ))
      (E := (cell13101 ⟨17, by decide⟩).energy) (xi := (323614855171903 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13101 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13101]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13101])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13101) (a := (20870087470499 / 25000000000000 : ℝ)) (b := (78583615413 / 50000000000000 : ℝ)) (q := (551161759359 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13101])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13101])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13101]

theorem cert13101_18 : CellCertificate 13101 (13684642033051 / 156250000000000 : ℝ) (320650596448507 / 200000000000000000 : ℝ) (323614855171903 / 10000000000000000 : ℝ)
    (cell13101 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · have h := gap_lower (n := 13101) (a := (10430734759731 / 12500000000000 : ℝ)) (b := (78583615413 / 50000000000000 : ℝ)) (q := (88186042377 / 4000000000000 : ℝ))
      (E := (cell13101 ⟨18, by decide⟩).energy) (xi := (323614855171903 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13101 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13101]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13101])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13101) (a := (10430734759731 / 12500000000000 : ℝ)) (b := (78583615413 / 50000000000000 : ℝ)) (q := (88186042377 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13101])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13101])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13101]

theorem cert13101_19 : CellCertificate 13101 (13684642033051 / 156250000000000 : ℝ) (320650596448507 / 200000000000000000 : ℝ) (323614855171903 / 10000000000000000 : ℝ)
    (cell13101 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · have h := gap_lower (n := 13101) (a := (20852857623943 / 25000000000000 : ℝ)) (b := (78583615413 / 50000000000000 : ℝ)) (q := (2204655074027 / 100000000000000 : ℝ))
      (E := (cell13101 ⟨19, by decide⟩).energy) (xi := (323614855171903 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13101 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13101]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13101])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13101) (a := (20852857623943 / 25000000000000 : ℝ)) (b := (78583615413 / 50000000000000 : ℝ)) (q := (2204655074027 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13101])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13101])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13101]

theorem cert13102_0 : CellCertificate 13102 (875790771810311 / 10000000000000000 : ℝ) (400782644050419 / 250000000000000000 : ℝ) (16179479408871 / 500000000000000 : ℝ)
    (cell13102 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · have h := gap_lower (n := 13102) (a := (84070095293419 / 100000000000000 : ℝ)) (b := (157155097391 / 100000000000000 : ℝ)) (q := (1102233427327 / 50000000000000 : ℝ))
      (E := (cell13102 ⟨0, by decide⟩).energy) (xi := (16179479408871 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13102 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13102]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13102])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13102) (a := (84070095293419 / 100000000000000 : ℝ)) (b := (157155097391 / 100000000000000 : ℝ)) (q := (1102233427327 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13102])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13102])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13102]

theorem cert13102_1 : CellCertificate 13102 (875790771810311 / 10000000000000000 : ℝ) (400782644050419 / 250000000000000000 : ℝ) (16179479408871 / 500000000000000 : ℝ)
    (cell13102 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · have h := gap_lower (n := 13102) (a := (84035206476491 / 100000000000000 : ℝ)) (b := (157155097391 / 100000000000000 : ℝ)) (q := (1102235434027 / 50000000000000 : ℝ))
      (E := (cell13102 ⟨1, by decide⟩).energy) (xi := (16179479408871 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13102 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13102]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13102])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13102) (a := (84035206476491 / 100000000000000 : ℝ)) (b := (157155097391 / 100000000000000 : ℝ)) (q := (1102235434027 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13102])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13102])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13102]

theorem cert13102_2 : CellCertificate 13102 (875790771810311 / 10000000000000000 : ℝ) (400782644050419 / 250000000000000000 : ℝ) (16179479408871 / 500000000000000 : ℝ)
    (cell13102 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · have h := gap_lower (n := 13102) (a := (21000085618127 / 25000000000000 : ℝ)) (b := (157155097391 / 100000000000000 : ℝ)) (q := (1102237441629 / 50000000000000 : ℝ))
      (E := (cell13102 ⟨2, by decide⟩).energy) (xi := (16179479408871 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13102 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13102]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13102])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13102) (a := (21000085618127 / 25000000000000 : ℝ)) (b := (157155097391 / 100000000000000 : ℝ)) (q := (1102237441629 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13102])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13102])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13102]

theorem cert13102_3 : CellCertificate 13102 (875790771810311 / 10000000000000000 : ℝ) (400782644050419 / 250000000000000000 : ℝ) (16179479408871 / 500000000000000 : ℝ)
    (cell13102 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · have h := gap_lower (n := 13102) (a := (83965503245237 / 100000000000000 : ℝ)) (b := (157155097391 / 100000000000000 : ℝ)) (q := (551119727161 / 25000000000000 : ℝ))
      (E := (cell13102 ⟨3, by decide⟩).energy) (xi := (16179479408871 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13102 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13102]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13102])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13102) (a := (83965503245237 / 100000000000000 : ℝ)) (b := (157155097391 / 100000000000000 : ℝ)) (q := (551119727161 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13102])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13102])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13102]

theorem cert13102_4 : CellCertificate 13102 (875790771810311 / 10000000000000000 : ℝ) (400782644050419 / 250000000000000000 : ℝ) (16179479408871 / 500000000000000 : ℝ)
    (cell13102 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · have h := gap_lower (n := 13102) (a := (16786137751727 / 20000000000000 : ℝ)) (b := (157155097391 / 100000000000000 : ℝ)) (q := (1102241447193 / 50000000000000 : ℝ))
      (E := (cell13102 ⟨4, by decide⟩).energy) (xi := (16179479408871 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13102 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13102]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13102])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13102) (a := (16786137751727 / 20000000000000 : ℝ)) (b := (157155097391 / 100000000000000 : ℝ)) (q := (1102241447193 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13102])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13102])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13102]

theorem cert13102_5 : CellCertificate 13102 (875790771810311 / 10000000000000000 : ℝ) (400782644050419 / 250000000000000000 : ℝ) (16179479408871 / 500000000000000 : ℝ)
    (cell13102 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · have h := gap_lower (n := 13102) (a := (5243493686053 / 6250000000000 : ℝ)) (b := (157155097391 / 100000000000000 : ℝ)) (q := (440897381249 / 20000000000000 : ℝ))
      (E := (cell13102 ⟨5, by decide⟩).energy) (xi := (16179479408871 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13102 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13102]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13102])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13102) (a := (5243493686053 / 6250000000000 : ℝ)) (b := (157155097391 / 100000000000000 : ℝ)) (q := (440897381249 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13102])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13102])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13102]

theorem cert13102_6 : CellCertificate 13102 (875790771810311 / 10000000000000000 : ℝ) (400782644050419 / 250000000000000000 : ℝ) (16179479408871 / 500000000000000 : ℝ)
    (cell13102 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · have h := gap_lower (n := 13102) (a := (20965283466053 / 25000000000000 : ℝ)) (b := (157155097391 / 100000000000000 : ℝ)) (q := (1102245446919 / 50000000000000 : ℝ))
      (E := (cell13102 ⟨6, by decide⟩).energy) (xi := (16179479408871 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13102 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13102]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13102])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13102) (a := (20965283466053 / 25000000000000 : ℝ)) (b := (157155097391 / 100000000000000 : ℝ)) (q := (1102245446919 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13102])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13102])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13102]

theorem cert13102_7 : CellCertificate 13102 (875790771810311 / 10000000000000000 : ℝ) (400782644050419 / 250000000000000000 : ℝ) (16179479408871 / 500000000000000 : ℝ)
    (cell13102 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · have h := gap_lower (n := 13102) (a := (2619574793289 / 3125000000000 : ℝ)) (b := (157155097391 / 100000000000000 : ℝ)) (q := (68890466327 / 3125000000000 : ℝ))
      (E := (cell13102 ⟨7, by decide⟩).energy) (xi := (16179479408871 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13102 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13102]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13102])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13102) (a := (2619574793289 / 3125000000000 : ℝ)) (b := (157155097391 / 100000000000000 : ℝ)) (q := (68890466327 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13102])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13102])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13102]

theorem cert13102_8 : CellCertificate 13102 (875790771810311 / 10000000000000000 : ℝ) (400782644050419 / 250000000000000000 : ℝ) (16179479408871 / 500000000000000 : ℝ)
    (cell13102 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · have h := gap_lower (n := 13102) (a := (10473959688083 / 12500000000000 : ℝ)) (b := (157155097391 / 100000000000000 : ℝ)) (q := (551124735297 / 25000000000000 : ℝ))
      (E := (cell13102 ⟨8, by decide⟩).energy) (xi := (16179479408871 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13102 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13102]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13102])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13102) (a := (10473959688083 / 12500000000000 : ℝ)) (b := (157155097391 / 100000000000000 : ℝ)) (q := (551124735297 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13102])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13102])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13102]

theorem cert13102_9 : CellCertificate 13102 (875790771810311 / 10000000000000000 : ℝ) (400782644050419 / 250000000000000000 : ℝ) (16179479408871 / 500000000000000 : ℝ)
    (cell13102 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · have h := gap_lower (n := 13102) (a := (1675139723747 / 2000000000000 : ℝ)) (b := (157155097391 / 100000000000000 : ℝ)) (q := (2204502956793 / 100000000000000 : ℝ))
      (E := (cell13102 ⟨9, by decide⟩).energy) (xi := (16179479408871 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13102 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13102]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13102])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13102) (a := (1675139723747 / 2000000000000 : ℝ)) (b := (157155097391 / 100000000000000 : ℝ)) (q := (2204502956793 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13102])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13102])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13102]

theorem cert13102_10 : CellCertificate 13102 (875790771810311 / 10000000000000000 : ℝ) (400782644050419 / 250000000000000000 : ℝ) (16179479408871 / 500000000000000 : ℝ)
    (cell13102 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · have h := gap_lower (n := 13102) (a := (83722319398381 / 100000000000000 : ℝ)) (b := (157155097391 / 100000000000000 : ℝ)) (q := (2204506975811 / 100000000000000 : ℝ))
      (E := (cell13102 ⟨10, by decide⟩).energy) (xi := (16179479408871 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13102 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13102]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13102])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13102) (a := (83722319398381 / 100000000000000 : ℝ)) (b := (157155097391 / 100000000000000 : ℝ)) (q := (2204506975811 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13102])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13102])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13102]

theorem cert13102_11 : CellCertificate 13102 (875790771810311 / 10000000000000000 : ℝ) (400782644050419 / 250000000000000000 : ℝ) (16179479408871 / 500000000000000 : ℝ)
    (cell13102 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · have h := gap_lower (n := 13102) (a := (16737535420603 / 20000000000000 : ℝ)) (b := (157155097391 / 100000000000000 : ℝ)) (q := (1102255473209 / 50000000000000 : ℝ))
      (E := (cell13102 ⟨11, by decide⟩).energy) (xi := (16179479408871 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13102 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13102]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13102])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13102) (a := (16737535420603 / 20000000000000 : ℝ)) (b := (157155097391 / 100000000000000 : ℝ)) (q := (1102255473209 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13102])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13102])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13102]

theorem cert13102_12 : CellCertificate 13102 (875790771810311 / 10000000000000000 : ℝ) (400782644050419 / 250000000000000000 : ℝ) (16179479408871 / 500000000000000 : ℝ)
    (cell13102 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · have h := gap_lower (n := 13102) (a := (83653059266687 / 100000000000000 : ℝ)) (b := (157155097391 / 100000000000000 : ℝ)) (q := (2204514990841 / 100000000000000 : ℝ))
      (E := (cell13102 ⟨12, by decide⟩).energy) (xi := (16179479408871 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13102 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13102]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13102])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13102) (a := (83653059266687 / 100000000000000 : ℝ)) (b := (157155097391 / 100000000000000 : ℝ)) (q := (2204514990841 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13102])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13102])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13102]

theorem cert13102_13 : CellCertificate 13102 (875790771810311 / 10000000000000000 : ℝ) (400782644050419 / 250000000000000000 : ℝ) (16179479408871 / 500000000000000 : ℝ)
    (cell13102 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · have h := gap_lower (n := 13102) (a := (16723693171003 / 20000000000000 : ℝ)) (b := (157155097391 / 100000000000000 : ℝ)) (q := (2204518998631 / 100000000000000 : ℝ))
      (E := (cell13102 ⟨13, by decide⟩).energy) (xi := (16179479408871 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13102 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13102]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13102])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13102) (a := (16723693171003 / 20000000000000 : ℝ)) (b := (157155097391 / 100000000000000 : ℝ)) (q := (2204518998631 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13102])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13102])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13102]

theorem cert13102_14 : CellCertificate 13102 (875790771810311 / 10000000000000000 : ℝ) (400782644050419 / 250000000000000000 : ℝ) (16179479408871 / 500000000000000 : ℝ)
    (cell13102 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · have h := gap_lower (n := 13102) (a := (16716779366759 / 20000000000000 : ℝ)) (b := (157155097391 / 100000000000000 : ℝ)) (q := (1102261487631 / 50000000000000 : ℝ))
      (E := (cell13102 ⟨14, by decide⟩).energy) (xi := (16179479408871 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13102 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13102]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13102])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13102) (a := (16716779366759 / 20000000000000 : ℝ)) (b := (157155097391 / 100000000000000 : ℝ)) (q := (1102261487631 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13102])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13102])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13102]

theorem cert13102_15 : CellCertificate 13102 (875790771810311 / 10000000000000000 : ℝ) (400782644050419 / 250000000000000000 : ℝ) (16179479408871 / 500000000000000 : ℝ)
    (cell13102 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · have h := gap_lower (n := 13102) (a := (83549352168999 / 100000000000000 : ℝ)) (b := (157155097391 / 100000000000000 : ℝ)) (q := (551131746041 / 25000000000000 : ℝ))
      (E := (cell13102 ⟨15, by decide⟩).energy) (xi := (16179479408871 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13102 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13102]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13102])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13102) (a := (83549352168999 / 100000000000000 : ℝ)) (b := (157155097391 / 100000000000000 : ℝ)) (q := (551131746041 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13102])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13102])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13102]

theorem cert13102_16 : CellCertificate 13102 (875790771810311 / 10000000000000000 : ℝ) (400782644050419 / 250000000000000000 : ℝ) (16179479408871 / 500000000000000 : ℝ)
    (cell13102 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · have h := gap_lower (n := 13102) (a := (10439353978347 / 12500000000000 : ℝ)) (b := (157155097391 / 100000000000000 : ℝ)) (q := (2204531030393 / 100000000000000 : ℝ))
      (E := (cell13102 ⟨16, by decide⟩).energy) (xi := (16179479408871 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13102 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13102]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13102])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13102) (a := (10439353978347 / 12500000000000 : ℝ)) (b := (157155097391 / 100000000000000 : ℝ)) (q := (2204531030393 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13102])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13102])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13102]

theorem cert13102_17 : CellCertificate 13102 (875790771810311 / 10000000000000000 : ℝ) (400782644050419 / 250000000000000000 : ℝ) (16179479408871 / 500000000000000 : ℝ)
    (cell13102 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · have h := gap_lower (n := 13102) (a := (1669606715469 / 2000000000000 : ℝ)) (b := (157155097391 / 100000000000000 : ℝ)) (q := (2204535060517 / 100000000000000 : ℝ))
      (E := (cell13102 ⟨17, by decide⟩).energy) (xi := (16179479408871 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13102 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13102]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13102])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13102) (a := (1669606715469 / 2000000000000 : ℝ)) (b := (157155097391 / 100000000000000 : ℝ)) (q := (2204535060517 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13102])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13102])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13102]

theorem cert13102_18 : CellCertificate 13102 (875790771810311 / 10000000000000000 : ℝ) (400782644050419 / 250000000000000000 : ℝ) (16179479408871 / 500000000000000 : ℝ)
    (cell13102 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · have h := gap_lower (n := 13102) (a := (41722931987759 / 50000000000000 : ℝ)) (b := (157155097391 / 100000000000000 : ℝ)) (q := (2204539020769 / 100000000000000 : ℝ))
      (E := (cell13102 ⟨18, by decide⟩).energy) (xi := (16179479408871 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13102 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13102]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13102])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13102) (a := (41722931987759 / 50000000000000 : ℝ)) (b := (157155097391 / 100000000000000 : ℝ)) (q := (2204539020769 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13102])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13102])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13102]

theorem cert13102_19 : CellCertificate 13102 (875790771810311 / 10000000000000000 : ℝ) (400782644050419 / 250000000000000000 : ℝ) (16179479408871 / 500000000000000 : ℝ)
    (cell13102 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · have h := gap_lower (n := 13102) (a := (20852854099913 / 25000000000000 : ℝ)) (b := (157155097391 / 100000000000000 : ℝ)) (q := (275567878991 / 12500000000000 : ℝ))
      (E := (cell13102 ⟨19, by decide⟩).energy) (xi := (16179479408871 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13102 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13102]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13102])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13102) (a := (20852854099913 / 25000000000000 : ℝ)) (b := (157155097391 / 100000000000000 : ℝ)) (q := (275567878991 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13102])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13102])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13102]

theorem cert13103_0 : CellCertificate 13103 (437882228675329 / 5000000000000000 : ℝ) (400752047212609 / 250000000000000000 : ℝ) (323564325156819 / 10000000000000000 : ℝ)
    (cell13103 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · have h := gap_lower (n := 13103) (a := (84070081080527 / 100000000000000 : ℝ)) (b := (39285741459 / 25000000000000 : ℝ)) (q := (2204354881711 / 100000000000000 : ℝ))
      (E := (cell13103 ⟨0, by decide⟩).energy) (xi := (323564325156819 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13103 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13103]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13103])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13103) (a := (84070081080527 / 100000000000000 : ℝ)) (b := (39285741459 / 25000000000000 : ℝ)) (q := (2204354881711 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13103])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13103])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13103]

theorem cert13103_1 : CellCertificate 13103 (437882228675329 / 5000000000000000 : ℝ) (400752047212609 / 250000000000000000 : ℝ) (323564325156819 / 10000000000000000 : ℝ)
    (cell13103 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · have h := gap_lower (n := 13103) (a := (8403519226991 / 10000000000000 : ℝ)) (b := (39285741459 / 25000000000000 : ℝ)) (q := (2204358890823 / 100000000000000 : ℝ))
      (E := (cell13103 ⟨1, by decide⟩).energy) (xi := (323564325156819 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13103 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13103]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13103])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13103) (a := (8403519226991 / 10000000000000 : ℝ)) (b := (39285741459 / 25000000000000 : ℝ)) (q := (2204358890823 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13103])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13103])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13103]

theorem cert13103_2 : CellCertificate 13103 (437882228675329 / 5000000000000000 : ℝ) (400752047212609 / 250000000000000000 : ℝ) (323564325156819 / 10000000000000000 : ℝ)
    (cell13103 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · have h := gap_lower (n := 13103) (a := (84000328272231 / 100000000000000 : ℝ)) (b := (39285741459 / 25000000000000 : ℝ)) (q := (2204362901789 / 100000000000000 : ℝ))
      (E := (cell13103 ⟨2, by decide⟩).energy) (xi := (323564325156819 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13103 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13103]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13103])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13103) (a := (84000328272231 / 100000000000000 : ℝ)) (b := (39285741459 / 25000000000000 : ℝ)) (q := (2204362901789 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13103])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13103])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13103]

theorem cert13103_3 : CellCertificate 13103 (437882228675329 / 5000000000000000 : ℝ) (400752047212609 / 250000000000000000 : ℝ) (323564325156819 / 10000000000000000 : ℝ)
    (cell13103 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · have h := gap_lower (n := 13103) (a := (41982744525629 / 50000000000000 : ℝ)) (b := (39285741459 / 25000000000000 : ℝ)) (q := (1102183461491 / 50000000000000 : ℝ))
      (E := (cell13103 ⟨3, by decide⟩).energy) (xi := (323564325156819 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13103 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13103]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13103])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13103) (a := (41982744525629 / 50000000000000 : ℝ)) (b := (39285741459 / 25000000000000 : ℝ)) (q := (1102183461491 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13103])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13103])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13103]

theorem cert13103_4 : CellCertificate 13103 (437882228675329 / 5000000000000000 : ℝ) (400752047212609 / 250000000000000000 : ℝ) (323564325156819 / 10000000000000000 : ℝ)
    (cell13103 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · have h := gap_lower (n := 13103) (a := (20982668642737 / 25000000000000 : ℝ)) (b := (39285741459 / 25000000000000 : ℝ)) (q := (110218545229 / 5000000000000 : ℝ))
      (E := (cell13103 ⟨4, by decide⟩).energy) (xi := (323564325156819 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13103 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13103]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13103])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13103) (a := (20982668642737 / 25000000000000 : ℝ)) (b := (39285741459 / 25000000000000 : ℝ)) (q := (110218545229 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13103])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13103])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13103]

theorem cert13103_5 : CellCertificate 13103 (437882228675329 / 5000000000000000 : ℝ) (400752047212609 / 250000000000000000 : ℝ) (323564325156819 / 10000000000000000 : ℝ)
    (cell13103 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · have h := gap_lower (n := 13103) (a := (10486985599431 / 12500000000000 : ℝ)) (b := (39285741459 / 25000000000000 : ℝ)) (q := (2204374912341 / 100000000000000 : ℝ))
      (E := (cell13103 ⟨5, by decide⟩).energy) (xi := (323564325156819 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13103 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13103]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13103])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13103) (a := (10486985599431 / 12500000000000 : ℝ)) (b := (39285741459 / 25000000000000 : ℝ)) (q := (2204374912341 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13103])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13103])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13103]

theorem cert13103_6 : CellCertificate 13103 (437882228675329 / 5000000000000000 : ℝ) (400752047212609 / 250000000000000000 : ℝ) (323564325156819 / 10000000000000000 : ℝ)
    (cell13103 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · have h := gap_lower (n := 13103) (a := (41930559844547 / 50000000000000 : ℝ)) (b := (39285741459 / 25000000000000 : ℝ)) (q := (137773684617 / 6250000000000 : ℝ))
      (E := (cell13103 ⟨6, by decide⟩).energy) (xi := (323564325156819 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13103 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13103]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13103])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13103) (a := (41930559844547 / 50000000000000 : ℝ)) (b := (39285741459 / 25000000000000 : ℝ)) (q := (137773684617 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13103])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13103])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13103]

theorem cert13103_7 : CellCertificate 13103 (437882228675329 / 5000000000000000 : ℝ) (400752047212609 / 250000000000000000 : ℝ) (323564325156819 / 10000000000000000 : ℝ)
    (cell13103 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · have h := gap_lower (n := 13103) (a := (16765275843281 / 20000000000000 : ℝ)) (b := (39285741459 / 25000000000000 : ℝ)) (q := (440876584101 / 20000000000000 : ℝ))
      (E := (cell13103 ⟨7, by decide⟩).energy) (xi := (323564325156819 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13103 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13103]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13103])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13103) (a := (16765275843281 / 20000000000000 : ℝ)) (b := (39285741459 / 25000000000000 : ℝ)) (q := (440876584101 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13103])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13103])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13103]

theorem cert13103_8 : CellCertificate 13103 (437882228675329 / 5000000000000000 : ℝ) (400752047212609 / 250000000000000000 : ℝ) (323564325156819 / 10000000000000000 : ℝ)
    (cell13103 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · have h := gap_lower (n := 13103) (a := (83791663342091 / 100000000000000 : ℝ)) (b := (39285741459 / 25000000000000 : ℝ)) (q := (275548366909 / 12500000000000 : ℝ))
      (E := (cell13103 ⟨8, by decide⟩).energy) (xi := (323564325156819 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13103 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13103]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13103])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13103) (a := (83791663342091 / 100000000000000 : ℝ)) (b := (39285741459 / 25000000000000 : ℝ)) (q := (275548366909 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13103])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13103])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13103]

theorem cert13103_9 : CellCertificate 13103 (437882228675329 / 5000000000000000 : ℝ) (400752047212609 / 250000000000000000 : ℝ) (323564325156819 / 10000000000000000 : ℝ)
    (cell13103 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · have h := gap_lower (n := 13103) (a := (41878486015521 / 50000000000000 : ℝ)) (b := (39285741459 / 25000000000000 : ℝ)) (q := (1102195473483 / 50000000000000 : ℝ))
      (E := (cell13103 ⟨9, by decide⟩).energy) (xi := (323564325156819 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13103 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13103]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13103])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13103) (a := (41878486015521 / 50000000000000 : ℝ)) (b := (39285741459 / 25000000000000 : ℝ)) (q := (1102195473483 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13103])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13103])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13103]

theorem cert13103_10 : CellCertificate 13103 (437882228675329 / 5000000000000000 : ℝ) (400752047212609 / 250000000000000000 : ℝ) (323564325156819 / 10000000000000000 : ℝ)
    (cell13103 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · have h := gap_lower (n := 13103) (a := (20930576312083 / 25000000000000 : ℝ)) (b := (39285741459 / 25000000000000 : ℝ)) (q := (2204394962121 / 100000000000000 : ℝ))
      (E := (cell13103 ⟨10, by decide⟩).energy) (xi := (323564325156819 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13103 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13103]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13103])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13103) (a := (20930576312083 / 25000000000000 : ℝ)) (b := (39285741459 / 25000000000000 : ℝ)) (q := (2204394962121 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13103])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13103])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13103]

theorem cert13103_11 : CellCertificate 13103 (437882228675329 / 5000000000000000 : ℝ) (400752047212609 / 250000000000000000 : ℝ) (323564325156819 / 10000000000000000 : ℝ)
    (cell13103 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · have h := gap_lower (n := 13103) (a := (83687662959219 / 100000000000000 : ℝ)) (b := (39285741459 / 25000000000000 : ℝ)) (q := (1102199493509 / 50000000000000 : ℝ))
      (E := (cell13103 ⟨11, by decide⟩).energy) (xi := (323564325156819 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13103 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13103]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13103])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13103) (a := (83687662959219 / 100000000000000 : ℝ)) (b := (39285741459 / 25000000000000 : ℝ)) (q := (1102199493509 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13103])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13103])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13103]

theorem cert13103_12 : CellCertificate 13103 (437882228675329 / 5000000000000000 : ℝ) (400752047212609 / 250000000000000000 : ℝ) (323564325156819 / 10000000000000000 : ℝ)
    (cell13103 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · have h := gap_lower (n := 13103) (a := (83653045129139 / 100000000000000 : ℝ)) (b := (39285741459 / 25000000000000 : ℝ)) (q := (551100742391 / 25000000000000 : ℝ))
      (E := (cell13103 ⟨12, by decide⟩).energy) (xi := (323564325156819 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13103 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13103]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13103])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13103) (a := (83653045129139 / 100000000000000 : ℝ)) (b := (39285741459 / 25000000000000 : ℝ)) (q := (551100742391 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13103])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13103])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13103]

theorem cert13103_13 : CellCertificate 13103 (437882228675329 / 5000000000000000 : ℝ) (400752047212609 / 250000000000000000 : ℝ) (323564325156819 / 10000000000000000 : ℝ)
    (cell13103 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · have h := gap_lower (n := 13103) (a := (8361845172371 / 10000000000000 : ℝ)) (b := (39285741459 / 25000000000000 : ℝ)) (q := (275550878973 / 12500000000000 : ℝ))
      (E := (cell13103 ⟨13, by decide⟩).energy) (xi := (323564325156819 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13103 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13103]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13103])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13103) (a := (8361845172371 / 10000000000000 : ℝ)) (b := (39285741459 / 25000000000000 : ℝ)) (q := (275550878973 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13103])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13103])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13103]

theorem cert13103_14 : CellCertificate 13103 (437882228675329 / 5000000000000000 : ℝ) (400752047212609 / 250000000000000000 : ℝ) (323564325156819 / 10000000000000000 : ℝ)
    (cell13103 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · have h := gap_lower (n := 13103) (a := (83583882708727 / 100000000000000 : ℝ)) (b := (39285741459 / 25000000000000 : ℝ)) (q := (1102205502381 / 50000000000000 : ℝ))
      (E := (cell13103 ⟨14, by decide⟩).energy) (xi := (323564325156819 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13103 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13103]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13103])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13103) (a := (83583882708727 / 100000000000000 : ℝ)) (b := (39285741459 / 25000000000000 : ℝ)) (q := (1102205502381 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13103])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13103])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13103]

theorem cert13103_15 : CellCertificate 13103 (437882228675329 / 5000000000000000 : ℝ) (400752047212609 / 250000000000000000 : ℝ) (323564325156819 / 10000000000000000 : ℝ)
    (cell13103 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · have h := gap_lower (n := 13103) (a := (41774669025081 / 50000000000000 : ℝ)) (b := (39285741459 / 25000000000000 : ℝ)) (q := (2204415010059 / 100000000000000 : ℝ))
      (E := (cell13103 ⟨15, by decide⟩).energy) (xi := (323564325156819 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13103 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13103]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13103])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13103) (a := (41774669025081 / 50000000000000 : ℝ)) (b := (39285741459 / 25000000000000 : ℝ)) (q := (2204415010059 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13103])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13103])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13103]

theorem cert13103_16 : CellCertificate 13103 (437882228675329 / 5000000000000000 : ℝ) (400752047212609 / 250000000000000000 : ℝ) (323564325156819 / 10000000000000000 : ℝ)
    (cell13103 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · have h := gap_lower (n := 13103) (a := (16702963542833 / 20000000000000 : ℝ)) (b := (39285741459 / 25000000000000 : ℝ)) (q := (275552381591 / 12500000000000 : ℝ))
      (E := (cell13103 ⟨16, by decide⟩).energy) (xi := (323564325156819 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13103 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13103]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13103])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13103) (a := (16702963542833 / 20000000000000 : ℝ)) (b := (39285741459 / 25000000000000 : ℝ)) (q := (275552381591 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13103])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13103])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13103]

theorem cert13103_17 : CellCertificate 13103 (437882228675329 / 5000000000000000 : ℝ) (400752047212609 / 250000000000000000 : ℝ) (323564325156819 / 10000000000000000 : ℝ)
    (cell13103 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · have h := gap_lower (n := 13103) (a := (83480321667059 / 100000000000000 : ℝ)) (b := (39285741459 / 25000000000000 : ℝ)) (q := (110221153967 / 5000000000000 : ℝ))
      (E := (cell13103 ⟨17, by decide⟩).energy) (xi := (323564325156819 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13103 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13103]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13103])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13103) (a := (83480321667059 / 100000000000000 : ℝ)) (b := (39285741459 / 25000000000000 : ℝ)) (q := (110221153967 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13103])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13103])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13103]

theorem cert13103_18 : CellCertificate 13103 (437882228675329 / 5000000000000000 : ℝ) (400752047212609 / 250000000000000000 : ℝ) (323564325156819 / 10000000000000000 : ℝ)
    (cell13103 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · have h := gap_lower (n := 13103) (a := (83445849875343 / 100000000000000 : ℝ)) (b := (39285741459 / 25000000000000 : ℝ)) (q := (440885418879 / 20000000000000 : ℝ))
      (E := (cell13103 ⟨18, by decide⟩).energy) (xi := (323564325156819 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13103 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13103]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13103])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13103) (a := (83445849875343 / 100000000000000 : ℝ)) (b := (39285741459 / 25000000000000 : ℝ)) (q := (440885418879 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13103])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13103])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13103]

theorem cert13103_19 : CellCertificate 13103 (437882228675329 / 5000000000000000 : ℝ) (400752047212609 / 250000000000000000 : ℝ) (323564325156819 / 10000000000000000 : ℝ)
    (cell13103 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · have h := gap_lower (n := 13103) (a := (83411402305687 / 100000000000000 : ℝ)) (b := (39285741459 / 25000000000000 : ℝ)) (q := (2204431102157 / 100000000000000 : ℝ))
      (E := (cell13103 ⟨19, by decide⟩).energy) (xi := (323564325156819 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13103 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13103]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13103])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13103) (a := (83411402305687 / 100000000000000 : ℝ)) (b := (39285741459 / 25000000000000 : ℝ)) (q := (2204431102157 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13103])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13103])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13103]

theorem cert13104_0 : CellCertificate 13104 (43786907336771 / 500000000000000 : ℝ) (320577164036907 / 200000000000000000 : ℝ) (323539066109107 / 10000000000000000 : ℝ)
    (cell13104 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · have h := gap_lower (n := 13104) (a := (5254379179363 / 6250000000000 : ℝ)) (b := (157130836161 / 100000000000000 : ℝ)) (q := (1102121452247 / 50000000000000 : ℝ))
      (E := (cell13104 ⟨0, by decide⟩).energy) (xi := (323539066109107 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13104 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13104]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13104])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13104) (a := (5254379179363 / 6250000000000 : ℝ)) (b := (157130836161 / 100000000000000 : ℝ)) (q := (1102121452247 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13104])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13104])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13104]

theorem cert13104_1 : CellCertificate 13104 (43786907336771 / 500000000000000 : ℝ) (320577164036907 / 200000000000000000 : ℝ) (323539066109107 / 10000000000000000 : ℝ)
    (cell13104 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · have h := gap_lower (n := 13104) (a := (84035178065499 / 100000000000000 : ℝ)) (b := (157130836161 / 100000000000000 : ℝ)) (q := (2204246909321 / 100000000000000 : ℝ))
      (E := (cell13104 ⟨1, by decide⟩).energy) (xi := (323539066109107 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13104 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13104]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13104])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13104) (a := (84035178065499 / 100000000000000 : ℝ)) (b := (157130836161 / 100000000000000 : ℝ)) (q := (2204246909321 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13104])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13104])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13104]

theorem cert13104_2 : CellCertificate 13104 (43786907336771 / 500000000000000 : ℝ) (320577164036907 / 200000000000000000 : ℝ) (323539066109107 / 10000000000000000 : ℝ)
    (cell13104 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · have h := gap_lower (n := 13104) (a := (84000314074123 / 100000000000000 : ℝ)) (b := (157130836161 / 100000000000000 : ℝ)) (q := (137765682253 / 6250000000000 : ℝ))
      (E := (cell13104 ⟨2, by decide⟩).energy) (xi := (323539066109107 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13104 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13104]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13104])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13104) (a := (84000314074123 / 100000000000000 : ℝ)) (b := (157130836161 / 100000000000000 : ℝ)) (q := (137765682253 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13104])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13104])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13104]

theorem cert13104_3 : CellCertificate 13104 (43786907336771 / 500000000000000 : ℝ) (320577164036907 / 200000000000000000 : ℝ) (323539066109107 / 10000000000000000 : ℝ)
    (cell13104 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · have h := gap_lower (n := 13104) (a := (83965474859447 / 100000000000000 : ℝ)) (b := (157130836161 / 100000000000000 : ℝ)) (q := (2204254933051 / 100000000000000 : ℝ))
      (E := (cell13104 ⟨3, by decide⟩).energy) (xi := (323539066109107 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13104 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13104]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13104])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13104) (a := (83965474859447 / 100000000000000 : ℝ)) (b := (157130836161 / 100000000000000 : ℝ)) (q := (2204254933051 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13104])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13104])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13104]

theorem cert13104_4 : CellCertificate 13104 (43786907336771 / 500000000000000 : ℝ) (320577164036907 / 200000000000000000 : ℝ) (323539066109107 / 10000000000000000 : ℝ)
    (cell13104 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · have h := gap_lower (n := 13104) (a := (83930660385429 / 100000000000000 : ℝ)) (b := (157130836161 / 100000000000000 : ℝ)) (q := (2204258968447 / 100000000000000 : ℝ))
      (E := (cell13104 ⟨4, by decide⟩).energy) (xi := (323539066109107 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13104 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13104]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13104])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13104) (a := (83930660385429 / 100000000000000 : ℝ)) (b := (157130836161 / 100000000000000 : ℝ)) (q := (2204258968447 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13104])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13104])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13104]

theorem cert13104_5 : CellCertificate 13104 (43786907336771 / 500000000000000 : ℝ) (320577164036907 / 200000000000000000 : ℝ) (323539066109107 / 10000000000000000 : ℝ)
    (cell13104 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · have h := gap_lower (n := 13104) (a := (10486983827027 / 12500000000000 : ℝ)) (b := (157130836161 / 100000000000000 : ℝ)) (q := (2204262972133 / 100000000000000 : ℝ))
      (E := (cell13104 ⟨5, by decide⟩).energy) (xi := (323539066109107 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13104 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13104]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13104])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13104) (a := (10486983827027 / 12500000000000 : ℝ)) (b := (157130836161 / 100000000000000 : ℝ)) (q := (2204262972133 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13104])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13104])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13104]

theorem cert13104_6 : CellCertificate 13104 (43786907336771 / 500000000000000 : ℝ) (320577164036907 / 200000000000000000 : ℝ) (323539066109107 / 10000000000000000 : ℝ)
    (cell13104 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · have h := gap_lower (n := 13104) (a := (83861105516141 / 100000000000000 : ℝ)) (b := (157130836161 / 100000000000000 : ℝ)) (q := (2204266951649 / 100000000000000 : ℝ))
      (E := (cell13104 ⟨6, by decide⟩).energy) (xi := (323539066109107 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13104 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13104]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13104])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13104) (a := (83861105516141 / 100000000000000 : ℝ)) (b := (157130836161 / 100000000000000 : ℝ)) (q := (2204266951649 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13104])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13104])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13104]

theorem cert13104_7 : CellCertificate 13104 (43786907336771 / 500000000000000 : ℝ) (320577164036907 / 200000000000000000 : ℝ) (323539066109107 / 10000000000000000 : ℝ)
    (cell13104 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · have h := gap_lower (n := 13104) (a := (654893476951 / 781250000000 : ℝ)) (b := (157130836161 / 100000000000000 : ℝ)) (q := (2204270972291 / 100000000000000 : ℝ))
      (E := (cell13104 ⟨7, by decide⟩).energy) (xi := (323539066109107 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13104 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13104]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13104])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13104) (a := (654893476951 / 781250000000 : ℝ)) (b := (157130836161 / 100000000000000 : ℝ)) (q := (2204270972291 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13104])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13104])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13104]

theorem cert13104_8 : CellCertificate 13104 (43786907336771 / 500000000000000 : ℝ) (320577164036907 / 200000000000000000 : ℝ) (323539066109107 / 10000000000000000 : ℝ)
    (cell13104 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · have h := gap_lower (n := 13104) (a := (83791649181683 / 100000000000000 : ℝ)) (b := (157130836161 / 100000000000000 : ℝ)) (q := (3526839973 / 160000000000 : ℝ))
      (E := (cell13104 ⟨8, by decide⟩).energy) (xi := (323539066109107 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13104 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13104]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13104])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13104) (a := (83791649181683 / 100000000000000 : ℝ)) (b := (157130836161 / 100000000000000 : ℝ)) (q := (3526839973 / 160000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13104])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13104])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13104]

theorem cert13104_9 : CellCertificate 13104 (43786907336771 / 500000000000000 : ℝ) (320577164036907 / 200000000000000000 : ℝ) (323539066109107 / 10000000000000000 : ℝ)
    (cell13104 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · have h := gap_lower (n := 13104) (a := (83756957876897 / 100000000000000 : ℝ)) (b := (157130836161 / 100000000000000 : ℝ)) (q := (1102139495467 / 50000000000000 : ℝ))
      (E := (cell13104 ⟨9, by decide⟩).energy) (xi := (323539066109107 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13104 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13104]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13104])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13104) (a := (83756957876897 / 100000000000000 : ℝ)) (b := (157130836161 / 100000000000000 : ℝ)) (q := (1102139495467 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13104])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13104])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13104]

theorem cert13104_10 : CellCertificate 13104 (43786907336771 / 500000000000000 : ℝ) (320577164036907 / 200000000000000000 : ℝ) (323539066109107 / 10000000000000000 : ℝ)
    (cell13104 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · have h := gap_lower (n := 13104) (a := (16744458220089 / 20000000000000 : ℝ)) (b := (157130836161 / 100000000000000 : ℝ)) (q := (2204283002249 / 100000000000000 : ℝ))
      (E := (cell13104 ⟨10, by decide⟩).energy) (xi := (323539066109107 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13104 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13104]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13104])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13104) (a := (16744458220089 / 20000000000000 : ℝ)) (b := (157130836161 / 100000000000000 : ℝ)) (q := (2204283002249 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13104])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13104])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13104]

theorem cert13104_11 : CellCertificate 13104 (43786907336771 / 500000000000000 : ℝ) (320577164036907 / 200000000000000000 : ℝ) (323539066109107 / 10000000000000000 : ℝ)
    (cell13104 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · have h := gap_lower (n := 13104) (a := (16737529763517 / 20000000000000 : ℝ)) (b := (157130836161 / 100000000000000 : ℝ)) (q := (2204287023353 / 100000000000000 : ℝ))
      (E := (cell13104 ⟨11, by decide⟩).energy) (xi := (323539066109107 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13104 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13104]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13104])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13104) (a := (16737529763517 / 20000000000000 : ℝ)) (b := (157130836161 / 100000000000000 : ℝ)) (q := (2204287023353 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13104])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13104])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13104]

theorem cert13104_12 : CellCertificate 13104 (43786907336771 / 500000000000000 : ℝ) (320577164036907 / 200000000000000000 : ℝ) (323539066109107 / 10000000000000000 : ℝ)
    (cell13104 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · have h := gap_lower (n := 13104) (a := (10456628874219 / 12500000000000 : ℝ)) (b := (157130836161 / 100000000000000 : ℝ)) (q := (551072765071 / 25000000000000 : ℝ))
      (E := (cell13104 ⟨12, by decide⟩).energy) (xi := (323539066109107 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13104 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13104]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13104])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13104) (a := (10456628874219 / 12500000000000 : ℝ)) (b := (157130836161 / 100000000000000 : ℝ)) (q := (551072765071 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13104])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13104])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13104]

theorem cert13104_13 : CellCertificate 13104 (43786907336771 / 500000000000000 : ℝ) (320577164036907 / 200000000000000000 : ℝ) (323539066109107 / 10000000000000000 : ℝ)
    (cell13104 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · have h := gap_lower (n := 13104) (a := (20904609398641 / 25000000000000 : ℝ)) (b := (157130836161 / 100000000000000 : ℝ)) (q := (551073765169 / 25000000000000 : ℝ))
      (E := (cell13104 ⟨13, by decide⟩).energy) (xi := (323539066109107 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13104 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13104]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13104])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13104) (a := (20904609398641 / 25000000000000 : ℝ)) (b := (157130836161 / 100000000000000 : ℝ)) (q := (551073765169 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13104])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13104])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13104]

theorem cert13104_14 : CellCertificate 13104 (43786907336771 / 500000000000000 : ℝ) (320577164036907 / 200000000000000000 : ℝ) (323539066109107 / 10000000000000000 : ℝ)
    (cell13104 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · have h := gap_lower (n := 13104) (a := (83583868585817 / 100000000000000 : ℝ)) (b := (157130836161 / 100000000000000 : ℝ)) (q := (2204299088179 / 100000000000000 : ℝ))
      (E := (cell13104 ⟨14, by decide⟩).energy) (xi := (323539066109107 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13104 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13104]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13104])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13104) (a := (83583868585817 / 100000000000000 : ℝ)) (b := (157130836161 / 100000000000000 : ℝ)) (q := (2204299088179 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13104])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13104])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13104]

theorem cert13104_15 : CellCertificate 13104 (43786907336771 / 500000000000000 : ℝ) (320577164036907 / 200000000000000000 : ℝ) (323539066109107 / 10000000000000000 : ℝ)
    (cell13104 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · have h := gap_lower (n := 13104) (a := (83549323933483 / 100000000000000 : ℝ)) (b := (157130836161 / 100000000000000 : ℝ)) (q := (2204303089893 / 100000000000000 : ℝ))
      (E := (cell13104 ⟨15, by decide⟩).energy) (xi := (323539066109107 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13104 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13104]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13104])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13104) (a := (83549323933483 / 100000000000000 : ℝ)) (b := (157130836161 / 100000000000000 : ℝ)) (q := (2204303089893 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13104])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13104])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13104]

theorem cert13104_16 : CellCertificate 13104 (43786907336771 / 500000000000000 : ℝ) (320577164036907 / 200000000000000000 : ℝ) (323539066109107 / 10000000000000000 : ℝ)
    (cell13104 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · have h := gap_lower (n := 13104) (a := (83514803603711 / 100000000000000 : ℝ)) (b := (157130836161 / 100000000000000 : ℝ)) (q := (551076767701 / 25000000000000 : ℝ))
      (E := (cell13104 ⟨16, by decide⟩).energy) (xi := (323539066109107 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13104 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13104]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13104])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13104) (a := (83514803603711 / 100000000000000 : ℝ)) (b := (157130836161 / 100000000000000 : ℝ)) (q := (551076767701 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13104])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13104])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13104]

theorem cert13104_17 : CellCertificate 13104 (43786907336771 / 500000000000000 : ℝ) (320577164036907 / 200000000000000000 : ℝ) (323539066109107 / 10000000000000000 : ℝ)
    (cell13104 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · have h := gap_lower (n := 13104) (a := (3339212302513 / 4000000000000 : ℝ)) (b := (157130836161 / 100000000000000 : ℝ)) (q := (2204311093903 / 100000000000000 : ℝ))
      (E := (cell13104 ⟨17, by decide⟩).energy) (xi := (323539066109107 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13104 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13104]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13104])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13104) (a := (3339212302513 / 4000000000000 : ℝ)) (b := (157130836161 / 100000000000000 : ℝ)) (q := (2204311093903 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13104])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13104])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13104]

theorem cert13104_18 : CellCertificate 13104 (43786907336771 / 500000000000000 : ℝ) (320577164036907 / 200000000000000000 : ℝ) (323539066109107 / 10000000000000000 : ℝ)
    (cell13104 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · have h := gap_lower (n := 13104) (a := (83445835777323 / 100000000000000 : ℝ)) (b := (157130836161 / 100000000000000 : ℝ)) (q := (2204315105493 / 100000000000000 : ℝ))
      (E := (cell13104 ⟨18, by decide⟩).energy) (xi := (323539066109107 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13104 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13104]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13104])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13104) (a := (83445835777323 / 100000000000000 : ℝ)) (b := (157130836161 / 100000000000000 : ℝ)) (q := (2204315105493 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13104])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13104])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13104]

theorem cert13104_19 : CellCertificate 13104 (43786907336771 / 500000000000000 : ℝ) (320577164036907 / 200000000000000000 : ℝ) (323539066109107 / 10000000000000000 : ℝ)
    (cell13104 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · have h := gap_lower (n := 13104) (a := (20852847053469 / 25000000000000 : ℝ)) (b := (157130836161 / 100000000000000 : ℝ)) (q := (2204319109837 / 100000000000000 : ℝ))
      (E := (cell13104 ⟨19, by decide⟩).energy) (xi := (323539066109107 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13104 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13104]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13104])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13104) (a := (20852847053469 / 25000000000000 : ℝ)) (b := (157130836161 / 100000000000000 : ℝ)) (q := (2204319109837 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13104])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13104])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13104]

theorem cert13105_0 : CellCertificate 13105 (175142367992743 / 2000000000000000 : ℝ) (801381735099847 / 500000000000000000 : ℝ) (64702762206659 / 2000000000000000 : ℝ)
    (cell13105 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · have h := gap_lower (n := 13105) (a := (4203502633063 / 5000000000000 : ℝ)) (b := (78559354183 / 50000000000000 : ℝ)) (q := (2204130980853 / 100000000000000 : ℝ))
      (E := (cell13105 ⟨0, by decide⟩).energy) (xi := (64702762206659 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13105 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13105]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13105])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13105) (a := (4203502633063 / 5000000000000 : ℝ)) (b := (78559354183 / 50000000000000 : ℝ)) (q := (2204130980853 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13105])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13105])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13105]

theorem cert13105_1 : CellCertificate 13105 (175142367992743 / 2000000000000000 : ℝ) (801381735099847 / 500000000000000000 : ℝ) (64702762206659 / 2000000000000000 : ℝ)
    (cell13105 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · have h := gap_lower (n := 13105) (a := (84035163863259 / 100000000000000 : ℝ)) (b := (78559354183 / 50000000000000 : ℝ)) (q := (2204134981419 / 100000000000000 : ℝ))
      (E := (cell13105 ⟨1, by decide⟩).energy) (xi := (64702762206659 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13105 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13105]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13105])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13105) (a := (84035163863259 / 100000000000000 : ℝ)) (b := (78559354183 / 50000000000000 : ℝ)) (q := (2204134981419 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13105])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13105])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13105]

theorem cert13105_2 : CellCertificate 13105 (175142367992743 / 2000000000000000 : ℝ) (801381735099847 / 500000000000000000 : ℝ) (64702762206659 / 2000000000000000 : ℝ)
    (cell13105 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · have h := gap_lower (n := 13105) (a := (16800059975637 / 20000000000000 : ℝ)) (b := (78559354183 / 50000000000000 : ℝ)) (q := (551034745983 / 25000000000000 : ℝ))
      (E := (cell13105 ⟨2, by decide⟩).energy) (xi := (64702762206659 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13105 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13105]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13105])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13105) (a := (16800059975637 / 20000000000000 : ℝ)) (b := (78559354183 / 50000000000000 : ℝ)) (q := (551034745983 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13105])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13105])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13105]

theorem cert13105_3 : CellCertificate 13105 (175142367992743 / 2000000000000000 : ℝ) (801381735099847 / 500000000000000000 : ℝ) (64702762206659 / 2000000000000000 : ℝ)
    (cell13105 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · have h := gap_lower (n := 13105) (a := (41982730334903 / 50000000000000 : ℝ)) (b := (78559354183 / 50000000000000 : ℝ)) (q := (68879468649 / 3125000000000 : ℝ))
      (E := (cell13105 ⟨3, by decide⟩).energy) (xi := (64702762206659 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13105 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13105]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13105])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13105) (a := (41982730334903 / 50000000000000 : ℝ)) (b := (78559354183 / 50000000000000 : ℝ)) (q := (68879468649 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13105])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13105])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13105]

theorem cert13105_4 : CellCertificate 13105 (175142367992743 / 2000000000000000 : ℝ) (801381735099847 / 500000000000000000 : ℝ) (64702762206659 / 2000000000000000 : ℝ)
    (cell13105 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · have h := gap_lower (n := 13105) (a := (41965323101039 / 50000000000000 : ℝ)) (b := (78559354183 / 50000000000000 : ℝ)) (q := (440829405609 / 20000000000000 : ℝ))
      (E := (cell13105 ⟨4, by decide⟩).energy) (xi := (64702762206659 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13105 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13105]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13105])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13105) (a := (41965323101039 / 50000000000000 : ℝ)) (b := (78559354183 / 50000000000000 : ℝ)) (q := (440829405609 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13105])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13105])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13105]

theorem cert13105_5 : CellCertificate 13105 (175142367992743 / 2000000000000000 : ℝ) (801381735099847 / 500000000000000000 : ℝ) (64702762206659 / 2000000000000000 : ℝ)
    (cell13105 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · have h := gap_lower (n := 13105) (a := (1677917128783 / 2000000000000 : ℝ)) (b := (78559354183 / 50000000000000 : ℝ)) (q := (1102075513829 / 50000000000000 : ℝ))
      (E := (cell13105 ⟨5, by decide⟩).energy) (xi := (64702762206659 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13105 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13105]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13105])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13105) (a := (1677917128783 / 2000000000000 : ℝ)) (b := (78559354183 / 50000000000000 : ℝ)) (q := (1102075513829 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13105])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13105])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13105]

theorem cert13105_6 : CellCertificate 13105 (175142367992743 / 2000000000000000 : ℝ) (801381735099847 / 500000000000000000 : ℝ) (64702762206659 / 2000000000000000 : ℝ)
    (cell13105 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · have h := gap_lower (n := 13105) (a := (16772218269071 / 20000000000000 : ℝ)) (b := (78559354183 / 50000000000000 : ℝ)) (q := (2204155061137 / 100000000000000 : ℝ))
      (E := (cell13105 ⟨6, by decide⟩).energy) (xi := (64702762206659 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13105 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13105]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13105])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13105) (a := (16772218269071 / 20000000000000 : ℝ)) (b := (78559354183 / 50000000000000 : ℝ)) (q := (2204155061137 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13105])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13105])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13105]

theorem cert13105_7 : CellCertificate 13105 (175142367992743 / 2000000000000000 : ℝ) (801381735099847 / 500000000000000000 : ℝ) (64702762206659 / 2000000000000000 : ℝ)
    (cell13105 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · have h := gap_lower (n := 13105) (a := (16765270177043 / 20000000000000 : ℝ)) (b := (78559354183 / 50000000000000 : ℝ)) (q := (34439985591 / 1562500000000 : ℝ))
      (E := (cell13105 ⟨7, by decide⟩).energy) (xi := (64702762206659 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13105 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13105]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13105])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13105) (a := (16765270177043 / 20000000000000 : ℝ)) (b := (78559354183 / 50000000000000 : ℝ)) (q := (34439985591 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13105])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13105])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13105]

theorem cert13105_8 : CellCertificate 13105 (175142367992743 / 2000000000000000 : ℝ) (801381735099847 / 500000000000000000 : ℝ) (64702762206659 / 2000000000000000 : ℝ)
    (cell13105 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · have h := gap_lower (n := 13105) (a := (41895817511719 / 50000000000000 : ℝ)) (b := (78559354183 / 50000000000000 : ℝ)) (q := (2204163084749 / 100000000000000 : ℝ))
      (E := (cell13105 ⟨8, by decide⟩).energy) (xi := (64702762206659 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13105 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13105]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13105])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13105) (a := (41895817511719 / 50000000000000 : ℝ)) (b := (78559354183 / 50000000000000 : ℝ)) (q := (2204163084749 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13105])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13105])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13105]

theorem cert13105_9 : CellCertificate 13105 (175142367992743 / 2000000000000000 : ℝ) (801381735099847 / 500000000000000000 : ℝ) (64702762206659 / 2000000000000000 : ℝ)
    (cell13105 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · have h := gap_lower (n := 13105) (a := (16751388744983 / 20000000000000 : ℝ)) (b := (78559354183 / 50000000000000 : ℝ)) (q := (275520886087 / 12500000000000 : ℝ))
      (E := (cell13105 ⟨9, by decide⟩).energy) (xi := (64702762206659 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13105 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13105]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13105])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13105) (a := (16751388744983 / 20000000000000 : ℝ)) (b := (78559354183 / 50000000000000 : ℝ)) (q := (275520886087 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13105])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13105])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13105]

theorem cert13105_10 : CellCertificate 13105 (175142367992743 / 2000000000000000 : ℝ) (801381735099847 / 500000000000000000 : ℝ) (64702762206659 / 2000000000000000 : ℝ)
    (cell13105 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · have h := gap_lower (n := 13105) (a := (523264230967 / 625000000000 : ℝ)) (b := (78559354183 / 50000000000000 : ℝ)) (q := (2204171096197 / 100000000000000 : ℝ))
      (E := (cell13105 ⟨10, by decide⟩).energy) (xi := (64702762206659 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13105 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13105]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13105])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13105) (a := (523264230967 / 625000000000 : ℝ)) (b := (78559354183 / 50000000000000 : ℝ)) (q := (2204171096197 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13105])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13105])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13105]

theorem cert13105_11 : CellCertificate 13105 (175142367992743 / 2000000000000000 : ℝ) (801381735099847 / 500000000000000000 : ℝ) (64702762206659 / 2000000000000000 : ℝ)
    (cell13105 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · have h := gap_lower (n := 13105) (a := (83687634678111 / 100000000000000 : ℝ)) (b := (78559354183 / 50000000000000 : ℝ)) (q := (2204175113533 / 100000000000000 : ℝ))
      (E := (cell13105 ⟨11, by decide⟩).energy) (xi := (64702762206659 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13105 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13105]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13105])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13105) (a := (83687634678111 / 100000000000000 : ℝ)) (b := (78559354183 / 50000000000000 : ℝ)) (q := (2204175113533 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13105])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13105])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13105]

theorem cert13105_12 : CellCertificate 13105 (175142367992743 / 2000000000000000 : ℝ) (801381735099847 / 500000000000000000 : ℝ) (64702762206659 / 2000000000000000 : ℝ)
    (cell13105 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · have h := gap_lower (n := 13105) (a := (20913254215131 / 25000000000000 : ℝ)) (b := (78559354183 / 50000000000000 : ℝ)) (q := (2204179088613 / 100000000000000 : ℝ))
      (E := (cell13105 ⟨12, by decide⟩).energy) (xi := (64702762206659 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13105 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13105]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13105])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13105) (a := (20913254215131 / 25000000000000 : ℝ)) (b := (78559354183 / 50000000000000 : ℝ)) (q := (2204179088613 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13105])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13105])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13105]

theorem cert13105_13 : CellCertificate 13105 (175142367992743 / 2000000000000000 : ℝ) (801381735099847 / 500000000000000000 : ℝ) (64702762206659 / 2000000000000000 : ℝ)
    (cell13105 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · have h := gap_lower (n := 13105) (a := (83618423467577 / 100000000000000 : ℝ)) (b := (78559354183 / 50000000000000 : ℝ)) (q := (110209157173 / 5000000000000 : ℝ))
      (E := (cell13105 ⟨13, by decide⟩).energy) (xi := (64702762206659 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13105 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13105]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13105])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13105) (a := (83618423467577 / 100000000000000 : ℝ)) (b := (78559354183 / 50000000000000 : ℝ)) (q := (110209157173 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13105])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13105])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13105]

theorem cert13105_14 : CellCertificate 13105 (175142367992743 / 2000000000000000 : ℝ) (801381735099847 / 500000000000000000 : ℝ) (64702762206659 / 2000000000000000 : ℝ)
    (cell13105 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · have h := gap_lower (n := 13105) (a := (16716770893013 / 20000000000000 : ℝ)) (b := (78559354183 / 50000000000000 : ℝ)) (q := (1102093554579 / 50000000000000 : ℝ))
      (E := (cell13105 ⟨14, by decide⟩).energy) (xi := (64702762206659 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13105 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13105]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13105])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13105) (a := (16716770893013 / 20000000000000 : ℝ)) (b := (78559354183 / 50000000000000 : ℝ)) (q := (1102093554579 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13105])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13105])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13105]

theorem cert13105_15 : CellCertificate 13105 (175142367992743 / 2000000000000000 : ℝ) (801381735099847 / 500000000000000000 : ℝ) (64702762206659 / 2000000000000000 : ℝ)
    (cell13105 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · have h := gap_lower (n := 13105) (a := (83549309818961 / 100000000000000 : ℝ)) (b := (78559354183 / 50000000000000 : ℝ)) (q := (2204191165467 / 100000000000000 : ℝ))
      (E := (cell13105 ⟨15, by decide⟩).energy) (xi := (64702762206659 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13105 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13105]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13105])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13105) (a := (83549309818961 / 100000000000000 : ℝ)) (b := (78559354183 / 50000000000000 : ℝ)) (q := (2204191165467 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13105])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13105])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13105]

theorem cert13105_16 : CellCertificate 13105 (175142367992743 / 2000000000000000 : ℝ) (801381735099847 / 500000000000000000 : ℝ) (64702762206659 / 2000000000000000 : ℝ)
    (cell13105 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · have h := gap_lower (n := 13105) (a := (83514789495413 / 100000000000000 : ℝ)) (b := (78559354183 / 50000000000000 : ℝ)) (q := (551048785711 / 25000000000000 : ℝ))
      (E := (cell13105 ⟨16, by decide⟩).energy) (xi := (64702762206659 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13105 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13105]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13105])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13105) (a := (83514789495413 / 100000000000000 : ℝ)) (b := (78559354183 / 50000000000000 : ℝ)) (q := (551048785711 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13105])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13105])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13105]

theorem cert13105_17 : CellCertificate 13105 (175142367992743 / 2000000000000000 : ℝ) (801381735099847 / 500000000000000000 : ℝ) (64702762206659 / 2000000000000000 : ℝ)
    (cell13105 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · have h := gap_lower (n := 13105) (a := (41740146730373 / 50000000000000 : ℝ)) (b := (78559354183 / 50000000000000 : ℝ)) (q := (275524895307 / 12500000000000 : ℝ))
      (E := (cell13105 ⟨17, by decide⟩).energy) (xi := (64702762206659 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13105 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13105]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13105])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13105) (a := (41740146730373 / 50000000000000 : ℝ)) (b := (78559354183 / 50000000000000 : ℝ)) (q := (275524895307 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13105])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13105])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13105]

theorem cert13105_18 : CellCertificate 13105 (175142367992743 / 2000000000000000 : ℝ) (801381735099847 / 500000000000000000 : ℝ) (64702762206659 / 2000000000000000 : ℝ)
    (cell13105 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · have h := gap_lower (n := 13105) (a := (83445821681457 / 100000000000000 : ℝ)) (b := (78559354183 / 50000000000000 : ℝ)) (q := (440840634121 / 20000000000000 : ℝ))
      (E := (cell13105 ⟨18, by decide⟩).energy) (xi := (64702762206659 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13105 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13105]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13105])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13105) (a := (83445821681457 / 100000000000000 : ℝ)) (b := (78559354183 / 50000000000000 : ℝ)) (q := (440840634121 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13105])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13105])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13105]

theorem cert13105_19 : CellCertificate 13105 (175142367992743 / 2000000000000000 : ℝ) (801381735099847 / 500000000000000000 : ℝ) (64702762206659 / 2000000000000000 : ℝ)
    (cell13105 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · have h := gap_lower (n := 13105) (a := (41705687062109 / 50000000000000 : ℝ)) (b := (78559354183 / 50000000000000 : ℝ)) (q := (1102103585777 / 50000000000000 : ℝ))
      (E := (cell13105 ⟨19, by decide⟩).energy) (xi := (64702762206659 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13105 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13105]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13105])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13105) (a := (41705687062109 / 50000000000000 : ℝ)) (b := (78559354183 / 50000000000000 : ℝ)) (q := (1102103585777 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13105])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13105])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13105]

theorem cert13106_0 : CellCertificate 13106 (437842768517329 / 5000000000000000 : ℝ) (400660284722909 / 250000000000000000 : ℝ) (161744279964197 / 5000000000000000 : ℝ)
    (cell13106 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · have h := gap_lower (n := 13106) (a := (21017509613721 / 25000000000000 : ℝ)) (b := (157106582449 / 100000000000000 : ℝ)) (q := (2204019052941 / 100000000000000 : ℝ))
      (E := (cell13106 ⟨0, by decide⟩).energy) (xi := (161744279964197 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13106 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13106]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13106])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13106) (a := (21017509613721 / 25000000000000 : ℝ)) (b := (157106582449 / 100000000000000 : ℝ)) (q := (2204019052941 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13106])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13106])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13106]

theorem cert13106_1 : CellCertificate 13106 (437842768517329 / 5000000000000000 : ℝ) (400660284722909 / 250000000000000000 : ℝ) (161744279964197 / 5000000000000000 : ℝ)
    (cell13106 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · have h := gap_lower (n := 13106) (a := (84035149663189 / 100000000000000 : ℝ)) (b := (157106582449 / 100000000000000 : ℝ)) (q := (68875720289 / 3125000000000 : ℝ))
      (E := (cell13106 ⟨1, by decide⟩).energy) (xi := (161744279964197 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13106 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13106]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13106])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13106) (a := (84035149663189 / 100000000000000 : ℝ)) (b := (157106582449 / 100000000000000 : ℝ)) (q := (68875720289 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13106])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13106])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13106]

theorem cert13106_2 : CellCertificate 13106 (437842768517329 / 5000000000000000 : ℝ) (400660284722909 / 250000000000000000 : ℝ) (161744279964197 / 5000000000000000 : ℝ)
    (cell13106 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · have h := gap_lower (n := 13106) (a := (1312504463819 / 1562500000000 : ℝ)) (b := (157106582449 / 100000000000000 : ℝ)) (q := (551006776361 / 25000000000000 : ℝ))
      (E := (cell13106 ⟨2, by decide⟩).energy) (xi := (161744279964197 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13106 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13106]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13106])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13106) (a := (1312504463819 / 1562500000000 : ℝ)) (b := (157106582449 / 100000000000000 : ℝ)) (q := (551006776361 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13106])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13106])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13106]

theorem cert13106_3 : CellCertificate 13106 (437842768517329 / 5000000000000000 : ℝ) (400660284722909 / 250000000000000000 : ℝ) (161744279964197 / 5000000000000000 : ℝ)
    (cell13106 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · have h := gap_lower (n := 13106) (a := (20991361620583 / 25000000000000 : ℝ)) (b := (157106582449 / 100000000000000 : ℝ)) (q := (1102015557069 / 50000000000000 : ℝ))
      (E := (cell13106 ⟨3, by decide⟩).energy) (xi := (161744279964197 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13106 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13106]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13106])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13106) (a := (20991361620583 / 25000000000000 : ℝ)) (b := (157106582449 / 100000000000000 : ℝ)) (q := (1102015557069 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13106])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13106])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13106]

theorem cert13106_4 : CellCertificate 13106 (437842768517329 / 5000000000000000 : ℝ) (400660284722909 / 250000000000000000 : ℝ) (161744279964197 / 5000000000000000 : ℝ)
    (cell13106 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · have h := gap_lower (n := 13106) (a := (41965316010447 / 50000000000000 : ℝ)) (b := (157106582449 / 100000000000000 : ℝ)) (q := (137752192711 / 6250000000000 : ℝ))
      (E := (cell13106 ⟨4, by decide⟩).energy) (xi := (161744279964197 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13106 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13106]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13106])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13106) (a := (41965316010447 / 50000000000000 : ℝ)) (b := (157106582449 / 100000000000000 : ℝ)) (q := (137752192711 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13106])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13106])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13106]

theorem cert13106_5 : CellCertificate 13106 (437842768517329 / 5000000000000000 : ℝ) (400660284722909 / 250000000000000000 : ℝ) (161744279964197 / 5000000000000000 : ℝ)
    (cell13106 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · have h := gap_lower (n := 13106) (a := (335583369057 / 400000000000 : ℝ)) (b := (157106582449 / 100000000000000 : ℝ)) (q := (551009784221 / 25000000000000 : ℝ))
      (E := (cell13106 ⟨5, by decide⟩).energy) (xi := (161744279964197 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13106 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13106]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13106])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13106) (a := (335583369057 / 400000000000 : ℝ)) (b := (157106582449 / 100000000000000 : ℝ)) (q := (551009784221 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13106])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13106])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13106]

theorem cert13106_6 : CellCertificate 13106 (437842768517329 / 5000000000000000 : ℝ) (400660284722909 / 250000000000000000 : ℝ) (161744279964197 / 5000000000000000 : ℝ)
    (cell13106 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · have h := gap_lower (n := 13106) (a := (83861077176733 / 100000000000000 : ℝ)) (b := (157106582449 / 100000000000000 : ℝ)) (q := (551010777093 / 25000000000000 : ℝ))
      (E := (cell13106 ⟨6, by decide⟩).energy) (xi := (161744279964197 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13106 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13106]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13106])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13106) (a := (83861077176733 / 100000000000000 : ℝ)) (b := (157106582449 / 100000000000000 : ℝ)) (q := (551010777093 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13106])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13106])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13106]

theorem cert13106_7 : CellCertificate 13106 (437842768517329 / 5000000000000000 : ℝ) (400660284722909 / 250000000000000000 : ℝ) (161744279964197 / 5000000000000000 : ℝ)
    (cell13106 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · have h := gap_lower (n := 13106) (a := (83826336722867 / 100000000000000 : ℝ)) (b := (157106582449 / 100000000000000 : ℝ)) (q := (2204047121079 / 100000000000000 : ℝ))
      (E := (cell13106 ⟨7, by decide⟩).energy) (xi := (161744279964197 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13106 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13106]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13106])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13106) (a := (83826336722867 / 100000000000000 : ℝ)) (b := (157106582449 / 100000000000000 : ℝ)) (q := (2204047121079 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13106])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13106])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13106]

theorem cert13106_8 : CellCertificate 13106 (437842768517329 / 5000000000000000 : ℝ) (400660284722909 / 250000000000000000 : ℝ) (161744279964197 / 5000000000000000 : ℝ)
    (cell13106 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · have h := gap_lower (n := 13106) (a := (83791620867357 / 100000000000000 : ℝ)) (b := (157106582449 / 100000000000000 : ℝ)) (q := (1102025562037 / 50000000000000 : ℝ))
      (E := (cell13106 ⟨8, by decide⟩).energy) (xi := (161744279964197 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13106 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13106]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13106])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13106) (a := (83791620867357 / 100000000000000 : ℝ)) (b := (157106582449 / 100000000000000 : ℝ)) (q := (1102025562037 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13106])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13106])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13106]

theorem cert13106_9 : CellCertificate 13106 (437842768517329 / 5000000000000000 : ℝ) (400660284722909 / 250000000000000000 : ℝ) (161744279964197 / 5000000000000000 : ℝ)
    (cell13106 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · have h := gap_lower (n := 13106) (a := (16751385915019 / 20000000000000 : ℝ)) (b := (157106582449 / 100000000000000 : ℝ)) (q := (2204055182197 / 100000000000000 : ℝ))
      (E := (cell13106 ⟨9, by decide⟩).energy) (xi := (161744279964197 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13106 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13106]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13106])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13106) (a := (16751385915019 / 20000000000000 : ℝ)) (b := (157106582449 / 100000000000000 : ℝ)) (q := (2204055182197 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13106])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13106])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13106]

theorem cert13106_10 : CellCertificate 13106 (437842768517329 / 5000000000000000 : ℝ) (400660284722909 / 250000000000000000 : ℝ) (161744279964197 / 5000000000000000 : ℝ)
    (cell13106 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · have h := gap_lower (n := 13106) (a := (83722262811157 / 100000000000000 : ℝ)) (b := (157106582449 / 100000000000000 : ℝ)) (q := (2204059185883 / 100000000000000 : ℝ))
      (E := (cell13106 ⟨10, by decide⟩).energy) (xi := (161744279964197 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13106 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13106]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13106])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13106) (a := (83722262811157 / 100000000000000 : ℝ)) (b := (157106582449 / 100000000000000 : ℝ)) (q := (2204059185883 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13106])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13106])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13106]

theorem cert13106_11 : CellCertificate 13106 (437842768517329 / 5000000000000000 : ℝ) (400660284722909 / 250000000000000000 : ℝ) (161744279964197 / 5000000000000000 : ℝ)
    (cell13106 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · have h := gap_lower (n := 13106) (a := (41843810270399 / 50000000000000 : ℝ)) (b := (157106582449 / 100000000000000 : ℝ)) (q := (2204063199453 / 100000000000000 : ℝ))
      (E := (cell13106 ⟨11, by decide⟩).energy) (xi := (161744279964197 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13106 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13106]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13106])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13106) (a := (41843810270399 / 50000000000000 : ℝ)) (b := (157106582449 / 100000000000000 : ℝ)) (q := (2204063199453 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13106])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13106])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13106]

theorem cert13106_12 : CellCertificate 13106 (437842768517329 / 5000000000000000 : ℝ) (400660284722909 / 250000000000000000 : ℝ) (161744279964197 / 5000000000000000 : ℝ)
    (cell13106 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · have h := gap_lower (n := 13106) (a := (83653002729457 / 100000000000000 : ℝ)) (b := (157106582449 / 100000000000000 : ℝ)) (q := (2204067170811 / 100000000000000 : ℝ))
      (E := (cell13106 ⟨12, by decide⟩).energy) (xi := (161744279964197 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13106 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13106]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13106])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13106) (a := (83653002729457 / 100000000000000 : ℝ)) (b := (157106582449 / 100000000000000 : ℝ)) (q := (2204067170811 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13106])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13106])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13106]

theorem cert13106_13 : CellCertificate 13106 (437842768517329 / 5000000000000000 : ℝ) (400660284722909 / 250000000000000000 : ℝ) (161744279964197 / 5000000000000000 : ℝ)
    (cell13106 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · have h := gap_lower (n := 13106) (a := (83618409342749 / 100000000000000 : ℝ)) (b := (157106582449 / 100000000000000 : ℝ)) (q := (68877225687 / 3125000000000 : ℝ))
      (E := (cell13106 ⟨13, by decide⟩).energy) (xi := (161744279964197 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13106 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13106]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13106])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13106) (a := (83618409342749 / 100000000000000 : ℝ)) (b := (157106582449 / 100000000000000 : ℝ)) (q := (68877225687 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13106])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13106])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13106]

theorem cert13106_14 : CellCertificate 13106 (437842768517329 / 5000000000000000 : ℝ) (400660284722909 / 250000000000000000 : ℝ) (161744279964197 / 5000000000000000 : ℝ)
    (cell13106 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · have h := gap_lower (n := 13106) (a := (83583840346471 / 100000000000000 : ℝ)) (b := (157106582449 / 100000000000000 : ℝ)) (q := (2204075242233 / 100000000000000 : ℝ))
      (E := (cell13106 ⟨14, by decide⟩).energy) (xi := (161744279964197 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13106 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13106]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13106])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13106) (a := (83583840346471 / 100000000000000 : ℝ)) (b := (157106582449 / 100000000000000 : ℝ)) (q := (2204075242233 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13106])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13106])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13106]

theorem cert13106_15 : CellCertificate 13106 (437842768517329 / 5000000000000000 : ℝ) (400660284722909 / 250000000000000000 : ℝ) (161744279964197 / 5000000000000000 : ℝ)
    (cell13106 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · have h := gap_lower (n := 13106) (a := (16709859141319 / 20000000000000 : ℝ)) (b := (157106582449 / 100000000000000 : ℝ)) (q := (1102039618393 / 50000000000000 : ℝ))
      (E := (cell13106 ⟨15, by decide⟩).energy) (xi := (161744279964197 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13106 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13106]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13106])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13106) (a := (16709859141319 / 20000000000000 : ℝ)) (b := (157106582449 / 100000000000000 : ℝ)) (q := (1102039618393 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13106])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13106])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13106]

theorem cert13106_16 : CellCertificate 13106 (437842768517329 / 5000000000000000 : ℝ) (400660284722909 / 250000000000000000 : ℝ) (161744279964197 / 5000000000000000 : ℝ)
    (cell13106 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · have h := gap_lower (n := 13106) (a := (83514775389271 / 100000000000000 : ℝ)) (b := (157106582449 / 100000000000000 : ℝ)) (q := (551020802657 / 25000000000000 : ℝ))
      (E := (cell13106 ⟨16, by decide⟩).energy) (xi := (161744279964197 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13106 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13106]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13106])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13106) (a := (83514775389271 / 100000000000000 : ℝ)) (b := (157106582449 / 100000000000000 : ℝ)) (q := (551020802657 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13106])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13106])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13106]

theorem cert13106_17 : CellCertificate 13106 (437842768517329 / 5000000000000000 : ℝ) (400660284722909 / 250000000000000000 : ℝ) (161744279964197 / 5000000000000000 : ℝ)
    (cell13106 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · have h := gap_lower (n := 13106) (a := (83480279360821 / 100000000000000 : ℝ)) (b := (157106582449 / 100000000000000 : ℝ)) (q := (1102043613377 / 50000000000000 : ℝ))
      (E := (cell13106 ⟨17, by decide⟩).energy) (xi := (161744279964197 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13106 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13106]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13106])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13106) (a := (83480279360821 / 100000000000000 : ℝ)) (b := (157106582449 / 100000000000000 : ℝ)) (q := (1102043613377 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13106])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13106])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13106]

theorem cert13106_18 : CellCertificate 13106 (437842768517329 / 5000000000000000 : ℝ) (400660284722909 / 250000000000000000 : ℝ) (161744279964197 / 5000000000000000 : ℝ)
    (cell13106 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · have h := gap_lower (n := 13106) (a := (16689161517549 / 20000000000000 : ℝ)) (b := (157106582449 / 100000000000000 : ℝ)) (q := (2204091289733 / 100000000000000 : ℝ))
      (E := (cell13106 ⟨18, by decide⟩).energy) (xi := (161744279964197 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13106 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13106]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13106])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13106) (a := (16689161517549 / 20000000000000 : ℝ)) (b := (157106582449 / 100000000000000 : ℝ)) (q := (2204091289733 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13106])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13106])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13106]

theorem cert13106_19 : CellCertificate 13106 (437842768517329 / 5000000000000000 : ℝ) (400660284722909 / 250000000000000000 : ℝ) (161744279964197 / 5000000000000000 : ℝ)
    (cell13106 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · have h := gap_lower (n := 13106) (a := (83411360036713 / 100000000000000 : ℝ)) (b := (157106582449 / 100000000000000 : ℝ)) (q := (137755955457 / 6250000000000 : ℝ))
      (E := (cell13106 ⟨19, by decide⟩).energy) (xi := (161744279964197 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13106 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13106]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13106])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13106) (a := (83411360036713 / 100000000000000 : ℝ)) (b := (157106582449 / 100000000000000 : ℝ)) (q := (137755955457 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13106])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13106])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13106]

theorem cert13107_0 : CellCertificate 13107 (109457404743421 / 1250000000000000 : ℝ) (1602518826256083 / 1000000000000000000 : ℝ) (323463312793413 / 10000000000000000 : ℝ)
    (cell13107 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · have h := gap_lower (n := 13107) (a := (84070024250677 / 100000000000000 : ℝ)) (b := (39273614603 / 25000000000000 : ℝ)) (q := (2203907178609 / 100000000000000 : ℝ))
      (E := (cell13107 ⟨0, by decide⟩).energy) (xi := (323463312793413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13107 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13107]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13107])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13107) (a := (84070024250677 / 100000000000000 : ℝ)) (b := (39273614603 / 25000000000000 : ℝ)) (q := (2203907178609 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13107])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13107])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13107]

theorem cert13107_1 : CellCertificate 13107 (109457404743421 / 1250000000000000 : ℝ) (1602518826256083 / 1000000000000000000 : ℝ) (323463312793413 / 10000000000000000 : ℝ)
    (cell13107 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · have h := gap_lower (n := 13107) (a := (84035135465289 / 100000000000000 : ℝ)) (b := (39273614603 / 25000000000000 : ℝ)) (q := (1101955585339 / 50000000000000 : ℝ))
      (E := (cell13107 ⟨1, by decide⟩).energy) (xi := (323463312793413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13107 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13107]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13107])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13107) (a := (84035135465289 / 100000000000000 : ℝ)) (b := (39273614603 / 25000000000000 : ℝ)) (q := (1101955585339 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13107])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13107])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13107]

theorem cert13107_2 : CellCertificate 13107 (109457404743421 / 1250000000000000 : ℝ) (1602518826256083 / 1000000000000000000 : ℝ) (323463312793413 / 10000000000000000 : ℝ)
    (cell13107 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · have h := gap_lower (n := 13107) (a := (5250016968301 / 6250000000000 : ℝ)) (b := (39273614603 / 25000000000000 : ℝ)) (q := (220391516479 / 10000000000000 : ℝ))
      (E := (cell13107 ⟨2, by decide⟩).energy) (xi := (323463312793413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13107 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13107]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13107])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13107) (a := (5250016968301 / 6250000000000 : ℝ)) (b := (39273614603 / 25000000000000 : ℝ)) (q := (220391516479 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13107])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13107])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13107]

theorem cert13107_3 : CellCertificate 13107 (109457404743421 / 1250000000000000 : ℝ) (1602518826256083 / 1000000000000000000 : ℝ) (323463312793413 / 10000000000000000 : ℝ)
    (cell13107 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · have h := gap_lower (n := 13107) (a := (41982716148513 / 50000000000000 : ℝ)) (b := (39273614603 / 25000000000000 : ℝ)) (q := (1101959613619 / 50000000000000 : ℝ))
      (E := (cell13107 ⟨3, by decide⟩).energy) (xi := (323463312793413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13107 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13107]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13107])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13107) (a := (41982716148513 / 50000000000000 : ℝ)) (b := (39273614603 / 25000000000000 : ℝ)) (q := (1101959613619 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13107])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13107])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13107]

theorem cert13107_4 : CellCertificate 13107 (109457404743421 / 1250000000000000 : ℝ) (1602518826256083 / 1000000000000000000 : ℝ) (323463312793413 / 10000000000000000 : ℝ)
    (cell13107 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · have h := gap_lower (n := 13107) (a := (83930617841877 / 100000000000000 : ℝ)) (b := (39273614603 / 25000000000000 : ℝ)) (q := (1101961596191 / 50000000000000 : ℝ))
      (E := (cell13107 ⟨4, by decide⟩).energy) (xi := (323463312793413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13107 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13107]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13107])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13107) (a := (83930617841877 / 100000000000000 : ℝ)) (b := (39273614603 / 25000000000000 : ℝ)) (q := (1101961596191 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13107])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13107])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13107]

theorem cert13107_5 : CellCertificate 13107 (109457404743421 / 1250000000000000 : ℝ) (1602518826256083 / 1000000000000000000 : ℝ) (323463312793413 / 10000000000000000 : ℝ)
    (cell13107 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · have h := gap_lower (n := 13107) (a := (20973957022879 / 25000000000000 : ℝ)) (b := (39273614603 / 25000000000000 : ℝ)) (q := (1101963620921 / 50000000000000 : ℝ))
      (E := (cell13107 ⟨5, by decide⟩).energy) (xi := (323463312793413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13107 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13107]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13107])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13107) (a := (20973957022879 / 25000000000000 : ℝ)) (b := (39273614603 / 25000000000000 : ℝ)) (q := (1101963620921 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13107])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13107])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13107]

theorem cert13107_6 : CellCertificate 13107 (109457404743421 / 1250000000000000 : ℝ) (1602518826256083 / 1000000000000000000 : ℝ) (323463312793413 / 10000000000000000 : ℝ)
    (cell13107 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · have h := gap_lower (n := 13107) (a := (83861063010277 / 100000000000000 : ℝ)) (b := (39273614603 / 25000000000000 : ℝ)) (q := (2203931209329 / 100000000000000 : ℝ))
      (E := (cell13107 ⟨6, by decide⟩).energy) (xi := (323463312793413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13107 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13107]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13107])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13107) (a := (83861063010277 / 100000000000000 : ℝ)) (b := (39273614603 / 25000000000000 : ℝ)) (q := (2203931209329 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13107])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13107])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13107]

theorem cert13107_7 : CellCertificate 13107 (109457404743421 / 1250000000000000 : ℝ) (1602518826256083 / 1000000000000000000 : ℝ) (323463312793413 / 10000000000000000 : ℝ)
    (cell13107 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · have h := gap_lower (n := 13107) (a := (41913161281341 / 50000000000000 : ℝ)) (b := (39273614603 / 25000000000000 : ℝ)) (q := (2203935218083 / 100000000000000 : ℝ))
      (E := (cell13107 ⟨7, by decide⟩).energy) (xi := (323463312793413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13107 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13107]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13107])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13107) (a := (41913161281341 / 50000000000000 : ℝ)) (b := (39273614603 / 25000000000000 : ℝ)) (q := (2203935218083 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13107])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13107])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13107]

theorem cert13107_8 : CellCertificate 13107 (109457404743421 / 1250000000000000 : ℝ) (1602518826256083 / 1000000000000000000 : ℝ) (323463312793413 / 10000000000000000 : ℝ)
    (cell13107 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · have h := gap_lower (n := 13107) (a := (41895803356719 / 50000000000000 : ℝ)) (b := (39273614603 / 25000000000000 : ℝ)) (q := (2203939275207 / 100000000000000 : ℝ))
      (E := (cell13107 ⟨8, by decide⟩).energy) (xi := (323463312793413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13107 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13107]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13107])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13107) (a := (41895803356719 / 50000000000000 : ℝ)) (b := (39273614603 / 25000000000000 : ℝ)) (q := (2203939275207 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13107])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13107])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13107]

theorem cert13107_9 : CellCertificate 13107 (109457404743421 / 1250000000000000 : ℝ) (1602518826256083 / 1000000000000000000 : ℝ) (323463312793413 / 10000000000000000 : ℝ)
    (cell13107 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · have h := gap_lower (n := 13107) (a := (83756915427437 / 100000000000000 : ℝ)) (b := (39273614603 / 25000000000000 : ℝ)) (q := (1101971635717 / 50000000000000 : ℝ))
      (E := (cell13107 ⟨9, by decide⟩).energy) (xi := (323463312793413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13107 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13107]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13107])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13107) (a := (83756915427437 / 100000000000000 : ℝ)) (b := (39273614603 / 25000000000000 : ℝ)) (q := (1101971635717 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13107])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13107])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13107]

theorem cert13107_10 : CellCertificate 13107 (109457404743421 / 1250000000000000 : ℝ) (1602518826256083 / 1000000000000000000 : ℝ) (323463312793413 / 10000000000000000 : ℝ)
    (cell13107 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · have h := gap_lower (n := 13107) (a := (41861124334877 / 50000000000000 : ℝ)) (b := (39273614603 / 25000000000000 : ℝ)) (q := (1101973635653 / 50000000000000 : ℝ))
      (E := (cell13107 ⟨10, by decide⟩).energy) (xi := (323463312793413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13107 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13107]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13107])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13107) (a := (41861124334877 / 50000000000000 : ℝ)) (b := (39273614603 / 25000000000000 : ℝ)) (q := (1101973635653 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13107])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13107])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13107]

theorem cert13107_11 : CellCertificate 13107 (109457404743421 / 1250000000000000 : ℝ) (1602518826256083 / 1000000000000000000 : ℝ) (323463312793413 / 10000000000000000 : ℝ)
    (cell13107 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · have h := gap_lower (n := 13107) (a := (16737521281129 / 20000000000000 : ℝ)) (b := (39273614603 / 25000000000000 : ℝ)) (q := (220395128111 / 10000000000000 : ℝ))
      (E := (cell13107 ⟨11, by decide⟩).energy) (xi := (323463312793413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13107 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13107]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13107])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13107) (a := (16737521281129 / 20000000000000 : ℝ)) (b := (39273614603 / 25000000000000 : ℝ)) (q := (220395128111 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13107])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13107])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13107]

theorem cert13107_12 : CellCertificate 13107 (109457404743421 / 1250000000000000 : ℝ) (1602518826256083 / 1000000000000000000 : ℝ) (323463312793413 / 10000000000000000 : ℝ)
    (cell13107 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · have h := gap_lower (n := 13107) (a := (20913247150137 / 25000000000000 : ℝ)) (b := (39273614603 / 25000000000000 : ℝ)) (q := (1101977653439 / 50000000000000 : ℝ))
      (E := (cell13107 ⟨12, by decide⟩).energy) (xi := (323463312793413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13107 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13107]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13107])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13107) (a := (20913247150137 / 25000000000000 : ℝ)) (b := (39273614603 / 25000000000000 : ℝ)) (q := (1101977653439 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13107])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13107])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13107]

theorem cert13107_13 : CellCertificate 13107 (109457404743421 / 1250000000000000 : ℝ) (1602518826256083 / 1000000000000000000 : ℝ) (323463312793413 / 10000000000000000 : ℝ)
    (cell13107 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · have h := gap_lower (n := 13107) (a := (83618395220079 / 100000000000000 : ℝ)) (b := (39273614603 / 25000000000000 : ℝ)) (q := (2203959296249 / 100000000000000 : ℝ))
      (E := (cell13107 ⟨13, by decide⟩).energy) (xi := (323463312793413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13107 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13107]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13107])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13107) (a := (83618395220079 / 100000000000000 : ℝ)) (b := (39273614603 / 25000000000000 : ℝ)) (q := (2203959296249 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13107])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13107])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13107]

theorem cert13107_14 : CellCertificate 13107 (109457404743421 / 1250000000000000 : ℝ) (1602518826256083 / 1000000000000000000 : ℝ) (323463312793413 / 10000000000000000 : ℝ)
    (cell13107 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · have h := gap_lower (n := 13107) (a := (41791913115017 / 50000000000000 : ℝ)) (b := (39273614603 / 25000000000000 : ℝ)) (q := (2203963312871 / 100000000000000 : ℝ))
      (E := (cell13107 ⟨14, by decide⟩).energy) (xi := (323463312793413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13107 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13107]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13107])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13107) (a := (41791913115017 / 50000000000000 : ℝ)) (b := (39273614603 / 25000000000000 : ℝ)) (q := (2203963312871 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13107])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13107])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13107]

theorem cert13107_15 : CellCertificate 13107 (109457404743421 / 1250000000000000 : ℝ) (1602518826256083 / 1000000000000000000 : ℝ) (323463312793413 / 10000000000000000 : ℝ)
    (cell13107 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · have h := gap_lower (n := 13107) (a := (41774640798193 / 50000000000000 : ℝ)) (b := (39273614603 / 25000000000000 : ℝ)) (q := (440793460769 / 20000000000000 : ℝ))
      (E := (cell13107 ⟨15, by decide⟩).energy) (xi := (323463312793413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13107 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13107]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13107])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13107) (a := (41774640798193 / 50000000000000 : ℝ)) (b := (39273614603 / 25000000000000 : ℝ)) (q := (440793460769 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13107])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13107])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13107]

theorem cert13107_16 : CellCertificate 13107 (109457404743421 / 1250000000000000 : ℝ) (1602518826256083 / 1000000000000000000 : ℝ) (323463312793413 / 10000000000000000 : ℝ)
    (cell13107 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · have h := gap_lower (n := 13107) (a := (83514761285283 / 100000000000000 : ℝ)) (b := (39273614603 / 25000000000000 : ℝ)) (q := (110198566619 / 5000000000000 : ℝ))
      (E := (cell13107 ⟨16, by decide⟩).energy) (xi := (323463312793413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13107 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13107]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13107])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13107) (a := (83514761285283 / 100000000000000 : ℝ)) (b := (39273614603 / 25000000000000 : ℝ)) (q := (110198566619 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13107])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13107])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13107]

theorem cert13107_17 : CellCertificate 13107 (109457404743421 / 1250000000000000 : ℝ) (1602518826256083 / 1000000000000000000 : ℝ) (323463312793413 / 10000000000000000 : ℝ)
    (cell13107 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · have h := gap_lower (n := 13107) (a := (83480265263051 / 100000000000000 : ℝ)) (b := (39273614603 / 25000000000000 : ℝ)) (q := (1101987672521 / 50000000000000 : ℝ))
      (E := (cell13107 ⟨17, by decide⟩).energy) (xi := (323463312793413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13107 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13107]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13107])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13107) (a := (83480265263051 / 100000000000000 : ℝ)) (b := (39273614603 / 25000000000000 : ℝ)) (q := (1101987672521 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13107])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13107])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13107]

theorem cert13107_18 : CellCertificate 13107 (109457404743421 / 1250000000000000 : ℝ) (1602518826256083 / 1000000000000000000 : ℝ) (323463312793413 / 10000000000000000 : ℝ)
    (cell13107 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · have h := gap_lower (n := 13107) (a := (41722896748093 / 50000000000000 : ℝ)) (b := (39273614603 / 25000000000000 : ℝ)) (q := (440795869267 / 20000000000000 : ℝ))
      (E := (cell13107 ⟨18, by decide⟩).energy) (xi := (323463312793413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13107 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13107]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13107])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13107) (a := (41722896748093 / 50000000000000 : ℝ)) (b := (39273614603 / 25000000000000 : ℝ)) (q := (440795869267 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13107])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13107])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13107]

theorem cert13107_19 : CellCertificate 13107 (109457404743421 / 1250000000000000 : ℝ) (1602518826256083 / 1000000000000000000 : ℝ) (323463312793413 / 10000000000000000 : ℝ)
    (cell13107 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · have h := gap_lower (n := 13107) (a := (130330228049 / 156250000000 : ℝ)) (b := (39273614603 / 25000000000000 : ℝ)) (q := (440796679763 / 20000000000000 : ℝ))
      (E := (cell13107 ⟨19, by decide⟩).energy) (xi := (323463312793413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13107 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13107]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13107])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13107) (a := (130330228049 / 156250000000 : ℝ)) (b := (39273614603 / 25000000000000 : ℝ)) (q := (440796679763 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13107])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13107])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13107]

theorem cert13108_0 : CellCertificate 13108 (5472705891881 / 62500000000000 : ℝ) (801198266144381 / 500000000000000000 : ℝ) (80859517406841 / 2500000000000000 : ℝ)
    (cell13108 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · have h := gap_lower (n := 13108) (a := (84070010048641 / 100000000000000 : ℝ)) (b := (39270584063 / 25000000000000 : ℝ)) (q := (275474412501 / 12500000000000 : ℝ))
      (E := (cell13108 ⟨0, by decide⟩).energy) (xi := (80859517406841 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13108 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13108]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13108])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13108) (a := (84070010048641 / 100000000000000 : ℝ)) (b := (39270584063 / 25000000000000 : ℝ)) (q := (275474412501 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13108])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13108])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13108]

theorem cert13108_1 : CellCertificate 13108 (5472705891881 / 62500000000000 : ℝ) (801198266144381 / 500000000000000000 : ℝ) (80859517406841 / 2500000000000000 : ℝ)
    (cell13108 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · have h := gap_lower (n := 13108) (a := (84035121269557 / 100000000000000 : ℝ)) (b := (39270584063 / 25000000000000 : ℝ)) (q := (2203799287843 / 100000000000000 : ℝ))
      (E := (cell13108 ⟨1, by decide⟩).energy) (xi := (80859517406841 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13108 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13108]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13108])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13108) (a := (84035121269557 / 100000000000000 : ℝ)) (b := (39270584063 / 25000000000000 : ℝ)) (q := (2203799287843 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13108])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13108])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13108]

theorem cert13108_2 : CellCertificate 13108 (5472705891881 / 62500000000000 : ℝ) (801198266144381 / 500000000000000000 : ℝ) (80859517406841 / 2500000000000000 : ℝ)
    (cell13108 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · have h := gap_lower (n := 13108) (a := (84000257303383 / 100000000000000 : ℝ)) (b := (39270584063 / 25000000000000 : ℝ)) (q := (2203803335663 / 100000000000000 : ℝ))
      (E := (cell13108 ⟨2, by decide⟩).energy) (xi := (80859517406841 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13108 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13108]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13108])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13108) (a := (84000257303383 / 100000000000000 : ℝ)) (b := (39270584063 / 25000000000000 : ℝ)) (q := (2203803335663 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13108])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13108])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13108]

theorem cert13108_3 : CellCertificate 13108 (5472705891881 / 62500000000000 : ℝ) (801198266144381 / 500000000000000000 : ℝ) (80859517406841 / 2500000000000000 : ℝ)
    (cell13108 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · have h := gap_lower (n := 13108) (a := (83965418113887 / 100000000000000 : ℝ)) (b := (39270584063 / 25000000000000 : ℝ)) (q := (1101903668037 / 50000000000000 : ℝ))
      (E := (cell13108 ⟨3, by decide⟩).energy) (xi := (80859517406841 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13108 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13108]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13108])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13108) (a := (83965418113887 / 100000000000000 : ℝ)) (b := (39270584063 / 25000000000000 : ℝ)) (q := (1101903668037 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13108])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13108])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13108]

theorem cert13108_4 : CellCertificate 13108 (5472705891881 / 62500000000000 : ℝ) (801198266144381 / 500000000000000000 : ℝ) (80859517406841 / 2500000000000000 : ℝ)
    (cell13108 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · have h := gap_lower (n := 13108) (a := (41965301832513 / 50000000000000 : ℝ)) (b := (39270584063 / 25000000000000 : ℝ)) (q := (1101905677533 / 50000000000000 : ℝ))
      (E := (cell13108 ⟨4, by decide⟩).energy) (xi := (80859517406841 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13108 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13108]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13108])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13108) (a := (41965301832513 / 50000000000000 : ℝ)) (b := (39270584063 / 25000000000000 : ℝ)) (q := (1101905677533 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13108])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13108])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13108]

theorem cert13108_5 : CellCertificate 13108 (5472705891881 / 62500000000000 : ℝ) (801198266144381 / 500000000000000000 : ℝ) (80859517406841 / 2500000000000000 : ℝ)
    (cell13108 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · have h := gap_lower (n := 13108) (a := (83895813920947 / 100000000000000 : ℝ)) (b := (39270584063 / 25000000000000 : ℝ)) (q := (275476917817 / 12500000000000 : ℝ))
      (E := (cell13108 ⟨5, by decide⟩).energy) (xi := (80859517406841 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13108 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13108]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13108])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13108) (a := (83895813920947 / 100000000000000 : ℝ)) (b := (39270584063 / 25000000000000 : ℝ)) (q := (275476917817 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13108])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13108])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13108]

theorem cert13108_6 : CellCertificate 13108 (5472705891881 / 62500000000000 : ℝ) (801198266144381 / 500000000000000000 : ℝ) (80859517406841 / 2500000000000000 : ℝ)
    (cell13108 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · have h := gap_lower (n := 13108) (a := (2620657776437 / 3125000000000 : ℝ)) (b := (39270584063 / 25000000000000 : ℝ)) (q := (1101909682007 / 50000000000000 : ℝ))
      (E := (cell13108 ⟨6, by decide⟩).energy) (xi := (80859517406841 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13108 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13108]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13108])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13108) (a := (2620657776437 / 3125000000000 : ℝ)) (b := (39270584063 / 25000000000000 : ℝ)) (q := (1101909682007 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13108])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13108])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13108]

theorem cert13108_7 : CellCertificate 13108 (5472705891881 / 62500000000000 : ℝ) (801198266144381 / 500000000000000000 : ℝ) (80859517406841 / 2500000000000000 : ℝ)
    (cell13108 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · have h := gap_lower (n := 13108) (a := (4191315420233 / 5000000000000 : ℝ)) (b := (39270584063 / 25000000000000 : ℝ)) (q := (1101911684419 / 50000000000000 : ℝ))
      (E := (cell13108 ⟨7, by decide⟩).energy) (xi := (80859517406841 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13108 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13108]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13108])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13108) (a := (4191315420233 / 5000000000000 : ℝ)) (b := (39270584063 / 25000000000000 : ℝ)) (q := (1101911684419 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13108])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13108])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13108]

theorem cert13108_8 : CellCertificate 13108 (5472705891881 / 62500000000000 : ℝ) (801198266144381 / 500000000000000000 : ℝ) (80859517406841 / 2500000000000000 : ℝ)
    (cell13108 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · have h := gap_lower (n := 13108) (a := (41895796280841 / 50000000000000 : ℝ)) (b := (39270584063 / 25000000000000 : ℝ)) (q := (2203827364043 / 100000000000000 : ℝ))
      (E := (cell13108 ⟨8, by decide⟩).energy) (xi := (80859517406841 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13108 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13108]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13108])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13108) (a := (41895796280841 / 50000000000000 : ℝ)) (b := (39270584063 / 25000000000000 : ℝ)) (q := (2203827364043 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13108])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13108])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13108]

theorem cert13108_9 : CellCertificate 13108 (5472705891881 / 62500000000000 : ℝ) (801198266144381 / 500000000000000000 : ℝ) (80859517406841 / 2500000000000000 : ℝ)
    (cell13108 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · have h := gap_lower (n := 13108) (a := (83756901281941 / 100000000000000 : ℝ)) (b := (39270584063 / 25000000000000 : ℝ)) (q := (220383141447 / 10000000000000 : ℝ))
      (E := (cell13108 ⟨9, by decide⟩).energy) (xi := (80859517406841 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13108 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13108]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13108])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13108) (a := (83756901281941 / 100000000000000 : ℝ)) (b := (39270584063 / 25000000000000 : ℝ)) (q := (220383141447 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13108])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13108])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13108]

theorem cert13108_10 : CellCertificate 13108 (5472705891881 / 62500000000000 : ℝ) (801198266144381 / 500000000000000000 : ℝ) (80859517406841 / 2500000000000000 : ℝ)
    (cell13108 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · have h := gap_lower (n := 13108) (a := (5232639658157 / 6250000000000 : ℝ)) (b := (39270584063 / 25000000000000 : ℝ)) (q := (1101917705277 / 50000000000000 : ℝ))
      (E := (cell13108 ⟨10, by decide⟩).energy) (xi := (80859517406841 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13108 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13108]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13108])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13108) (a := (5232639658157 / 6250000000000 : ℝ)) (b := (39270584063 / 25000000000000 : ℝ)) (q := (1101917705277 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13108])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13108])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13108]

theorem cert13108_11 : CellCertificate 13108 (5472705891881 / 62500000000000 : ℝ) (801198266144381 / 500000000000000000 : ℝ) (80859517406841 / 2500000000000000 : ℝ)
    (cell13108 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · have h := gap_lower (n := 13108) (a := (20921898068163 / 25000000000000 : ℝ)) (b := (39270584063 / 25000000000000 : ℝ)) (q := (440767883323 / 20000000000000 : ℝ))
      (E := (cell13108 ⟨11, by decide⟩).energy) (xi := (80859517406841 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13108 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13108]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13108])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13108) (a := (20921898068163 / 25000000000000 : ℝ)) (b := (39270584063 / 25000000000000 : ℝ)) (q := (440767883323 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13108])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13108])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13108]

theorem cert13108_12 : CellCertificate 13108 (5472705891881 / 62500000000000 : ℝ) (801198266144381 / 500000000000000000 : ℝ) (80859517406841 / 2500000000000000 : ℝ)
    (cell13108 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · have h := gap_lower (n := 13108) (a := (83652974473797 / 100000000000000 : ℝ)) (b := (39270584063 / 25000000000000 : ℝ)) (q := (2203843438689 / 100000000000000 : ℝ))
      (E := (cell13108 ⟨12, by decide⟩).energy) (xi := (80859517406841 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13108 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13108]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13108])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13108) (a := (83652974473797 / 100000000000000 : ℝ)) (b := (39270584063 / 25000000000000 : ℝ)) (q := (2203843438689 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13108])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13108])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13108]

theorem cert13108_13 : CellCertificate 13108 (5472705891881 / 62500000000000 : ℝ) (801198266144381 / 500000000000000000 : ℝ) (80859517406841 / 2500000000000000 : ℝ)
    (cell13108 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · have h := gap_lower (n := 13108) (a := (41809190549783 / 50000000000000 : ℝ)) (b := (39270584063 / 25000000000000 : ℝ)) (q := (2203847424411 / 100000000000000 : ℝ))
      (E := (cell13108 ⟨13, by decide⟩).energy) (xi := (80859517406841 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13108 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13108]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13108])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13108) (a := (41809190549783 / 50000000000000 : ℝ)) (b := (39270584063 / 25000000000000 : ℝ)) (q := (2203847424411 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13108])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13108])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13108]

theorem cert13108_14 : CellCertificate 13108 (5472705891881 / 62500000000000 : ℝ) (801198266144381 / 500000000000000000 : ℝ) (80859517406841 / 2500000000000000 : ℝ)
    (cell13108 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · have h := gap_lower (n := 13108) (a := (83583812115753 / 100000000000000 : ℝ)) (b := (39270584063 / 25000000000000 : ℝ)) (q := (275481429679 / 12500000000000 : ℝ))
      (E := (cell13108 ⟨14, by decide⟩).energy) (xi := (80859517406841 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13108 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13108]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13108])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13108) (a := (83583812115753 / 100000000000000 : ℝ)) (b := (39270584063 / 25000000000000 : ℝ)) (q := (275481429679 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13108])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13108])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13108]

theorem cert13108_15 : CellCertificate 13108 (5472705891881 / 62500000000000 : ℝ) (801198266144381 / 500000000000000000 : ℝ) (80859517406841 / 2500000000000000 : ℝ)
    (cell13108 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · have h := gap_lower (n := 13108) (a := (20887316872083 / 25000000000000 : ℝ)) (b := (39270584063 / 25000000000000 : ℝ)) (q := (2203855483051 / 100000000000000 : ℝ))
      (E := (cell13108 ⟨15, by decide⟩).energy) (xi := (80859517406841 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13108 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13108]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13108])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13108) (a := (20887316872083 / 25000000000000 : ℝ)) (b := (39270584063 / 25000000000000 : ℝ)) (q := (2203855483051 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13108])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13108])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13108]

theorem cert13108_16 : CellCertificate 13108 (5472705891881 / 62500000000000 : ℝ) (801198266144381 / 500000000000000000 : ℝ) (80859517406841 / 2500000000000000 : ℝ)
    (cell13108 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · have h := gap_lower (n := 13108) (a := (83514747183451 / 100000000000000 : ℝ)) (b := (39270584063 / 25000000000000 : ℝ)) (q := (550964862469 / 25000000000000 : ℝ))
      (E := (cell13108 ⟨16, by decide⟩).energy) (xi := (80859517406841 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13108 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13108]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13108])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13108) (a := (83514747183451 / 100000000000000 : ℝ)) (b := (39270584063 / 25000000000000 : ℝ)) (q := (550964862469 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13108])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13108])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13108]

theorem cert13108_17 : CellCertificate 13108 (5472705891881 / 62500000000000 : ℝ) (801198266144381 / 500000000000000000 : ℝ) (80859517406841 / 2500000000000000 : ℝ)
    (cell13108 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · have h := gap_lower (n := 13108) (a := (41740125583717 / 50000000000000 : ℝ)) (b := (39270584063 / 25000000000000 : ℝ)) (q := (2203863459077 / 100000000000000 : ℝ))
      (E := (cell13108 ⟨17, by decide⟩).energy) (xi := (80859517406841 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13108 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13108]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13108])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13108) (a := (41740125583717 / 50000000000000 : ℝ)) (b := (39270584063 / 25000000000000 : ℝ)) (q := (2203863459077 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13108])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13108])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13108]

theorem cert13108_18 : CellCertificate 13108 (5472705891881 / 62500000000000 : ℝ) (801198266144381 / 500000000000000000 : ℝ) (80859517406841 / 2500000000000000 : ℝ)
    (cell13108 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · have h := gap_lower (n := 13108) (a := (4172288970339 / 5000000000000 : ℝ)) (b := (39270584063 / 25000000000000 : ℝ)) (q := (1101933757613 / 50000000000000 : ℝ))
      (E := (cell13108 ⟨18, by decide⟩).energy) (xi := (80859517406841 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13108 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13108]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13108])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13108) (a := (4172288970339 / 5000000000000 : ℝ)) (b := (39270584063 / 25000000000000 : ℝ)) (q := (1101933757613 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13108])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13108])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13108]

theorem cert13108_19 : CellCertificate 13108 (5472705891881 / 62500000000000 : ℝ) (801198266144381 / 500000000000000000 : ℝ) (80859517406841 / 2500000000000000 : ℝ)
    (cell13108 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · have h := gap_lower (n := 13108) (a := (83411331868159 / 100000000000000 : ℝ)) (b := (39270584063 / 25000000000000 : ℝ)) (q := (2203871506067 / 100000000000000 : ℝ))
      (E := (cell13108 ⟨19, by decide⟩).energy) (xi := (80859517406841 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13108 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13108]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13108])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13108) (a := (83411331868159 / 100000000000000 : ℝ)) (b := (39270584063 / 25000000000000 : ℝ)) (q := (2203871506067 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13108])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13108])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13108]

theorem cert13109_0 : CellCertificate 13109 (109450831411819 / 1250000000000000 : ℝ) (1602274256985399 / 1000000000000000000 : ℝ) (323412830429257 / 10000000000000000 : ℝ)
    (cell13109 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · have h := gap_lower (n := 13109) (a := (42034997924387 / 50000000000000 : ℝ)) (b := (15707021597 / 10000000000000 : ℝ)) (q := (1101841708569 / 50000000000000 : ℝ))
      (E := (cell13109 ⟨0, by decide⟩).energy) (xi := (323412830429257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13109 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13109]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13109])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13109) (a := (42034997924387 / 50000000000000 : ℝ)) (b := (15707021597 / 10000000000000 : ℝ)) (q := (1101841708569 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13109])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13109])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13109]

theorem cert13109_1 : CellCertificate 13109 (109450831411819 / 1250000000000000 : ℝ) (1602274256985399 / 1000000000000000000 : ℝ) (323412830429257 / 10000000000000000 : ℝ)
    (cell13109 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · have h := gap_lower (n := 13109) (a := (42017553537997 / 50000000000000 : ℝ)) (b := (15707021597 / 10000000000000 : ℝ)) (q := (2203687458613 / 100000000000000 : ℝ))
      (E := (cell13109 ⟨1, by decide⟩).energy) (xi := (323412830429257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13109 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13109]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13109])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13109) (a := (42017553537997 / 50000000000000 : ℝ)) (b := (15707021597 / 10000000000000 : ℝ)) (q := (2203687458613 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13109])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13109])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13109]

theorem cert13109_2 : CellCertificate 13109 (109450831411819 / 1250000000000000 : ℝ) (1602274256985399 / 1000000000000000000 : ℝ) (323412830429257 / 10000000000000000 : ℝ)
    (cell13109 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · have h := gap_lower (n := 13109) (a := (84000243116119 / 100000000000000 : ℝ)) (b := (15707021597 / 10000000000000 : ℝ)) (q := (550922861093 / 25000000000000 : ℝ))
      (E := (cell13109 ⟨2, by decide⟩).energy) (xi := (323412830429257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13109 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13109]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13109])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13109) (a := (84000243116119 / 100000000000000 : ℝ)) (b := (15707021597 / 10000000000000 : ℝ)) (q := (550922861093 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13109])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13109])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13109]

theorem cert13109_3 : CellCertificate 13109 (109450831411819 / 1250000000000000 : ℝ) (1602274256985399 / 1000000000000000000 : ℝ) (323412830429257 / 10000000000000000 : ℝ)
    (cell13109 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · have h := gap_lower (n := 13109) (a := (16793080786583 / 20000000000000 : ℝ)) (b := (15707021597 / 10000000000000 : ℝ)) (q := (2203695498563 / 100000000000000 : ℝ))
      (E := (cell13109 ⟨3, by decide⟩).energy) (xi := (323412830429257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13109 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13109]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13109])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13109) (a := (16793080786583 / 20000000000000 : ℝ)) (b := (15707021597 / 10000000000000 : ℝ)) (q := (2203695498563 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13109])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13109])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13109]

theorem cert13109_4 : CellCertificate 13109 (109450831411819 / 1250000000000000 : ℝ) (1602274256985399 / 1000000000000000000 : ℝ) (323412830429257 / 10000000000000000 : ℝ)
    (cell13109 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · have h := gap_lower (n := 13109) (a := (4196529474517 / 5000000000000 : ℝ)) (b := (15707021597 / 10000000000000 : ℝ)) (q := (1101849756743 / 50000000000000 : ℝ))
      (E := (cell13109 ⟨4, by decide⟩).energy) (xi := (323412830429257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13109 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13109]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13109])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13109) (a := (4196529474517 / 5000000000000 : ℝ)) (b := (15707021597 / 10000000000000 : ℝ)) (q := (1101849756743 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13109])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13109])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13109]

theorem cert13109_5 : CellCertificate 13109 (109450831411819 / 1250000000000000 : ℝ) (1602274256985399 / 1000000000000000000 : ℝ) (323412830429257 / 10000000000000000 : ℝ)
    (cell13109 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · have h := gap_lower (n := 13109) (a := (41947899876271 / 50000000000000 : ℝ)) (b := (15707021597 / 10000000000000 : ℝ)) (q := (1101851748467 / 50000000000000 : ℝ))
      (E := (cell13109 ⟨5, by decide⟩).energy) (xi := (323412830429257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13109 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13109]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13109])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13109) (a := (41947899876271 / 50000000000000 : ℝ)) (b := (15707021597 / 10000000000000 : ℝ)) (q := (1101851748467 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13109])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13109])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13109]

theorem cert13109_6 : CellCertificate 13109 (109450831411819 / 1250000000000000 : ℝ) (1602274256985399 / 1000000000000000000 : ℝ) (323412830429257 / 10000000000000000 : ℝ)
    (cell13109 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · have h := gap_lower (n := 13109) (a := (16772206936771 / 20000000000000 : ℝ)) (b := (15707021597 / 10000000000000 : ℝ)) (q := (440741502887 / 20000000000000 : ℝ))
      (E := (cell13109 ⟨6, by decide⟩).energy) (xi := (323412830429257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13109 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13109]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13109])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13109) (a := (16772206936771 / 20000000000000 : ℝ)) (b := (15707021597 / 10000000000000 : ℝ)) (q := (440741502887 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13109])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13109])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13109]

theorem cert13109_7 : CellCertificate 13109 (109450831411819 / 1250000000000000 : ℝ) (1602274256985399 / 1000000000000000000 : ℝ) (323412830429257 / 10000000000000000 : ℝ)
    (cell13109 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · have h := gap_lower (n := 13109) (a := (83826294248801 / 100000000000000 : ℝ)) (b := (15707021597 / 10000000000000 : ℝ)) (q := (2203711515331 / 100000000000000 : ℝ))
      (E := (cell13109 ⟨7, by decide⟩).energy) (xi := (323412830429257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13109 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13109]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13109])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13109) (a := (83826294248801 / 100000000000000 : ℝ)) (b := (15707021597 / 10000000000000 : ℝ)) (q := (2203711515331 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13109])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13109])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13109]

theorem cert13109_8 : CellCertificate 13109 (109450831411819 / 1250000000000000 : ℝ) (1602274256985399 / 1000000000000000000 : ℝ) (323412830429257 / 10000000000000000 : ℝ)
    (cell13109 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · have h := gap_lower (n := 13109) (a := (83791578412087 / 100000000000000 : ℝ)) (b := (15707021597 / 10000000000000 : ℝ)) (q := (1101857753327 / 50000000000000 : ℝ))
      (E := (cell13109 ⟨8, by decide⟩).energy) (xi := (323412830429257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13109 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13109]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13109])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13109) (a := (83791578412087 / 100000000000000 : ℝ)) (b := (15707021597 / 10000000000000 : ℝ)) (q := (1101857753327 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13109])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13109])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13109]

theorem cert13109_9 : CellCertificate 13109 (109450831411819 / 1250000000000000 : ℝ) (1602274256985399 / 1000000000000000000 : ℝ) (323412830429257 / 10000000000000000 : ℝ)
    (cell13109 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · have h := gap_lower (n := 13109) (a := (16751377427721 / 20000000000000 : ℝ)) (b := (15707021597 / 10000000000000 : ℝ)) (q := (1101859776623 / 50000000000000 : ℝ))
      (E := (cell13109 ⟨9, by decide⟩).energy) (xi := (323412830429257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13109 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13109]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13109])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13109) (a := (16751377427721 / 20000000000000 : ℝ)) (b := (15707021597 / 10000000000000 : ℝ)) (q := (1101859776623 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13109])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13109])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13109]

theorem cert13109_10 : CellCertificate 13109 (109450831411819 / 1250000000000000 : ℝ) (1602274256985399 / 1000000000000000000 : ℝ) (323412830429257 / 10000000000000000 : ℝ)
    (cell13109 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · have h := gap_lower (n := 13109) (a := (8372222039343 / 10000000000000 : ℝ)) (b := (15707021597 / 10000000000000 : ℝ)) (q := (1101861772771 / 50000000000000 : ℝ))
      (E := (cell13109 ⟨10, by decide⟩).energy) (xi := (323412830429257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13109 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13109]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13109])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13109) (a := (8372222039343 / 10000000000000 : ℝ)) (b := (15707021597 / 10000000000000 : ℝ)) (q := (1101861772771 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13109])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13109])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13109]

theorem cert13109_11 : CellCertificate 13109 (109450831411819 / 1250000000000000 : ℝ) (1602274256985399 / 1000000000000000000 : ℝ) (323412830429257 / 10000000000000000 : ℝ)
    (cell13109 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · have h := gap_lower (n := 13109) (a := (83687578141817 / 100000000000000 : ℝ)) (b := (15707021597 / 10000000000000 : ℝ)) (q := (1101863773931 / 50000000000000 : ℝ))
      (E := (cell13109 ⟨11, by decide⟩).energy) (xi := (323412830429257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13109 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13109]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13109])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13109) (a := (83687578141817 / 100000000000000 : ℝ)) (b := (15707021597 / 10000000000000 : ℝ)) (q := (1101863773931 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13109])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13109])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13109]

theorem cert13109_12 : CellCertificate 13109 (109450831411819 / 1250000000000000 : ℝ) (1602274256985399 / 1000000000000000000 : ℝ) (323412830429257 / 10000000000000000 : ℝ)
    (cell13109 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · have h := gap_lower (n := 13109) (a := (16730592069841 / 20000000000000 : ℝ)) (b := (15707021597 / 10000000000000 : ℝ)) (q := (1101865783121 / 50000000000000 : ℝ))
      (E := (cell13109 ⟨12, by decide⟩).energy) (xi := (323412830429257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13109 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13109]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13109])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13109) (a := (16730592069841 / 20000000000000 : ℝ)) (b := (15707021597 / 10000000000000 : ℝ)) (q := (1101865783121 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13109])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13109])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13109]

theorem cert13109_13 : CellCertificate 13109 (109450831411819 / 1250000000000000 : ℝ) (1602274256985399 / 1000000000000000000 : ℝ) (323412830429257 / 10000000000000000 : ℝ)
    (cell13109 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · have h := gap_lower (n := 13109) (a := (8361836698121 / 10000000000000 : ℝ)) (b := (15707021597 / 10000000000000 : ℝ)) (q := (220373560647 / 10000000000000 : ℝ))
      (E := (cell13109 ⟨13, by decide⟩).energy) (xi := (323412830429257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13109 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13109]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13109])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13109) (a := (8361836698121 / 10000000000000 : ℝ)) (b := (15707021597 / 10000000000000 : ℝ)) (q := (220373560647 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13109])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13109])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13109]

theorem cert13109_14 : CellCertificate 13109 (109450831411819 / 1250000000000000 : ℝ) (1602274256985399 / 1000000000000000000 : ℝ) (323412830429257 / 10000000000000000 : ℝ)
    (cell13109 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · have h := gap_lower (n := 13109) (a := (83583798003629 / 100000000000000 : ℝ)) (b := (15707021597 / 10000000000000 : ℝ)) (q := (2203739615913 / 100000000000000 : ℝ))
      (E := (cell13109 ⟨14, by decide⟩).energy) (xi := (323412830429257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13109 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13109]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13109])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13109) (a := (83583798003629 / 100000000000000 : ℝ)) (b := (15707021597 / 10000000000000 : ℝ)) (q := (2203739615913 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13109])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13109])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13109]

theorem cert13109_15 : CellCertificate 13109 (109450831411819 / 1250000000000000 : ℝ) (1602274256985399 / 1000000000000000000 : ℝ) (323412830429257 / 10000000000000000 : ℝ)
    (cell13109 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · have h := gap_lower (n := 13109) (a := (83549253382433 / 100000000000000 : ℝ)) (b := (15707021597 / 10000000000000 : ℝ)) (q := (2203743599801 / 100000000000000 : ℝ))
      (E := (cell13109 ⟨15, by decide⟩).energy) (xi := (323412830429257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13109 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13109]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13109])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13109) (a := (83549253382433 / 100000000000000 : ℝ)) (b := (15707021597 / 10000000000000 : ℝ)) (q := (2203743599801 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13109])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13109])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13109]

theorem cert13109_16 : CellCertificate 13109 (109450831411819 / 1250000000000000 : ℝ) (1602274256985399 / 1000000000000000000 : ℝ) (323412830429257 / 10000000000000000 : ℝ)
    (cell13109 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · have h := gap_lower (n := 13109) (a := (20878683270943 / 25000000000000 : ℝ)) (b := (15707021597 / 10000000000000 : ℝ)) (q := (2203747621343 / 100000000000000 : ℝ))
      (E := (cell13109 ⟨16, by decide⟩).energy) (xi := (323412830429257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13109 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13109]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13109])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13109) (a := (20878683270943 / 25000000000000 : ℝ)) (b := (15707021597 / 10000000000000 : ℝ)) (q := (2203747621343 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13109])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13109])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13109]

theorem cert13109_17 : CellCertificate 13109 (109450831411819 / 1250000000000000 : ℝ) (1602274256985399 / 1000000000000000000 : ℝ) (323412830429257 / 10000000000000000 : ℝ)
    (cell13109 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · have h := gap_lower (n := 13109) (a := (83480237073971 / 100000000000000 : ℝ)) (b := (15707021597 / 10000000000000 : ℝ)) (q := (1101875813553 / 50000000000000 : ℝ))
      (E := (cell13109 ⟨17, by decide⟩).energy) (xi := (323412830429257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13109 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13109]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13109])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13109) (a := (83480237073971 / 100000000000000 : ℝ)) (b := (15707021597 / 10000000000000 : ℝ)) (q := (1101875813553 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13109])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13109])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13109]

theorem cert13109_18 : CellCertificate 13109 (109450831411819 / 1250000000000000 : ℝ) (1602274256985399 / 1000000000000000000 : ℝ) (323412830429257 / 10000000000000000 : ℝ)
    (cell13109 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · have h := gap_lower (n := 13109) (a := (41722882659763 / 50000000000000 : ℝ)) (b := (15707021597 / 10000000000000 : ℝ)) (q := (1101877810797 / 50000000000000 : ℝ))
      (E := (cell13109 ⟨18, by decide⟩).energy) (xi := (323412830429257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13109 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13109]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13109])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13109) (a := (41722882659763 / 50000000000000 : ℝ)) (b := (15707021597 / 10000000000000 : ℝ)) (q := (1101877810797 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13109])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13109])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13109]

theorem cert13109_19 : CellCertificate 13109 (109450831411819 / 1250000000000000 : ℝ) (1602274256985399 / 1000000000000000000 : ℝ) (323412830429257 / 10000000000000000 : ℝ)
    (cell13109 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · have h := gap_lower (n := 13109) (a := (83411317787109 / 100000000000000 : ℝ)) (b := (15707021597 / 10000000000000 : ℝ)) (q := (1101879833681 / 50000000000000 : ℝ))
      (E := (cell13109 ⟨19, by decide⟩).energy) (xi := (323412830429257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13109 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13109]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13109])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13109) (a := (83411317787109 / 100000000000000 : ℝ)) (b := (15707021597 / 10000000000000 : ℝ)) (q := (1101879833681 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13109])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13109])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13109]

theorem cert13110_0 : CellCertificate 13110 (875580363727263 / 10000000000000000 : ℝ) (801076000170861 / 500000000000000000 : ℝ) (161693797599053 / 5000000000000000 : ℝ)
    (cell13110 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · have h := gap_lower (n := 13110) (a := (21017495412769 / 25000000000000 : ℝ)) (b := (31411619513 / 20000000000000 : ℝ)) (q := (550892896963 / 25000000000000 : ℝ))
      (E := (cell13110 ⟨0, by decide⟩).energy) (xi := (161693797599053 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13110 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13110]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13110])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13110) (a := (21017495412769 / 25000000000000 : ℝ)) (b := (31411619513 / 20000000000000 : ℝ)) (q := (550892896963 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13110])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13110])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13110]

theorem cert13110_1 : CellCertificate 13110 (875580363727263 / 10000000000000000 : ℝ) (801076000170861 / 500000000000000000 : ℝ) (161693797599053 / 5000000000000000 : ℝ)
    (cell13110 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · have h := gap_lower (n := 13110) (a := (84035092884599 / 100000000000000 : ℝ)) (b := (31411619513 / 20000000000000 : ℝ)) (q := (550893906279 / 25000000000000 : ℝ))
      (E := (cell13110 ⟨1, by decide⟩).energy) (xi := (161693797599053 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13110 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13110]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13110])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13110) (a := (84035092884599 / 100000000000000 : ℝ)) (b := (31411619513 / 20000000000000 : ℝ)) (q := (550893906279 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13110])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13110])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13110]

theorem cert13110_2 : CellCertificate 13110 (875580363727263 / 10000000000000000 : ℝ) (801076000170861 / 500000000000000000 : ℝ) (161693797599053 / 5000000000000000 : ℝ)
    (cell13110 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · have h := gap_lower (n := 13110) (a := (84000228931021 / 100000000000000 : ℝ)) (b := (31411619513 / 20000000000000 : ℝ)) (q := (2203579606713 / 100000000000000 : ℝ))
      (E := (cell13110 ⟨2, by decide⟩).energy) (xi := (161693797599053 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13110 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13110]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13110])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13110) (a := (84000228931021 / 100000000000000 : ℝ)) (b := (31411619513 / 20000000000000 : ℝ)) (q := (2203579606713 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13110])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13110])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13110]

theorem cert13110_3 : CellCertificate 13110 (875580363727263 / 10000000000000000 : ℝ) (801076000170861 / 500000000000000000 : ℝ) (161693797599053 / 5000000000000000 : ℝ)
    (cell13110 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · have h := gap_lower (n := 13110) (a := (83965389754109 / 100000000000000 : ℝ)) (b := (31411619513 / 20000000000000 : ℝ)) (q := (550895914197 / 25000000000000 : ℝ))
      (E := (cell13110 ⟨3, by decide⟩).energy) (xi := (161693797599053 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13110 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13110]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13110])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13110) (a := (83965389754109 / 100000000000000 : ℝ)) (b := (31411619513 / 20000000000000 : ℝ)) (q := (550895914197 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13110])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13110])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13110]

theorem cert13110_4 : CellCertificate 13110 (875580363727263 / 10000000000000000 : ℝ) (801076000170861 / 500000000000000000 : ℝ) (161693797599053 / 5000000000000000 : ℝ)
    (cell13110 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · have h := gap_lower (n := 13110) (a := (4196528765891 / 5000000000000 : ℝ)) (b := (31411619513 / 20000000000000 : ℝ)) (q := (1101793833821 / 50000000000000 : ℝ))
      (E := (cell13110 ⟨4, by decide⟩).energy) (xi := (161693797599053 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13110 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13110]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13110])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13110) (a := (4196528765891 / 5000000000000 : ℝ)) (b := (31411619513 / 20000000000000 : ℝ)) (q := (1101793833821 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13110])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13110])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13110]

theorem cert13110_5 : CellCertificate 13110 (875580363727263 / 10000000000000000 : ℝ) (801076000170861 / 500000000000000000 : ℝ) (161693797599053 / 5000000000000000 : ℝ)
    (cell13110 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · have h := gap_lower (n := 13110) (a := (41947892793151 / 50000000000000 : ℝ)) (b := (31411619513 / 20000000000000 : ℝ)) (q := (2203591647069 / 100000000000000 : ℝ))
      (E := (cell13110 ⟨5, by decide⟩).energy) (xi := (161693797599053 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13110 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13110]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13110])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13110) (a := (41947892793151 / 50000000000000 : ℝ)) (b := (31411619513 / 20000000000000 : ℝ)) (q := (2203591647069 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13110])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13110])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13110]

theorem cert13110_6 : CellCertificate 13110 (875580363727263 / 10000000000000000 : ℝ) (801076000170861 / 500000000000000000 : ℝ) (161693797599053 / 5000000000000000 : ℝ)
    (cell13110 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · have h := gap_lower (n := 13110) (a := (8386102052389 / 10000000000000 : ℝ)) (b := (31411619513 / 20000000000000 : ℝ)) (q := (440719132119 / 20000000000000 : ℝ))
      (E := (cell13110 ⟨6, by decide⟩).energy) (xi := (161693797599053 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13110 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13110]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13110])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13110) (a := (8386102052389 / 10000000000000 : ℝ)) (b := (31411619513 / 20000000000000 : ℝ)) (q := (440719132119 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13110])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13110])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13110]

theorem cert13110_7 : CellCertificate 13110 (875580363727263 / 10000000000000000 : ℝ) (801076000170861 / 500000000000000000 : ℝ) (161693797599053 / 5000000000000000 : ℝ)
    (cell13110 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · have h := gap_lower (n := 13110) (a := (16765256019021 / 20000000000000 : ℝ)) (b := (31411619513 / 20000000000000 : ℝ)) (q := (275449964447 / 12500000000000 : ℝ))
      (E := (cell13110 ⟨7, by decide⟩).energy) (xi := (161693797599053 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13110 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13110]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13110])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13110) (a := (16765256019021 / 20000000000000 : ℝ)) (b := (31411619513 / 20000000000000 : ℝ)) (q := (275449964447 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13110])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13110])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13110]

theorem cert13110_8 : CellCertificate 13110 (875580363727263 / 10000000000000000 : ℝ) (801076000170861 / 500000000000000000 : ℝ) (161693797599053 / 5000000000000000 : ℝ)
    (cell13110 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · have h := gap_lower (n := 13110) (a := (41895782132327 / 50000000000000 : ℝ)) (b := (31411619513 / 20000000000000 : ℝ)) (q := (1101801851521 / 50000000000000 : ℝ))
      (E := (cell13110 ⟨8, by decide⟩).energy) (xi := (161693797599053 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13110 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13110]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13110])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13110) (a := (41895782132327 / 50000000000000 : ℝ)) (b := (31411619513 / 20000000000000 : ℝ)) (q := (1101801851521 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13110])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13110])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13110]

theorem cert13110_9 : CellCertificate 13110 (875580363727263 / 10000000000000000 : ℝ) (801076000170861 / 500000000000000000 : ℝ) (161693797599053 / 5000000000000000 : ℝ)
    (cell13110 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · have h := gap_lower (n := 13110) (a := (8375687299743 / 10000000000000 : ℝ)) (b := (31411619513 / 20000000000000 : ℝ)) (q := (2203607687763 / 100000000000000 : ℝ))
      (E := (cell13110 ⟨9, by decide⟩).energy) (xi := (161693797599053 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13110 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13110]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13110])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13110) (a := (8375687299743 / 10000000000000 : ℝ)) (b := (31411619513 / 20000000000000 : ℝ)) (q := (2203607687763 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13110])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13110])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13110]

theorem cert13110_10 : CellCertificate 13110 (875580363727263 / 10000000000000000 : ℝ) (801076000170861 / 500000000000000000 : ℝ) (161693797599053 / 5000000000000000 : ℝ)
    (cell13110 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · have h := gap_lower (n := 13110) (a := (83722206258507 / 100000000000000 : ℝ)) (b := (31411619513 / 20000000000000 : ℝ)) (q := (550902933589 / 25000000000000 : ℝ))
      (E := (cell13110 ⟨10, by decide⟩).energy) (xi := (161693797599053 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13110 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13110]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13110])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13110) (a := (83722206258507 / 100000000000000 : ℝ)) (b := (31411619513 / 20000000000000 : ℝ)) (q := (550902933589 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13110])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13110])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13110]

theorem cert13110_11 : CellCertificate 13110 (875580363727263 / 10000000000000000 : ℝ) (801076000170861 / 500000000000000000 : ℝ) (161693797599053 / 5000000000000000 : ℝ)
    (cell13110 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · have h := gap_lower (n := 13110) (a := (83687564013141 / 100000000000000 : ℝ)) (b := (31411619513 / 20000000000000 : ℝ)) (q := (2203615732959 / 100000000000000 : ℝ))
      (E := (cell13110 ⟨11, by decide⟩).energy) (xi := (161693797599053 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13110 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13110]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13110])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13110) (a := (83687564013141 / 100000000000000 : ℝ)) (b := (31411619513 / 20000000000000 : ℝ)) (q := (2203615732959 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13110])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13110])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13110]

theorem cert13110_12 : CellCertificate 13110 (875580363727263 / 10000000000000000 : ℝ) (801076000170861 / 500000000000000000 : ℝ) (161693797599053 / 5000000000000000 : ℝ)
    (cell13110 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · have h := gap_lower (n := 13110) (a := (8365294622677 / 10000000000000 : ℝ)) (b := (31411619513 / 20000000000000 : ℝ)) (q := (550904936917 / 25000000000000 : ℝ))
      (E := (cell13110 ⟨12, by decide⟩).energy) (xi := (161693797599053 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13110 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13110]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13110])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13110) (a := (8365294622677 / 10000000000000 : ℝ)) (b := (31411619513 / 20000000000000 : ℝ)) (q := (550904936917 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13110])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13110])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13110]

theorem cert13110_13 : CellCertificate 13110 (875580363727263 / 10000000000000000 : ℝ) (801076000170861 / 500000000000000000 : ℝ) (161693797599053 / 5000000000000000 : ℝ)
    (cell13110 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · have h := gap_lower (n := 13110) (a := (83618352865011 / 100000000000000 : ℝ)) (b := (31411619513 / 20000000000000 : ℝ)) (q := (2203623784273 / 100000000000000 : ℝ))
      (E := (cell13110 ⟨13, by decide⟩).energy) (xi := (161693797599053 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13110 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13110]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13110])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13110) (a := (83618352865011 / 100000000000000 : ℝ)) (b := (31411619513 / 20000000000000 : ℝ)) (q := (2203623784273 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13110])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13110])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13110]

theorem cert13110_14 : CellCertificate 13110 (875580363727263 / 10000000000000000 : ℝ) (801076000170861 / 500000000000000000 : ℝ) (161693797599053 / 5000000000000000 : ℝ)
    (cell13110 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · have h := gap_lower (n := 13110) (a := (4179189194683 / 5000000000000 : ℝ)) (b := (31411619513 / 20000000000000 : ℝ)) (q := (110181389507 / 5000000000000 : ℝ))
      (E := (cell13110 ⟨14, by decide⟩).energy) (xi := (161693797599053 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13110 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13110]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13110])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13110) (a := (4179189194683 / 5000000000000 : ℝ)) (b := (31411619513 / 20000000000000 : ℝ)) (q := (110181389507 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13110])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13110])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13110]

theorem cert13110_15 : CellCertificate 13110 (875580363727263 / 10000000000000000 : ℝ) (801076000170861 / 500000000000000000 : ℝ) (161693797599053 / 5000000000000000 : ℝ)
    (cell13110 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · have h := gap_lower (n := 13110) (a := (83549239278689 / 100000000000000 : ℝ)) (b := (31411619513 / 20000000000000 : ℝ)) (q := (1101815885249 / 50000000000000 : ℝ))
      (E := (cell13110 ⟨15, by decide⟩).energy) (xi := (161693797599053 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13110 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13110]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13110])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13110) (a := (83549239278689 / 100000000000000 : ℝ)) (b := (31411619513 / 20000000000000 : ℝ)) (q := (1101815885249 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13110])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13110])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13110]

theorem cert13110_16 : CellCertificate 13110 (875580363727263 / 10000000000000000 : ℝ) (801076000170861 / 500000000000000000 : ℝ) (161693797599053 / 5000000000000000 : ℝ)
    (cell13110 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · have h := gap_lower (n := 13110) (a := (10439339873281 / 12500000000000 : ℝ)) (b := (31411619513 / 20000000000000 : ℝ)) (q := (550908947139 / 25000000000000 : ℝ))
      (E := (cell13110 ⟨16, by decide⟩).energy) (xi := (161693797599053 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13110 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13110]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13110])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13110) (a := (10439339873281 / 12500000000000 : ℝ)) (b := (31411619513 / 20000000000000 : ℝ)) (q := (550908947139 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13110])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13110])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13110]

theorem cert13110_17 : CellCertificate 13110 (875580363727263 / 10000000000000000 : ℝ) (801076000170861 / 500000000000000000 : ℝ) (161693797599053 / 5000000000000000 : ℝ)
    (cell13110 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · have h := gap_lower (n := 13110) (a := (4174011149133 / 5000000000000 : ℝ)) (b := (31411619513 / 20000000000000 : ℝ)) (q := (550909947721 / 25000000000000 : ℝ))
      (E := (cell13110 ⟨17, by decide⟩).energy) (xi := (161693797599053 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13110 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13110]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13110])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13110) (a := (4174011149133 / 5000000000000 : ℝ)) (b := (31411619513 / 20000000000000 : ℝ)) (q := (550909947721 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13110])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13110])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13110]

theorem cert13110_18 : CellCertificate 13110 (875580363727263 / 10000000000000000 : ℝ) (801076000170861 / 500000000000000000 : ℝ) (161693797599053 / 5000000000000000 : ℝ)
    (cell13110 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · have h := gap_lower (n := 13110) (a := (10430718904303 / 12500000000000 : ℝ)) (b := (31411619513 / 20000000000000 : ℝ)) (q := (550910960063 / 25000000000000 : ℝ))
      (E := (cell13110 ⟨18, by decide⟩).energy) (xi := (161693797599053 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13110 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13110]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13110])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13110) (a := (10430718904303 / 12500000000000 : ℝ)) (b := (31411619513 / 20000000000000 : ℝ)) (q := (550910960063 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13110])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13110])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13110]

theorem cert13110_19 : CellCertificate 13110 (875580363727263 / 10000000000000000 : ℝ) (801076000170861 / 500000000000000000 : ℝ) (161693797599053 / 5000000000000000 : ℝ)
    (cell13110 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · have h := gap_lower (n := 13110) (a := (8341130370821 / 10000000000000 : ℝ)) (b := (31411619513 / 20000000000000 : ℝ)) (q := (1101823912203 / 50000000000000 : ℝ))
      (E := (cell13110 ⟨19, by decide⟩).energy) (xi := (161693797599053 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13110 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13110]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13110])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13110) (a := (8341130370821 / 10000000000000 : ℝ)) (b := (31411619513 / 20000000000000 : ℝ)) (q := (1101823912203 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13110])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13110])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13110]

theorem cert13111_0 : CellCertificate 13111 (875554079998209 / 10000000000000000 : ℝ) (1602029762353459 / 1000000000000000000 : ℝ) (323362363932921 / 10000000000000000 : ℝ)
    (cell13111 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · have h := gap_lower (n := 13111) (a := (84069967455547 / 100000000000000 : ℝ)) (b := (157045981037 / 100000000000000 : ℝ)) (q := (2203459812149 / 100000000000000 : ℝ))
      (E := (cell13111 ⟨0, by decide⟩).energy) (xi := (323362363932921 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13111 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13111]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13111])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13111) (a := (84069967455547 / 100000000000000 : ℝ)) (b := (157045981037 / 100000000000000 : ℝ)) (q := (2203459812149 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13111])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13111])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13111]

theorem cert13111_1 : CellCertificate 13111 (875554079998209 / 10000000000000000 : ℝ) (1602029762353459 / 1000000000000000000 : ℝ) (323362363932921 / 10000000000000000 : ℝ)
    (cell13111 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · have h := gap_lower (n := 13111) (a := (21008769673843 / 25000000000000 : ℝ)) (b := (157045981037 / 100000000000000 : ℝ)) (q := (1101731893677 / 50000000000000 : ℝ))
      (E := (cell13111 ⟨1, by decide⟩).energy) (xi := (323362363932921 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13111 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13111]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13111])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13111) (a := (21008769673843 / 25000000000000 : ℝ)) (b := (157045981037 / 100000000000000 : ℝ)) (q := (1101731893677 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13111])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13111])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13111]

theorem cert13111_2 : CellCertificate 13111 (875554079998209 / 10000000000000000 : ℝ) (1602029762353459 / 1000000000000000000 : ℝ) (323362363932921 / 10000000000000000 : ℝ)
    (cell13111 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · have h := gap_lower (n := 13111) (a := (8400021474809 / 10000000000000 : ℝ)) (b := (157045981037 / 100000000000000 : ℝ)) (q := (1101733911343 / 50000000000000 : ℝ))
      (E := (cell13111 ⟨2, by decide⟩).energy) (xi := (323362363932921 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13111 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13111]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13111])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13111) (a := (8400021474809 / 10000000000000 : ℝ)) (b := (157045981037 / 100000000000000 : ℝ)) (q := (1101733911343 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13111])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13111])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13111]

theorem cert13111_3 : CellCertificate 13111 (875554079998209 / 10000000000000000 : ℝ) (1602029762353459 / 1000000000000000000 : ℝ) (323362363932921 / 10000000000000000 : ℝ)
    (cell13111 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · have h := gap_lower (n := 13111) (a := (20991343894367 / 25000000000000 : ℝ)) (b := (157045981037 / 100000000000000 : ℝ)) (q := (8813887243 / 400000000000 : ℝ))
      (E := (cell13111 ⟨3, by decide⟩).energy) (xi := (323362363932921 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13111 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13111]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13111])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13111) (a := (20991343894367 / 25000000000000 : ℝ)) (b := (157045981037 / 100000000000000 : ℝ)) (q := (8813887243 / 400000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13111])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13111])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13111]

theorem cert13111_4 : CellCertificate 13111 (875554079998209 / 10000000000000000 : ℝ) (1602029762353459 / 1000000000000000000 : ℝ) (323362363932921 / 10000000000000000 : ℝ)
    (cell13111 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · have h := gap_lower (n := 13111) (a := (10491320143433 / 12500000000000 : ℝ)) (b := (157045981037 / 100000000000000 : ℝ)) (q := (34429309649 / 1562500000000 : ℝ))
      (E := (cell13111 ⟨4, by decide⟩).energy) (xi := (323362363932921 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13111 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13111]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13111])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13111) (a := (10491320143433 / 12500000000000 : ℝ)) (b := (157045981037 / 100000000000000 : ℝ)) (q := (34429309649 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13111])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13111])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13111]

theorem cert13111_5 : CellCertificate 13111 (875554079998209 / 10000000000000000 : ℝ) (1602029762353459 / 1000000000000000000 : ℝ) (323362363932921 / 10000000000000000 : ℝ)
    (cell13111 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · have h := gap_lower (n := 13111) (a := (41947885711113 / 50000000000000 : ℝ)) (b := (157045981037 / 100000000000000 : ℝ)) (q := (550869962727 / 25000000000000 : ℝ))
      (E := (cell13111 ⟨5, by decide⟩).energy) (xi := (323362363932921 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13111 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13111]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13111])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13111) (a := (41947885711113 / 50000000000000 : ℝ)) (b := (157045981037 / 100000000000000 : ℝ)) (q := (550869962727 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13111])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13111])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13111]

theorem cert13111_6 : CellCertificate 13111 (875554079998209 / 10000000000000000 : ℝ) (1602029762353459 / 1000000000000000000 : ℝ) (323362363932921 / 10000000000000000 : ℝ)
    (cell13111 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · have h := gap_lower (n := 13111) (a := (83861006366087 / 100000000000000 : ℝ)) (b := (157045981037 / 100000000000000 : ℝ)) (q := (550870965121 / 25000000000000 : ℝ))
      (E := (cell13111 ⟨6, by decide⟩).energy) (xi := (323362363932921 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13111 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13111]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13111])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13111) (a := (83861006366087 / 100000000000000 : ℝ)) (b := (157045981037 / 100000000000000 : ℝ)) (q := (550870965121 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13111])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13111])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13111]

theorem cert13111_7 : CellCertificate 13111 (875554079998209 / 10000000000000000 : ℝ) (1602029762353459 / 1000000000000000000 : ℝ) (323362363932921 / 10000000000000000 : ℝ)
    (cell13111 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · have h := gap_lower (n := 13111) (a := (8382626594357 / 10000000000000 : ℝ)) (b := (157045981037 / 100000000000000 : ℝ)) (q := (2203487853549 / 100000000000000 : ℝ))
      (E := (cell13111 ⟨7, by decide⟩).energy) (xi := (323362363932921 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13111 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13111]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13111])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13111) (a := (8382626594357 / 10000000000000 : ℝ)) (b := (157045981037 / 100000000000000 : ℝ)) (q := (2203487853549 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13111])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13111])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13111]

theorem cert13111_8 : CellCertificate 13111 (875554079998209 / 10000000000000000 : ℝ) (1602029762353459 / 1000000000000000000 : ℝ) (323362363932921 / 10000000000000000 : ℝ)
    (cell13111 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · have h := gap_lower (n := 13111) (a := (41895775059691 / 50000000000000 : ℝ)) (b := (157045981037 / 100000000000000 : ℝ)) (q := (2203491895171 / 100000000000000 : ℝ))
      (E := (cell13111 ⟨8, by decide⟩).energy) (xi := (323362363932921 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13111 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13111]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13111])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13111) (a := (41895775059691 / 50000000000000 : ℝ)) (b := (157045981037 / 100000000000000 : ℝ)) (q := (2203491895171 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13111])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13111])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13111]

theorem cert13111_9 : CellCertificate 13111 (875554079998209 / 10000000000000000 : ℝ) (1602029762353459 / 1000000000000000000 : ℝ) (323362363932921 / 10000000000000000 : ℝ)
    (cell13111 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · have h := gap_lower (n := 13111) (a := (16751371771683 / 20000000000000 : ℝ)) (b := (157045981037 / 100000000000000 : ℝ)) (q := (1101747938041 / 50000000000000 : ℝ))
      (E := (cell13111 ⟨9, by decide⟩).energy) (xi := (323362363932921 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13111 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13111]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13111])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13111) (a := (16751371771683 / 20000000000000 : ℝ)) (b := (157045981037 / 100000000000000 : ℝ)) (q := (1101747938041 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13111])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13111])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13111]

theorem cert13111_10 : CellCertificate 13111 (875554079998209 / 10000000000000000 : ℝ) (1602029762353459 / 1000000000000000000 : ℝ) (323362363932921 / 10000000000000000 : ℝ)
    (cell13111 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · have h := gap_lower (n := 13111) (a := (83722192125743 / 100000000000000 : ℝ)) (b := (157045981037 / 100000000000000 : ℝ)) (q := (34429686233 / 1562500000000 : ℝ))
      (E := (cell13111 ⟨10, by decide⟩).energy) (xi := (323362363932921 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13111 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13111]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13111])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13111) (a := (83722192125743 / 100000000000000 : ℝ)) (b := (157045981037 / 100000000000000 : ℝ)) (q := (34429686233 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13111])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13111])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13111]

theorem cert13111_11 : CellCertificate 13111 (875554079998209 / 10000000000000000 : ℝ) (1602029762353459 / 1000000000000000000 : ℝ) (323362363932921 / 10000000000000000 : ℝ)
    (cell13111 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · have h := gap_lower (n := 13111) (a := (41843774943311 / 50000000000000 : ℝ)) (b := (157045981037 / 100000000000000 : ℝ)) (q := (11017519569 / 500000000000 : ℝ))
      (E := (cell13111 ⟨11, by decide⟩).energy) (xi := (323362363932921 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13111 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13111]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13111])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13111) (a := (41843774943311 / 50000000000000 : ℝ)) (b := (157045981037 / 100000000000000 : ℝ)) (q := (11017519569 / 500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13111])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13111])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13111]

theorem cert13111_12 : CellCertificate 13111 (875554079998209 / 10000000000000000 : ℝ) (1602029762353459 / 1000000000000000000 : ℝ) (323362363932921 / 10000000000000000 : ℝ)
    (cell13111 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · have h := gap_lower (n := 13111) (a := (20913233026623 / 25000000000000 : ℝ)) (b := (157045981037 / 100000000000000 : ℝ)) (q := (55087698121 / 2500000000000 : ℝ))
      (E := (cell13111 ⟨12, by decide⟩).energy) (xi := (323362363932921 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13111 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13111]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13111])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13111) (a := (20913233026623 / 25000000000000 : ℝ)) (b := (157045981037 / 100000000000000 : ℝ)) (q := (55087698121 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13111])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13111])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13111]

theorem cert13111_13 : CellCertificate 13111 (875554079998209 / 10000000000000000 : ℝ) (1602029762353459 / 1000000000000000000 : ℝ) (323362363932921 / 10000000000000000 : ℝ)
    (cell13111 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · have h := gap_lower (n := 13111) (a := (10452292343871 / 12500000000000 : ℝ)) (b := (157045981037 / 100000000000000 : ℝ)) (q := (1101755978911 / 50000000000000 : ℝ))
      (E := (cell13111 ⟨13, by decide⟩).energy) (xi := (323362363932921 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13111 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13111]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13111])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13111) (a := (10452292343871 / 12500000000000 : ℝ)) (b := (157045981037 / 100000000000000 : ℝ)) (q := (1101755978911 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13111])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13111])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13111]

theorem cert13111_14 : CellCertificate 13111 (875554079998209 / 10000000000000000 : ℝ) (1602029762353459 / 1000000000000000000 : ℝ) (323362363932921 / 10000000000000000 : ℝ)
    (cell13111 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · have h := gap_lower (n := 13111) (a := (41791884892923 / 50000000000000 : ℝ)) (b := (157045981037 / 100000000000000 : ℝ)) (q := (2203515960113 / 100000000000000 : ℝ))
      (E := (cell13111 ⟨14, by decide⟩).energy) (xi := (323362363932921 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13111 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13111]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13111])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13111) (a := (41791884892923 / 50000000000000 : ℝ)) (b := (157045981037 / 100000000000000 : ℝ)) (q := (2203515960113 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13111])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13111])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13111]

theorem cert13111_15 : CellCertificate 13111 (875554079998209 / 10000000000000000 : ℝ) (1602029762353459 / 1000000000000000000 : ℝ) (323362363932921 / 10000000000000000 : ℝ)
    (cell13111 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · have h := gap_lower (n := 13111) (a := (83549225177099 / 100000000000000 : ℝ)) (b := (157045981037 / 100000000000000 : ℝ)) (q := (1101759997571 / 50000000000000 : ℝ))
      (E := (cell13111 ⟨15, by decide⟩).energy) (xi := (323362363932921 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13111 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13111]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13111])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13111) (a := (83549225177099 / 100000000000000 : ℝ)) (b := (157045981037 / 100000000000000 : ℝ)) (q := (1101759997571 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13111])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13111])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13111]

theorem cert13111_16 : CellCertificate 13111 (875554079998209 / 10000000000000000 : ℝ) (1602029762353459 / 1000000000000000000 : ℝ) (323362363932921 / 10000000000000000 : ℝ)
    (cell13111 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · have h := gap_lower (n := 13111) (a := (20878676222719 / 25000000000000 : ℝ)) (b := (157045981037 / 100000000000000 : ℝ)) (q := (2203524009743 / 100000000000000 : ℝ))
      (E := (cell13111 ⟨16, by decide⟩).energy) (xi := (323362363932921 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13111 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13111]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13111])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13111) (a := (20878676222719 / 25000000000000 : ℝ)) (b := (157045981037 / 100000000000000 : ℝ)) (q := (2203524009743 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13111])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13111])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13111]

theorem cert13111_17 : CellCertificate 13111 (875554079998209 / 10000000000000000 : ℝ) (1602029762353459 / 1000000000000000000 : ℝ) (323362363932921 / 10000000000000000 : ℝ)
    (cell13111 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · have h := gap_lower (n := 13111) (a := (41740104446751 / 50000000000000 : ℝ)) (b := (157045981037 / 100000000000000 : ℝ)) (q := (2203528008657 / 100000000000000 : ℝ))
      (E := (cell13111 ⟨17, by decide⟩).energy) (xi := (323362363932921 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13111 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13111]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13111])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13111) (a := (41740104446751 / 50000000000000 : ℝ)) (b := (157045981037 / 100000000000000 : ℝ)) (q := (2203528008657 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13111])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13111])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13111]

theorem cert13111_18 : CellCertificate 13111 (875554079998209 / 10000000000000000 : ℝ) (1602029762353459 / 1000000000000000000 : ℝ) (323362363932921 / 10000000000000000 : ℝ)
    (cell13111 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · have h := gap_lower (n := 13111) (a := (83445737151473 / 100000000000000 : ℝ)) (b := (157045981037 / 100000000000000 : ℝ)) (q := (2203531996389 / 100000000000000 : ℝ))
      (E := (cell13111 ⟨18, by decide⟩).energy) (xi := (323362363932921 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13111 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13111]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13111])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13111) (a := (83445737151473 / 100000000000000 : ℝ)) (b := (157045981037 / 100000000000000 : ℝ)) (q := (2203531996389 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13111])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13111])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13111]

theorem cert13111_19 : CellCertificate 13111 (875554079998209 / 10000000000000000 : ℝ) (1602029762353459 / 1000000000000000000 : ℝ) (323362363932921 / 10000000000000000 : ℝ)
    (cell13111 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · have h := gap_lower (n := 13111) (a := (41705644815731 / 50000000000000 : ℝ)) (b := (157045981037 / 100000000000000 : ℝ)) (q := (440707207099 / 20000000000000 : ℝ))
      (E := (cell13111 ⟨19, by decide⟩).energy) (xi := (323362363932921 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13111 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13111]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13111])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13111) (a := (41705644815731 / 50000000000000 : ℝ)) (b := (157045981037 / 100000000000000 : ℝ)) (q := (440707207099 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13111])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13111])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13111]

theorem cert13112_0 : CellCertificate 13112 (87552780010651 / 1000000000000000 : ℝ) (1601907543016341 / 1000000000000000000 : ℝ) (80834284158179 / 2500000000000000 : ℝ)
    (cell13112 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · have h := gap_lower (n := 13112) (a := (16813990652437 / 20000000000000 : ℝ)) (b := (31406773277 / 20000000000000 : ℝ)) (q := (1101674016091 / 50000000000000 : ℝ))
      (E := (cell13112 ⟨0, by decide⟩).energy) (xi := (80834284158179 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13112 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13112]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13112])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13112) (a := (16813990652437 / 20000000000000 : ℝ)) (b := (31406773277 / 20000000000000 : ℝ)) (q := (1101674016091 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13112])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13112])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13112]

theorem cert13112_1 : CellCertificate 13112 (87552780010651 / 1000000000000000 : ℝ) (1601907543016341 / 1000000000000000000 : ℝ) (80834284158179 / 2500000000000000 : ℝ)
    (cell13112 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · have h := gap_lower (n := 13112) (a := (84035064508311 / 100000000000000 : ℝ)) (b := (31406773277 / 20000000000000 : ℝ)) (q := (1101676001601 / 50000000000000 : ℝ))
      (E := (cell13112 ⟨1, by decide⟩).energy) (xi := (80834284158179 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13112 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13112]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13112])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13112) (a := (84035064508311 / 100000000000000 : ℝ)) (b := (31406773277 / 20000000000000 : ℝ)) (q := (1101676001601 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13112])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13112])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13112]

theorem cert13112_2 : CellCertificate 13112 (87552780010651 / 1000000000000000 : ℝ) (1601907543016341 / 1000000000000000000 : ℝ) (80834284158179 / 2500000000000000 : ℝ)
    (cell13112 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · have h := gap_lower (n := 13112) (a := (3360008022693 / 4000000000000 : ℝ)) (b := (31406773277 / 20000000000000 : ℝ)) (q := (550839008599 / 25000000000000 : ℝ))
      (E := (cell13112 ⟨2, by decide⟩).energy) (xi := (80834284158179 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13112 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13112]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13112])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13112) (a := (3360008022693 / 4000000000000 : ℝ)) (b := (31406773277 / 20000000000000 : ℝ)) (q := (550839008599 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13112])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13112])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13112]

theorem cert13112_3 : CellCertificate 13112 (87552780010651 / 1000000000000000 : ℝ) (1601907543016341 / 1000000000000000000 : ℝ) (80834284158179 / 2500000000000000 : ℝ)
    (cell13112 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · have h := gap_lower (n := 13112) (a := (83965361402993 / 100000000000000 : ℝ)) (b := (31406773277 / 20000000000000 : ℝ)) (q := (2203360018369 / 100000000000000 : ℝ))
      (E := (cell13112 ⟨3, by decide⟩).energy) (xi := (80834284158179 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13112 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13112]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13112])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13112) (a := (83965361402993 / 100000000000000 : ℝ)) (b := (31406773277 / 20000000000000 : ℝ)) (q := (2203360018369 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13112])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13112])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13112]

theorem cert13112_4 : CellCertificate 13112 (87552780010651 / 1000000000000000 : ℝ) (1601907543016341 / 1000000000000000000 : ℝ) (80834284158179 / 2500000000000000 : ℝ)
    (cell13112 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · have h := gap_lower (n := 13112) (a := (83930546979273 / 100000000000000 : ℝ)) (b := (31406773277 / 20000000000000 : ℝ)) (q := (440672815811 / 20000000000000 : ℝ))
      (E := (cell13112 ⟨4, by decide⟩).energy) (xi := (80834284158179 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13112 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13112]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13112])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13112) (a := (83930546979273 / 100000000000000 : ℝ)) (b := (31406773277 / 20000000000000 : ℝ)) (q := (440672815811 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13112])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13112])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13112]

theorem cert13112_5 : CellCertificate 13112 (87552780010651 / 1000000000000000 : ℝ) (1601907543016341 / 1000000000000000000 : ℝ) (80834284158179 / 2500000000000000 : ℝ)
    (cell13112 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · have h := gap_lower (n := 13112) (a := (83895757260313 / 100000000000000 : ℝ)) (b := (31406773277 / 20000000000000 : ℝ)) (q := (2203368050487 / 100000000000000 : ℝ))
      (E := (cell13112 ⟨5, by decide⟩).energy) (xi := (80834284158179 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13112 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13112]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13112])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13112) (a := (83895757260313 / 100000000000000 : ℝ)) (b := (31406773277 / 20000000000000 : ℝ)) (q := (2203368050487 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13112])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13112])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13112]

theorem cert13112_6 : CellCertificate 13112 (87552780010651 / 1000000000000000 : ℝ) (1601907543016341 / 1000000000000000000 : ℝ) (80834284158179 / 2500000000000000 : ℝ)
    (cell13112 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · have h := gap_lower (n := 13112) (a := (83860992210447 / 100000000000000 : ℝ)) (b := (31406773277 / 20000000000000 : ℝ)) (q := (1101686028057 / 50000000000000 : ℝ))
      (E := (cell13112 ⟨6, by decide⟩).energy) (xi := (80834284158179 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13112 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13112]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13112])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13112) (a := (83860992210447 / 100000000000000 : ℝ)) (b := (31406773277 / 20000000000000 : ℝ)) (q := (1101686028057 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13112])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13112])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13112]

theorem cert13112_7 : CellCertificate 13112 (87552780010651 / 1000000000000000 : ℝ) (1601907543016341 / 1000000000000000000 : ℝ) (80834284158179 / 2500000000000000 : ℝ)
    (cell13112 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · have h := gap_lower (n := 13112) (a := (83826251794197 / 100000000000000 : ℝ)) (b := (31406773277 / 20000000000000 : ℝ)) (q := (2203376103289 / 100000000000000 : ℝ))
      (E := (cell13112 ⟨7, by decide⟩).energy) (xi := (80834284158179 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13112 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13112]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13112])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13112) (a := (83826251794197 / 100000000000000 : ℝ)) (b := (31406773277 / 20000000000000 : ℝ)) (q := (2203376103289 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13112])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13112])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13112]

theorem cert13112_8 : CellCertificate 13112 (87552780010651 / 1000000000000000 : ℝ) (1601907543016341 / 1000000000000000000 : ℝ) (80834284158179 / 2500000000000000 : ℝ)
    (cell13112 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · have h := gap_lower (n := 13112) (a := (8379153597627 / 10000000000000 : ℝ)) (b := (31406773277 / 20000000000000 : ℝ)) (q := (2203380083043 / 100000000000000 : ℝ))
      (E := (cell13112 ⟨8, by decide⟩).energy) (xi := (80834284158179 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13112 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13112]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13112])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13112) (a := (8379153597627 / 10000000000000 : ℝ)) (b := (31406773277 / 20000000000000 : ℝ)) (q := (2203380083043 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13112])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13112])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13112]

theorem cert13112_9 : CellCertificate 13112 (87552780010651 / 1000000000000000 : ℝ) (1601907543016341 / 1000000000000000000 : ℝ) (80834284158179 / 2500000000000000 : ℝ)
    (cell13112 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · have h := gap_lower (n := 13112) (a := (83756844721559 / 100000000000000 : ℝ)) (b := (31406773277 / 20000000000000 : ℝ)) (q := (440676823641 / 20000000000000 : ℝ))
      (E := (cell13112 ⟨9, by decide⟩).energy) (xi := (80834284158179 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13112 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13112]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13112])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13112) (a := (83756844721559 / 100000000000000 : ℝ)) (b := (31406773277 / 20000000000000 : ℝ)) (q := (440676823641 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13112])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13112])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13112]

theorem cert13112_10 : CellCertificate 13112 (87552780010651 / 1000000000000000 : ℝ) (1601907543016341 / 1000000000000000000 : ℝ) (80834284158179 / 2500000000000000 : ℝ)
    (cell13112 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · have h := gap_lower (n := 13112) (a := (83722177995137 / 100000000000000 : ℝ)) (b := (31406773277 / 20000000000000 : ℝ)) (q := (2203388099213 / 100000000000000 : ℝ))
      (E := (cell13112 ⟨10, by decide⟩).energy) (xi := (80834284158179 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13112 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13112]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13112])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13112) (a := (83722177995137 / 100000000000000 : ℝ)) (b := (31406773277 / 20000000000000 : ℝ)) (q := (2203388099213 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13112])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13112])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13112]

theorem cert13112_11 : CellCertificate 13112 (87552780010651 / 1000000000000000 : ℝ) (1601907543016341 / 1000000000000000000 : ℝ) (80834284158179 / 2500000000000000 : ℝ)
    (cell13112 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · have h := gap_lower (n := 13112) (a := (41843767881131 / 50000000000000 : ℝ)) (b := (31406773277 / 20000000000000 : ℝ)) (q := (550848037123 / 25000000000000 : ℝ))
      (E := (cell13112 ⟨11, by decide⟩).energy) (xi := (80834284158179 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13112 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13112]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13112])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13112) (a := (41843767881131 / 50000000000000 : ℝ)) (b := (31406773277 / 20000000000000 : ℝ)) (q := (550848037123 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13112])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13112])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13112]

theorem cert13112_12 : CellCertificate 13112 (87552780010651 / 1000000000000000 : ℝ) (1601907543016341 / 1000000000000000000 : ℝ) (80834284158179 / 2500000000000000 : ℝ)
    (cell13112 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · have h := gap_lower (n := 13112) (a := (8365291798837 / 10000000000000 : ℝ)) (b := (31406773277 / 20000000000000 : ℝ)) (q := (137712259743 / 6250000000000 : ℝ))
      (E := (cell13112 ⟨12, by decide⟩).energy) (xi := (80834284158179 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13112 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13112]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13112])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13112) (a := (8365291798837 / 10000000000000 : ℝ)) (b := (31406773277 / 20000000000000 : ℝ)) (q := (137712259743 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13112])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13112])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13112]

theorem cert13112_13 : CellCertificate 13112 (87552780010651 / 1000000000000000 : ℝ) (1601907543016341 / 1000000000000000000 : ℝ) (80834284158179 / 2500000000000000 : ℝ)
    (cell13112 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · have h := gap_lower (n := 13112) (a := (2090458115977 / 2500000000000 : ℝ)) (b := (31406773277 / 20000000000000 : ℝ)) (q := (275425023159 / 12500000000000 : ℝ))
      (E := (cell13112 ⟨13, by decide⟩).energy) (xi := (80834284158179 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13112 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13112]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13112])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13112) (a := (2090458115977 / 2500000000000 : ℝ)) (b := (31406773277 / 20000000000000 : ℝ)) (q := (275425023159 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13112])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13112])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13112]

theorem cert13112_14 : CellCertificate 13112 (87552780010651 / 1000000000000000 : ℝ) (1601907543016341 / 1000000000000000000 : ℝ) (80834284158179 / 2500000000000000 : ℝ)
    (cell13112 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · have h := gap_lower (n := 13112) (a := (83583755680187 / 100000000000000 : ℝ)) (b := (31406773277 / 20000000000000 : ℝ)) (q := (2203404184011 / 100000000000000 : ℝ))
      (E := (cell13112 ⟨14, by decide⟩).energy) (xi := (80834284158179 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13112 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13112]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13112])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13112) (a := (83583755680187 / 100000000000000 : ℝ)) (b := (31406773277 / 20000000000000 : ℝ)) (q := (2203404184011 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13112])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13112])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13112]

theorem cert13112_15 : CellCertificate 13112 (87552780010651 / 1000000000000000 : ℝ) (1601907543016341 / 1000000000000000000 : ℝ) (80834284158179 / 2500000000000000 : ℝ)
    (cell13112 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · have h := gap_lower (n := 13112) (a := (83549211077663 / 100000000000000 : ℝ)) (b := (31406773277 / 20000000000000 : ℝ)) (q := (440681631467 / 20000000000000 : ℝ))
      (E := (cell13112 ⟨15, by decide⟩).energy) (xi := (80834284158179 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13112 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13112]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13112])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13112) (a := (83549211077663 / 100000000000000 : ℝ)) (b := (31406773277 / 20000000000000 : ℝ)) (q := (440681631467 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13112])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13112])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13112]

theorem cert13112_16 : CellCertificate 13112 (87552780010651 / 1000000000000000 : ℝ) (1601907543016341 / 1000000000000000000 : ℝ) (80834284158179 / 2500000000000000 : ℝ)
    (cell13112 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · have h := gap_lower (n := 13112) (a := (41757345398829 / 50000000000000 : ℝ)) (b := (31406773277 / 20000000000000 : ℝ)) (q := (2203412168453 / 100000000000000 : ℝ))
      (E := (cell13112 ⟨16, by decide⟩).energy) (xi := (80834284158179 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13112 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13112]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13112])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13112) (a := (41757345398829 / 50000000000000 : ℝ)) (b := (31406773277 / 20000000000000 : ℝ)) (q := (2203412168453 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13112])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13112])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13112]

theorem cert13112_17 : CellCertificate 13112 (87552780010651 / 1000000000000000 : ℝ) (1601907543016341 / 1000000000000000000 : ℝ) (80834284158179 / 2500000000000000 : ℝ)
    (cell13112 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · have h := gap_lower (n := 13112) (a := (16696038961299 / 20000000000000 : ℝ)) (b := (31406773277 / 20000000000000 : ℝ)) (q := (2203416222181 / 100000000000000 : ℝ))
      (E := (cell13112 ⟨17, by decide⟩).energy) (xi := (80834284158179 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13112 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13112]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13112])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13112) (a := (16696038961299 / 20000000000000 : ℝ)) (b := (31406773277 / 20000000000000 : ℝ)) (q := (2203416222181 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13112])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13112])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13112]

theorem cert13112_18 : CellCertificate 13112 (87552780010651 / 1000000000000000 : ℝ) (1601907543016341 / 1000000000000000000 : ℝ) (80834284158179 / 2500000000000000 : ℝ)
    (cell13112 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · have h := gap_lower (n := 13112) (a := (83445723070673 / 100000000000000 : ℝ)) (b := (31406773277 / 20000000000000 : ℝ)) (q := (550855051637 / 25000000000000 : ℝ))
      (E := (cell13112 ⟨18, by decide⟩).energy) (xi := (80834284158179 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13112 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13112]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13112])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13112) (a := (83445723070673 / 100000000000000 : ℝ)) (b := (31406773277 / 20000000000000 : ℝ)) (q := (550855051637 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13112])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13112])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13112]

theorem cert13112_19 : CellCertificate 13112 (87552780010651 / 1000000000000000 : ℝ) (1601907543016341 / 1000000000000000000 : ℝ) (80834284158179 / 2500000000000000 : ℝ)
    (cell13112 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · have h := gap_lower (n := 13112) (a := (83411275556863 / 100000000000000 : ℝ)) (b := (31406773277 / 20000000000000 : ℝ)) (q := (68857007573 / 3125000000000 : ℝ))
      (E := (cell13112 ⟨19, by decide⟩).energy) (xi := (80834284158179 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13112 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13112]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13112])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13112) (a := (83411275556863 / 100000000000000 : ℝ)) (b := (31406773277 / 20000000000000 : ℝ)) (q := (68857007573 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13112])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13112])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13112]

theorem cert13113_0 : CellCertificate 13113 (875501524051283 / 10000000000000000 : ℝ) (16017853423261 / 10000000000000000 : ℝ) (40413989162063 / 1250000000000000 : ℝ)
    (cell13113 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · have h := gap_lower (n := 13113) (a := (84069939070991 / 100000000000000 : ℝ)) (b := (157021753609 / 100000000000000 : ℝ)) (q := (44064724959 / 2000000000000 : ℝ))
      (E := (cell13113 ⟨0, by decide⟩).energy) (xi := (40413989162063 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13113 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13113]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13113])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13113) (a := (84069939070991 / 100000000000000 : ℝ)) (b := (157021753609 / 100000000000000 : ℝ)) (q := (44064724959 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13113])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13113])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13113]

theorem cert13113_1 : CellCertificate 13113 (875501524051283 / 10000000000000000 : ℝ) (16017853423261 / 10000000000000000 : ℝ) (40413989162063 / 1250000000000000 : ℝ)
    (cell13113 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · have h := gap_lower (n := 13113) (a := (84035050323417 / 100000000000000 : ℝ)) (b := (157021753609 / 100000000000000 : ℝ)) (q := (2203240272661 / 100000000000000 : ℝ))
      (E := (cell13113 ⟨1, by decide⟩).energy) (xi := (40413989162063 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13113 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13113]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13113])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13113) (a := (84035050323417 / 100000000000000 : ℝ)) (b := (157021753609 / 100000000000000 : ℝ)) (q := (2203240272661 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13113])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13113])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13113]

theorem cert13113_2 : CellCertificate 13113 (875501524051283 / 10000000000000000 : ℝ) (16017853423261 / 10000000000000000 : ℝ) (40413989162063 / 1250000000000000 : ℝ)
    (cell13113 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · have h := gap_lower (n := 13113) (a := (3360007455549 / 4000000000000 : ℝ)) (b := (157021753609 / 100000000000000 : ℝ)) (q := (550811060461 / 25000000000000 : ℝ))
      (E := (cell13113 ⟨2, by decide⟩).energy) (xi := (40413989162063 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13113 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13113]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13113])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13113) (a := (3360007455549 / 4000000000000 : ℝ)) (b := (157021753609 / 100000000000000 : ℝ)) (q := (550811060461 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13113])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13113])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13113]

theorem cert13113_3 : CellCertificate 13113 (875501524051283 / 10000000000000000 : ℝ) (16017853423261 / 10000000000000000 : ℝ) (40413989162063 / 1250000000000000 : ℝ)
    (cell13113 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · have h := gap_lower (n := 13113) (a := (41982673615341 / 50000000000000 : ℝ)) (b := (157021753609 / 100000000000000 : ℝ)) (q := (2203248279647 / 100000000000000 : ℝ))
      (E := (cell13113 ⟨3, by decide⟩).energy) (xi := (40413989162063 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13113 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13113]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13113])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13113) (a := (41982673615341 / 50000000000000 : ℝ)) (b := (157021753609 / 100000000000000 : ℝ)) (q := (2203248279647 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13113])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13113])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13113]

theorem cert13113_4 : CellCertificate 13113 (875501524051283 / 10000000000000000 : ℝ) (16017853423261 / 10000000000000000 : ℝ) (40413989162063 / 1250000000000000 : ℝ)
    (cell13113 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · have h := gap_lower (n := 13113) (a := (16786106562649 / 20000000000000 : ℝ)) (b := (157021753609 / 100000000000000 : ℝ)) (q := (2203252278371 / 100000000000000 : ℝ))
      (E := (cell13113 ⟨4, by decide⟩).energy) (xi := (40413989162063 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13113 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13113]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13113])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13113) (a := (16786106562649 / 20000000000000 : ℝ)) (b := (157021753609 / 100000000000000 : ℝ)) (q := (2203252278371 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13113])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13113])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13113]

theorem cert13113_5 : CellCertificate 13113 (875501524051283 / 10000000000000000 : ℝ) (16017853423261 / 10000000000000000 : ℝ) (40413989162063 / 1250000000000000 : ℝ)
    (cell13113 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · have h := gap_lower (n := 13113) (a := (41947871550281 / 50000000000000 : ℝ)) (b := (157021753609 / 100000000000000 : ℝ)) (q := (1101628151887 / 50000000000000 : ℝ))
      (E := (cell13113 ⟨5, by decide⟩).energy) (xi := (40413989162063 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13113 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13113]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13113])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13113) (a := (41947871550281 / 50000000000000 : ℝ)) (b := (157021753609 / 100000000000000 : ℝ)) (q := (1101628151887 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13113])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13113])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13113]

theorem cert13113_6 : CellCertificate 13113 (875501524051283 / 10000000000000000 : ℝ) (16017853423261 / 10000000000000000 : ℝ) (40413989162063 / 1250000000000000 : ℝ)
    (cell13113 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · have h := gap_lower (n := 13113) (a := (10482622257121 / 12500000000000 : ℝ)) (b := (157021753609 / 100000000000000 : ℝ)) (q := (88130412219 / 4000000000000 : ℝ))
      (E := (cell13113 ⟨6, by decide⟩).energy) (xi := (40413989162063 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13113 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13113]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13113])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13113) (a := (10482622257121 / 12500000000000 : ℝ)) (b := (157021753609 / 100000000000000 : ℝ)) (q := (88130412219 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13113])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13113])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13113]

theorem cert13113_7 : CellCertificate 13113 (875501524051283 / 10000000000000000 : ℝ) (16017853423261 / 10000000000000000 : ℝ) (40413989162063 / 1250000000000000 : ℝ)
    (cell13113 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · have h := gap_lower (n := 13113) (a := (10478279705873 / 12500000000000 : ℝ)) (b := (157021753609 / 100000000000000 : ℝ)) (q := (550816087193 / 25000000000000 : ℝ))
      (E := (cell13113 ⟨7, by decide⟩).energy) (xi := (40413989162063 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13113 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13113]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13113])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13113) (a := (10478279705873 / 12500000000000 : ℝ)) (b := (157021753609 / 100000000000000 : ℝ)) (q := (550816087193 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13113])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13113])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13113]

theorem cert13113_8 : CellCertificate 13113 (875501524051283 / 10000000000000000 : ℝ) (16017853423261 / 10000000000000000 : ℝ) (40413989162063 / 1250000000000000 : ℝ)
    (cell13113 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · have h := gap_lower (n := 13113) (a := (41895760917659 / 50000000000000 : ℝ)) (b := (157021753609 / 100000000000000 : ℝ)) (q := (1101634162347 / 50000000000000 : ℝ))
      (E := (cell13113 ⟨8, by decide⟩).energy) (xi := (40413989162063 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13113 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13113]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13113])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13113) (a := (41895760917659 / 50000000000000 : ℝ)) (b := (157021753609 / 100000000000000 : ℝ)) (q := (1101634162347 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13113])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13113])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13113]

theorem cert13113_9 : CellCertificate 13113 (875501524051283 / 10000000000000000 : ℝ) (16017853423261 / 10000000000000000 : ℝ) (40413989162063 / 1250000000000000 : ℝ)
    (cell13113 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · have h := gap_lower (n := 13113) (a := (83756830586861 / 100000000000000 : ℝ)) (b := (157021753609 / 100000000000000 : ℝ)) (q := (2203272356073 / 100000000000000 : ℝ))
      (E := (cell13113 ⟨9, by decide⟩).energy) (xi := (40413989162063 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13113 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13113]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13113])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13113) (a := (83756830586861 / 100000000000000 : ℝ)) (b := (157021753609 / 100000000000000 : ℝ)) (q := (2203272356073 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13113])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13113])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13113]

theorem cert13113_10 : CellCertificate 13113 (875501524051283 / 10000000000000000 : ℝ) (16017853423261 / 10000000000000000 : ℝ) (40413989162063 / 1250000000000000 : ℝ)
    (cell13113 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · have h := gap_lower (n := 13113) (a := (83722163866689 / 100000000000000 : ℝ)) (b := (157021753609 / 100000000000000 : ℝ)) (q := (1101638166671 / 50000000000000 : ℝ))
      (E := (cell13113 ⟨10, by decide⟩).energy) (xi := (40413989162063 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13113 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13113]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13113])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13113) (a := (83722163866689 / 100000000000000 : ℝ)) (b := (157021753609 / 100000000000000 : ℝ)) (q := (1101638166671 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13113])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13113])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13113]

theorem cert13113_11 : CellCertificate 13113 (875501524051283 / 10000000000000000 : ℝ) (16017853423261 / 10000000000000000 : ℝ) (40413989162063 / 1250000000000000 : ℝ)
    (cell13113 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · have h := gap_lower (n := 13113) (a := (41843760820029 / 50000000000000 : ℝ)) (b := (157021753609 / 100000000000000 : ℝ)) (q := (220328037893 / 10000000000000 : ℝ))
      (E := (cell13113 ⟨11, by decide⟩).energy) (xi := (40413989162063 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13113 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13113]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13113])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13113) (a := (41843760820029 / 50000000000000 : ℝ)) (b := (157021753609 / 100000000000000 : ℝ)) (q := (220328037893 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13113])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13113])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13113]

theorem cert13113_12 : CellCertificate 13113 (875501524051283 / 10000000000000000 : ℝ) (16017853423261 / 10000000000000000 : ℝ) (40413989162063 / 1250000000000000 : ℝ)
    (cell13113 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · have h := gap_lower (n := 13113) (a := (16730580774481 / 20000000000000 : ℝ)) (b := (157021753609 / 100000000000000 : ℝ)) (q := (2203284382681 / 100000000000000 : ℝ))
      (E := (cell13113 ⟨12, by decide⟩).energy) (xi := (40413989162063 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13113 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13113]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13113])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13113) (a := (16730580774481 / 20000000000000 : ℝ)) (b := (157021753609 / 100000000000000 : ℝ)) (q := (2203284382681 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13113])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13113])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13113]

theorem cert13113_13 : CellCertificate 13113 (875501524051283 / 10000000000000000 : ℝ) (16017853423261 / 10000000000000000 : ℝ) (40413989162063 / 1250000000000000 : ℝ)
    (cell13113 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · have h := gap_lower (n := 13113) (a := (20904577632337 / 25000000000000 : ℝ)) (b := (157021753609 / 100000000000000 : ℝ)) (q := (550822102117 / 25000000000000 : ℝ))
      (E := (cell13113 ⟨13, by decide⟩).energy) (xi := (40413989162063 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13113 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13113]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13113])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13113) (a := (20904577632337 / 25000000000000 : ℝ)) (b := (157021753609 / 100000000000000 : ℝ)) (q := (550822102117 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13113])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13113])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13113]

theorem cert13113_14 : CellCertificate 13113 (875501524051283 / 10000000000000000 : ℝ) (16017853423261 / 10000000000000000 : ℝ) (40413989162063 / 1250000000000000 : ℝ)
    (cell13113 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · have h := gap_lower (n := 13113) (a := (41791870788341 / 50000000000000 : ℝ)) (b := (157021753609 / 100000000000000 : ℝ)) (q := (2203292403657 / 100000000000000 : ℝ))
      (E := (cell13113 ⟨14, by decide⟩).energy) (xi := (40413989162063 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13113 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13113]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13113])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13113) (a := (41791870788341 / 50000000000000 : ℝ)) (b := (157021753609 / 100000000000000 : ℝ)) (q := (2203292403657 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13113])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13113])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13113]

theorem cert13113_15 : CellCertificate 13113 (875501524051283 / 10000000000000000 : ℝ) (16017853423261 / 10000000000000000 : ℝ) (40413989162063 / 1250000000000000 : ℝ)
    (cell13113 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · have h := gap_lower (n := 13113) (a := (4177459849019 / 5000000000000 : ℝ)) (b := (157021753609 / 100000000000000 : ℝ)) (q := (1101648215839 / 50000000000000 : ℝ))
      (E := (cell13113 ⟨15, by decide⟩).energy) (xi := (40413989162063 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13113 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13113]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13113])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13113) (a := (4177459849019 / 5000000000000 : ℝ)) (b := (157021753609 / 100000000000000 : ℝ)) (q := (1101648215839 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13113])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13113])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13113]

theorem cert13113_16 : CellCertificate 13113 (875501524051283 / 10000000000000000 : ℝ) (16017853423261 / 10000000000000000 : ℝ) (40413989162063 / 1250000000000000 : ℝ)
    (cell13113 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · have h := gap_lower (n := 13113) (a := (83514676706591 / 100000000000000 : ℝ)) (b := (157021753609 / 100000000000000 : ℝ)) (q := (2203300439363 / 100000000000000 : ℝ))
      (E := (cell13113 ⟨16, by decide⟩).energy) (xi := (40413989162063 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13113 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13113]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13113])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13113) (a := (83514676706591 / 100000000000000 : ℝ)) (b := (157021753609 / 100000000000000 : ℝ)) (q := (2203300439363 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13113])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13113])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13113]

theorem cert13113_17 : CellCertificate 13113 (875501524051283 / 10000000000000000 : ℝ) (16017853423261 / 10000000000000000 : ℝ) (40413989162063 / 1250000000000000 : ℝ)
    (cell13113 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · have h := gap_lower (n := 13113) (a := (2087004518041 / 2500000000000 : ℝ)) (b := (157021753609 / 100000000000000 : ℝ)) (q := (440660886291 / 20000000000000 : ℝ))
      (E := (cell13113 ⟨17, by decide⟩).energy) (xi := (40413989162063 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13113 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13113]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13113])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13113) (a := (2087004518041 / 2500000000000 : ℝ)) (b := (157021753609 / 100000000000000 : ℝ)) (q := (440660886291 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13113])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13113])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13113]

theorem cert13113_18 : CellCertificate 13113 (875501524051283 / 10000000000000000 : ℝ) (16017853423261 / 10000000000000000 : ℝ) (40413989162063 / 1250000000000000 : ℝ)
    (cell13113 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · have h := gap_lower (n := 13113) (a := (10430713624003 / 12500000000000 : ℝ)) (b := (157021753609 / 100000000000000 : ℝ)) (q := (2203308470729 / 100000000000000 : ℝ))
      (E := (cell13113 ⟨18, by decide⟩).energy) (xi := (40413989162063 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13113 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13113]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13113])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13113) (a := (10430713624003 / 12500000000000 : ℝ)) (b := (157021753609 / 100000000000000 : ℝ)) (q := (2203308470729 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13113])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13113])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13113]

theorem cert13113_19 : CellCertificate 13113 (875501524051283 / 10000000000000000 : ℝ) (16017853423261 / 10000000000000000 : ℝ) (40413989162063 / 1250000000000000 : ℝ)
    (cell13113 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · have h := gap_lower (n := 13113) (a := (41705630742207 / 50000000000000 : ℝ)) (b := (157021753609 / 100000000000000 : ℝ)) (q := (220331244493 / 10000000000000 : ℝ))
      (E := (cell13113 ⟨19, by decide⟩).energy) (xi := (40413989162063 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13113 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13113]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13113])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13113) (a := (41705630742207 / 50000000000000 : ℝ)) (b := (157021753609 / 100000000000000 : ℝ)) (q := (220331244493 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13113])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13113])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13113]

theorem cert13114_0 : CellCertificate 13114 (27358601619739 / 312500000000000 : ℝ) (1601663160278467 / 1000000000000000000 : ℝ) (323286693923297 / 10000000000000000 : ℝ)
    (cell13114 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · have h := gap_lower (n := 13114) (a := (16813984976393 / 20000000000000 : ℝ)) (b := (39252410677 / 25000000000000 : ℝ)) (q := (1101562258653 / 50000000000000 : ℝ))
      (E := (cell13114 ⟨0, by decide⟩).energy) (xi := (323286693923297 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13114 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13114]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13114])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13114) (a := (16813984976393 / 20000000000000 : ℝ)) (b := (39252410677 / 25000000000000 : ℝ)) (q := (1101562258653 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13114])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13114])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13114]

theorem cert13114_1 : CellCertificate 13114 (27358601619739 / 312500000000000 : ℝ) (1601663160278467 / 1000000000000000000 : ℝ) (323286693923297 / 10000000000000000 : ℝ)
    (cell13114 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · have h := gap_lower (n := 13114) (a := (8403503614069 / 10000000000000 : ℝ)) (b := (39252410677 / 25000000000000 : ℝ)) (q := (8605970851 / 390625000000 : ℝ))
      (E := (cell13114 ⟨1, by decide⟩).energy) (xi := (323286693923297 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13114 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13114]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13114])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13114) (a := (8403503614069 / 10000000000000 : ℝ)) (b := (39252410677 / 25000000000000 : ℝ)) (q := (8605970851 / 390625000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13114])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13114])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13114]

theorem cert13114_2 : CellCertificate 13114 (27358601619739 / 312500000000000 : ℝ) (1601663160278467 / 1000000000000000000 : ℝ) (323286693923297 / 10000000000000000 : ℝ)
    (cell13114 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · have h := gap_lower (n := 13114) (a := (84000172212291 / 100000000000000 : ℝ)) (b := (39252410677 / 25000000000000 : ℝ)) (q := (137695781433 / 6250000000000 : ℝ))
      (E := (cell13114 ⟨2, by decide⟩).energy) (xi := (323286693923297 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13114 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13114]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13114])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13114) (a := (84000172212291 / 100000000000000 : ℝ)) (b := (39252410677 / 25000000000000 : ℝ)) (q := (137695781433 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13114])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13114])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13114]

theorem cert13114_3 : CellCertificate 13114 (27358601619739 / 312500000000000 : ℝ) (1601663160278467 / 1000000000000000000 : ℝ) (323286693923297 / 10000000000000000 : ℝ)
    (cell13114 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · have h := gap_lower (n := 13114) (a := (16793066612107 / 20000000000000 : ℝ)) (b := (39252410677 / 25000000000000 : ℝ)) (q := (1101568268333 / 50000000000000 : ℝ))
      (E := (cell13114 ⟨3, by decide⟩).energy) (xi := (323286693923297 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13114 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13114]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13114])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13114) (a := (16793066612107 / 20000000000000 : ℝ)) (b := (39252410677 / 25000000000000 : ℝ)) (q := (1101568268333 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13114])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13114])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13114]

theorem cert13114_4 : CellCertificate 13114 (27358601619739 / 312500000000000 : ℝ) (1601663160278467 / 1000000000000000000 : ℝ) (323286693923297 / 10000000000000000 : ℝ)
    (cell13114 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · have h := gap_lower (n := 13114) (a := (4196525932469 / 5000000000000 : ℝ)) (b := (39252410677 / 25000000000000 : ℝ)) (q := (2203140531371 / 100000000000000 : ℝ))
      (E := (cell13114 ⟨4, by decide⟩).energy) (xi := (323286693923297 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13114 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13114]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13114])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13114) (a := (4196525932469 / 5000000000000 : ℝ)) (b := (39252410677 / 25000000000000 : ℝ)) (q := (2203140531371 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13114])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13114])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13114]

theorem cert13114_5 : CellCertificate 13114 (27358601619739 / 312500000000000 : ℝ) (1601663160278467 / 1000000000000000000 : ℝ) (323286693923297 / 10000000000000000 : ℝ)
    (cell13114 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · have h := gap_lower (n := 13114) (a := (41947864471487 / 50000000000000 : ℝ)) (b := (39252410677 / 25000000000000 : ℝ)) (q := (2203144552803 / 100000000000000 : ℝ))
      (E := (cell13114 ⟨5, by decide⟩).energy) (xi := (323286693923297 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13114 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13114]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13114])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13114) (a := (41947864471487 / 50000000000000 : ℝ)) (b := (39252410677 / 25000000000000 : ℝ)) (q := (2203144552803 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13114])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13114])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13114]

theorem cert13114_6 : CellCertificate 13114 (27358601619739 / 312500000000000 : ℝ) (1601663160278467 / 1000000000000000000 : ℝ) (323286693923297 / 10000000000000000 : ℝ)
    (cell13114 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · have h := gap_lower (n := 13114) (a := (1677219278113 / 2000000000000 : ℝ)) (b := (39252410677 / 25000000000000 : ℝ)) (q := (110157427529 / 5000000000000 : ℝ))
      (E := (cell13114 ⟨6, by decide⟩).energy) (xi := (323286693923297 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13114 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13114]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13114])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13114) (a := (1677219278113 / 2000000000000 : ℝ)) (b := (39252410677 / 25000000000000 : ℝ)) (q := (110157427529 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13114])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13114])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13114]

theorem cert13114_7 : CellCertificate 13114 (27358601619739 / 312500000000000 : ℝ) (1601663160278467 / 1000000000000000000 : ℝ) (323286693923297 / 10000000000000000 : ℝ)
    (cell13114 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · have h := gap_lower (n := 13114) (a := (20956555875483 / 25000000000000 : ℝ)) (b := (39252410677 / 25000000000000 : ℝ)) (q := (2203152589999 / 100000000000000 : ℝ))
      (E := (cell13114 ⟨7, by decide⟩).energy) (xi := (323286693923297 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13114 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13114]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13114])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13114) (a := (20956555875483 / 25000000000000 : ℝ)) (b := (39252410677 / 25000000000000 : ℝ)) (q := (2203152589999 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13114])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13114])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13114]

theorem cert13114_8 : CellCertificate 13114 (27358601619739 / 312500000000000 : ℝ) (1601663160278467 / 1000000000000000000 : ℝ) (323286693923297 / 10000000000000000 : ℝ)
    (cell13114 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · have h := gap_lower (n := 13114) (a := (3351660307861 / 4000000000000 : ℝ)) (b := (39252410677 / 25000000000000 : ℝ)) (q := (220315656209 / 10000000000000 : ℝ))
      (E := (cell13114 ⟨8, by decide⟩).energy) (xi := (323286693923297 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13114 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13114]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13114])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13114) (a := (3351660307861 / 4000000000000 : ℝ)) (b := (39252410677 / 25000000000000 : ℝ)) (q := (220315656209 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13114])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13114])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13114]

theorem cert13114_9 : CellCertificate 13114 (27358601619739 / 312500000000000 : ℝ) (1601663160278467 / 1000000000000000000 : ℝ) (323286693923297 / 10000000000000000 : ℝ)
    (cell13114 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · have h := gap_lower (n := 13114) (a := (83756816454323 / 100000000000000 : ℝ)) (b := (39252410677 / 25000000000000 : ℝ)) (q := (550790147421 / 25000000000000 : ℝ))
      (E := (cell13114 ⟨9, by decide⟩).energy) (xi := (323286693923297 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13114 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13114]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13114])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13114) (a := (83756816454323 / 100000000000000 : ℝ)) (b := (39252410677 / 25000000000000 : ℝ)) (q := (550790147421 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13114])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13114])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13114]

theorem cert13114_10 : CellCertificate 13114 (27358601619739 / 312500000000000 : ℝ) (1601663160278467 / 1000000000000000000 : ℝ) (323286693923297 / 10000000000000000 : ℝ)
    (cell13114 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · have h := gap_lower (n := 13114) (a := (83722149740399 / 100000000000000 : ℝ)) (b := (39252410677 / 25000000000000 : ℝ)) (q := (2203164621301 / 100000000000000 : ℝ))
      (E := (cell13114 ⟨10, by decide⟩).energy) (xi := (323286693923297 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13114 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13114]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13114])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13114) (a := (83722149740399 / 100000000000000 : ℝ)) (b := (39252410677 / 25000000000000 : ℝ)) (q := (2203164621301 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13114])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13114])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13114]

theorem cert13114_11 : CellCertificate 13114 (27358601619739 / 312500000000000 : ℝ) (1601663160278467 / 1000000000000000000 : ℝ) (323286693923297 / 10000000000000000 : ℝ)
    (cell13114 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · have h := gap_lower (n := 13114) (a := (8368750752001 / 10000000000000 : ℝ)) (b := (39252410677 / 25000000000000 : ℝ)) (q := (550792151279 / 25000000000000 : ℝ))
      (E := (cell13114 ⟨11, by decide⟩).energy) (xi := (323286693923297 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13114 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13114]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13114])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13114) (a := (8368750752001 / 10000000000000 : ℝ)) (b := (39252410677 / 25000000000000 : ℝ)) (q := (550792151279 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13114])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13114])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13114]

theorem cert13114_12 : CellCertificate 13114 (27358601619739 / 312500000000000 : ℝ) (1601663160278467 / 1000000000000000000 : ℝ) (323286693923297 / 10000000000000000 : ℝ)
    (cell13114 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · have h := gap_lower (n := 13114) (a := (16730577951719 / 20000000000000 : ℝ)) (b := (39252410677 / 25000000000000 : ℝ)) (q := (275396575653 / 12500000000000 : ℝ))
      (E := (cell13114 ⟨12, by decide⟩).energy) (xi := (323286693923297 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13114 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13114]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13114])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13114) (a := (16730577951719 / 20000000000000 : ℝ)) (b := (39252410677 / 25000000000000 : ℝ)) (q := (275396575653 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13114])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13114])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13114]

theorem cert13114_13 : CellCertificate 13114 (27358601619739 / 312500000000000 : ℝ) (1601663160278467 / 1000000000000000000 : ℝ) (323286693923297 / 10000000000000000 : ℝ)
    (cell13114 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · have h := gap_lower (n := 13114) (a := (8361829642177 / 10000000000000 : ℝ)) (b := (39252410677 / 25000000000000 : ℝ)) (q := (1101588313707 / 50000000000000 : ℝ))
      (E := (cell13114 ⟨13, by decide⟩).energy) (xi := (323286693923297 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13114 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13114]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13114])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13114) (a := (8361829642177 / 10000000000000 : ℝ)) (b := (39252410677 / 25000000000000 : ℝ)) (q := (1101588313707 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13114])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13114])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13114]

theorem cert13114_14 : CellCertificate 13114 (27358601619739 / 312500000000000 : ℝ) (1601663160278467 / 1000000000000000000 : ℝ) (323286693923297 / 10000000000000000 : ℝ)
    (cell13114 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · have h := gap_lower (n := 13114) (a := (8358372747533 / 10000000000000 : ℝ)) (b := (39252410677 / 25000000000000 : ℝ)) (q := (2203180677231 / 100000000000000 : ℝ))
      (E := (cell13114 ⟨14, by decide⟩).energy) (xi := (323286693923297 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13114 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13114]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13114])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13114) (a := (8358372747533 / 10000000000000 : ℝ)) (b := (39252410677 / 25000000000000 : ℝ)) (q := (2203180677231 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13114])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13114])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13114]

theorem cert13114_15 : CellCertificate 13114 (27358601619739 / 312500000000000 : ℝ) (1601663160278467 / 1000000000000000000 : ℝ) (323286693923297 / 10000000000000000 : ℝ)
    (cell13114 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · have h := gap_lower (n := 13114) (a := (83549182885249 / 100000000000000 : ℝ)) (b := (39252410677 / 25000000000000 : ℝ)) (q := (2203184643571 / 100000000000000 : ℝ))
      (E := (cell13114 ⟨15, by decide⟩).energy) (xi := (323286693923297 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13114 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13114]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13114])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13114) (a := (83549182885249 / 100000000000000 : ℝ)) (b := (39252410677 / 25000000000000 : ℝ)) (q := (2203184643571 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13114])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13114])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13114]

theorem cert13114_16 : CellCertificate 13114 (27358601619739 / 312500000000000 : ℝ) (1601663160278467 / 1000000000000000000 : ℝ) (323286693923297 / 10000000000000000 : ℝ)
    (cell13114 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · have h := gap_lower (n := 13114) (a := (20878665654419 / 25000000000000 : ℝ)) (b := (39252410677 / 25000000000000 : ℝ)) (q := (275398588253 / 12500000000000 : ℝ))
      (E := (cell13114 ⟨16, by decide⟩).energy) (xi := (323286693923297 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13114 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13114]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13114])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13114) (a := (20878665654419 / 25000000000000 : ℝ)) (b := (39252410677 / 25000000000000 : ℝ)) (q := (275398588253 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13114])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13114])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13114]

theorem cert13114_17 : CellCertificate 13114 (27358601619739 / 312500000000000 : ℝ) (1601663160278467 / 1000000000000000000 : ℝ) (323286693923297 / 10000000000000000 : ℝ)
    (cell13114 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · have h := gap_lower (n := 13114) (a := (16696033327787 / 20000000000000 : ℝ)) (b := (39252410677 / 25000000000000 : ℝ)) (q := (220319269473 / 10000000000000 : ℝ))
      (E := (cell13114 ⟨17, by decide⟩).energy) (xi := (323286693923297 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13114 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13114]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13114])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13114) (a := (16696033327787 / 20000000000000 : ℝ)) (b := (39252410677 / 25000000000000 : ℝ)) (q := (220319269473 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13114])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13114])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13114]

theorem cert13114_18 : CellCertificate 13114 (27358601619739 / 312500000000000 : ℝ) (1601663160278467 / 1000000000000000000 : ℝ) (323286693923297 / 10000000000000000 : ℝ)
    (cell13114 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · have h := gap_lower (n := 13114) (a := (20861423728881 / 25000000000000 : ℝ)) (b := (39252410677 / 25000000000000 : ℝ)) (q := (440639346133 / 20000000000000 : ℝ))
      (E := (cell13114 ⟨18, by decide⟩).energy) (xi := (323286693923297 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13114 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13114]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13114])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13114) (a := (20861423728881 / 25000000000000 : ℝ)) (b := (39252410677 / 25000000000000 : ℝ)) (q := (440639346133 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13114])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13114])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13114]

theorem cert13114_19 : CellCertificate 13114 (27358601619739 / 312500000000000 : ℝ) (1601663160278467 / 1000000000000000000 : ℝ) (323286693923297 / 10000000000000000 : ℝ)
    (cell13114 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · have h := gap_lower (n := 13114) (a := (83411247414113 / 100000000000000 : ℝ)) (b := (39252410677 / 25000000000000 : ℝ)) (q := (2203200701573 / 100000000000000 : ℝ))
      (E := (cell13114 ⟨19, by decide⟩).energy) (xi := (323286693923297 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13114 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13114]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13114])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13114) (a := (83411247414113 / 100000000000000 : ℝ)) (b := (39252410677 / 25000000000000 : ℝ)) (q := (2203200701573 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13114])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13114])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13114]

theorem cert13115_0 : CellCertificate 13115 (218862245861681 / 2500000000000000 : ℝ) (1601540996869179 / 1000000000000000000 : ℝ) (323261478512109 / 10000000000000000 : ℝ)
    (cell13115 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · have h := gap_lower (n := 13115) (a := (1313592354611 / 1562500000000 : ℝ)) (b := (156997533683 / 100000000000000 : ℝ)) (q := (2203012782399 / 100000000000000 : ℝ))
      (E := (cell13115 ⟨0, by decide⟩).energy) (xi := (323261478512109 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13115 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13115]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13115])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13115) (a := (1313592354611 / 1562500000000 : ℝ)) (b := (156997533683 / 100000000000000 : ℝ)) (q := (2203012782399 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13115])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13115])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13115]

theorem cert13115_1 : CellCertificate 13115 (218862245861681 / 2500000000000000 : ℝ) (1601540996869179 / 1000000000000000000 : ℝ) (323261478512109 / 10000000000000000 : ℝ)
    (cell13115 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · have h := gap_lower (n := 13115) (a := (84035021960127 / 100000000000000 : ℝ)) (b := (156997533683 / 100000000000000 : ℝ)) (q := (2203016798791 / 100000000000000 : ℝ))
      (E := (cell13115 ⟨1, by decide⟩).energy) (xi := (323261478512109 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13115 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13115]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13115])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13115) (a := (84035021960127 / 100000000000000 : ℝ)) (b := (156997533683 / 100000000000000 : ℝ)) (q := (2203016798791 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13115])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13115])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13115]

theorem cert13115_2 : CellCertificate 13115 (218862245861681 / 2500000000000000 : ℝ) (1601540996869179 / 1000000000000000000 : ℝ) (323261478512109 / 10000000000000000 : ℝ)
    (cell13115 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · have h := gap_lower (n := 13115) (a := (84000158038021 / 100000000000000 : ℝ)) (b := (156997533683 / 100000000000000 : ℝ)) (q := (137688801103 / 6250000000000 : ℝ))
      (E := (cell13115 ⟨2, by decide⟩).energy) (xi := (323261478512109 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13115 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13115]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13115])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13115) (a := (84000158038021 / 100000000000000 : ℝ)) (b := (156997533683 / 100000000000000 : ℝ)) (q := (137688801103 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13115])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13115])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13115]

theorem cert13115_3 : CellCertificate 13115 (218862245861681 / 2500000000000000 : ℝ) (1601540996869179 / 1000000000000000000 : ℝ) (323261478512109 / 10000000000000000 : ℝ)
    (cell13115 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · have h := gap_lower (n := 13115) (a := (10495664861569 / 12500000000000 : ℝ)) (b := (156997533683 / 100000000000000 : ℝ)) (q := (137689049339 / 6250000000000 : ℝ))
      (E := (cell13115 ⟨3, by decide⟩).energy) (xi := (323261478512109 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13115 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13115]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13115])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13115) (a := (10495664861569 / 12500000000000 : ℝ)) (b := (156997533683 / 100000000000000 : ℝ)) (q := (137689049339 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13115])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13115])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13115]

theorem cert13115_4 : CellCertificate 13115 (218862245861681 / 2500000000000000 : ℝ) (1601540996869179 / 1000000000000000000 : ℝ) (323261478512109 / 10000000000000000 : ℝ)
    (cell13115 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · have h := gap_lower (n := 13115) (a := (41965252243839 / 50000000000000 : ℝ)) (b := (156997533683 / 100000000000000 : ℝ)) (q := (275378604757 / 12500000000000 : ℝ))
      (E := (cell13115 ⟨4, by decide⟩).energy) (xi := (323261478512109 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13115 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13115]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13115])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13115) (a := (41965252243839 / 50000000000000 : ℝ)) (b := (156997533683 / 100000000000000 : ℝ)) (q := (275378604757 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13115])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13115])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13115]

theorem cert13115_5 : CellCertificate 13115 (218862245861681 / 2500000000000000 : ℝ) (1601540996869179 / 1000000000000000000 : ℝ) (323261478512109 / 10000000000000000 : ℝ)
    (cell13115 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · have h := gap_lower (n := 13115) (a := (83895714787547 / 100000000000000 : ℝ)) (b := (156997533683 / 100000000000000 : ℝ)) (q := (110151642777 / 5000000000000 : ℝ))
      (E := (cell13115 ⟨5, by decide⟩).energy) (xi := (323261478512109 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13115 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13115]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13115])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13115) (a := (83895714787547 / 100000000000000 : ℝ)) (b := (156997533683 / 100000000000000 : ℝ)) (q := (110151642777 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13115])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13115])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13115]

theorem cert13115_6 : CellCertificate 13115 (218862245861681 / 2500000000000000 : ℝ) (1601540996869179 / 1000000000000000000 : ℝ) (323261478512109 / 10000000000000000 : ℝ)
    (cell13115 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · have h := gap_lower (n := 13115) (a := (83860949756493 / 100000000000000 : ℝ)) (b := (156997533683 / 100000000000000 : ℝ)) (q := (2203036849417 / 100000000000000 : ℝ))
      (E := (cell13115 ⟨6, by decide⟩).energy) (xi := (323261478512109 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13115 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13115]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13115])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13115) (a := (83860949756493 / 100000000000000 : ℝ)) (b := (156997533683 / 100000000000000 : ℝ)) (q := (2203036849417 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13115])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13115])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13115]

theorem cert13115_7 : CellCertificate 13115 (218862245861681 / 2500000000000000 : ℝ) (1601540996869179 / 1000000000000000000 : ℝ) (323261478512109 / 10000000000000000 : ℝ)
    (cell13115 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · have h := gap_lower (n := 13115) (a := (83826209359039 / 100000000000000 : ℝ)) (b := (156997533683 / 100000000000000 : ℝ)) (q := (2203040826969 / 100000000000000 : ℝ))
      (E := (cell13115 ⟨7, by decide⟩).energy) (xi := (323261478512109 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13115 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13115]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13115])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13115) (a := (83826209359039 / 100000000000000 : ℝ)) (b := (156997533683 / 100000000000000 : ℝ)) (q := (2203040826969 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13115])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13115])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13115]

theorem cert13115_8 : CellCertificate 13115 (218862245861681 / 2500000000000000 : ℝ) (1601540996869179 / 1000000000000000000 : ℝ) (323261478512109 / 10000000000000000 : ℝ)
    (cell13115 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · have h := gap_lower (n := 13115) (a := (83791493559891 / 100000000000000 : ℝ)) (b := (156997533683 / 100000000000000 : ℝ)) (q := (2203044853267 / 100000000000000 : ℝ))
      (E := (cell13115 ⟨8, by decide⟩).energy) (xi := (323261478512109 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13115 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13115]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13115])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13115) (a := (83791493559891 / 100000000000000 : ℝ)) (b := (156997533683 / 100000000000000 : ℝ)) (q := (2203044853267 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13115])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13115])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13115]

theorem cert13115_9 : CellCertificate 13115 (218862245861681 / 2500000000000000 : ℝ) (1601540996869179 / 1000000000000000000 : ℝ) (323261478512109 / 10000000000000000 : ℝ)
    (cell13115 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · have h := gap_lower (n := 13115) (a := (41878401161971 / 50000000000000 : ℝ)) (b := (156997533683 / 100000000000000 : ℝ)) (q := (1101524438551 / 50000000000000 : ℝ))
      (E := (cell13115 ⟨9, by decide⟩).energy) (xi := (323261478512109 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13115 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13115]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13115])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13115) (a := (41878401161971 / 50000000000000 : ℝ)) (b := (156997533683 / 100000000000000 : ℝ)) (q := (1101524438551 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13115])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13115])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13115]

theorem cert13115_10 : CellCertificate 13115 (218862245861681 / 2500000000000000 : ℝ) (1601540996869179 / 1000000000000000000 : ℝ) (323261478512109 / 10000000000000000 : ℝ)
    (cell13115 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · have h := gap_lower (n := 13115) (a := (16744427123253 / 20000000000000 : ℝ)) (b := (156997533683 / 100000000000000 : ℝ)) (q := (2203052905007 / 100000000000000 : ℝ))
      (E := (cell13115 ⟨10, by decide⟩).energy) (xi := (323261478512109 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13115 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13115]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13115])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13115) (a := (16744427123253 / 20000000000000 : ℝ)) (b := (156997533683 / 100000000000000 : ℝ)) (q := (2203052905007 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13115])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13115])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13115]

theorem cert13115_11 : CellCertificate 13115 (218862245861681 / 2500000000000000 : ℝ) (1601540996869179 / 1000000000000000000 : ℝ) (323261478512109 / 10000000000000000 : ℝ)
    (cell13115 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · have h := gap_lower (n := 13115) (a := (83687493402119 / 100000000000000 : ℝ)) (b := (156997533683 / 100000000000000 : ℝ)) (q := (440611377031 / 20000000000000 : ℝ))
      (E := (cell13115 ⟨11, by decide⟩).energy) (xi := (323261478512109 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13115 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13115]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13115])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13115) (a := (83687493402119 / 100000000000000 : ℝ)) (b := (156997533683 / 100000000000000 : ℝ)) (q := (440611377031 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13115])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13115])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13115]

theorem cert13115_12 : CellCertificate 13115 (218862245861681 / 2500000000000000 : ℝ) (1601540996869179 / 1000000000000000000 : ℝ) (323261478512109 / 10000000000000000 : ℝ)
    (cell13115 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · have h := gap_lower (n := 13115) (a := (4182643782347 / 5000000000000 : ℝ)) (b := (156997533683 / 100000000000000 : ℝ)) (q := (550765220411 / 25000000000000 : ℝ))
      (E := (cell13115 ⟨12, by decide⟩).energy) (xi := (323261478512109 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13115 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13115]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13115])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13115) (a := (4182643782347 / 5000000000000 : ℝ)) (b := (156997533683 / 100000000000000 : ℝ)) (q := (550765220411 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13115])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13115])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13115]

theorem cert13115_13 : CellCertificate 13115 (218862245861681 / 2500000000000000 : ℝ) (1601540996869179 / 1000000000000000000 : ℝ) (323261478512109 / 10000000000000000 : ℝ)
    (cell13115 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · have h := gap_lower (n := 13115) (a := (41809141158173 / 50000000000000 : ℝ)) (b := (156997533683 / 100000000000000 : ℝ)) (q := (1101532450131 / 50000000000000 : ℝ))
      (E := (cell13115 ⟨13, by decide⟩).energy) (xi := (323261478512109 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13115 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13115]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13115])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13115) (a := (41809141158173 / 50000000000000 : ℝ)) (b := (156997533683 / 100000000000000 : ℝ)) (q := (1101532450131 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13115])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13115])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13115]

theorem cert13115_14 : CellCertificate 13115 (218862245861681 / 2500000000000000 : ℝ) (1601540996869179 / 1000000000000000000 : ℝ) (323261478512109 / 10000000000000000 : ℝ)
    (cell13115 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · have h := gap_lower (n := 13115) (a := (20895928344033 / 25000000000000 : ℝ)) (b := (156997533683 / 100000000000000 : ℝ)) (q := (2203068946553 / 100000000000000 : ℝ))
      (E := (cell13115 ⟨14, by decide⟩).energy) (xi := (323261478512109 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13115 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13115]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13115])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13115) (a := (20895928344033 / 25000000000000 : ℝ)) (b := (156997533683 / 100000000000000 : ℝ)) (q := (2203068946553 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13115])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13115])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13115]

theorem cert13115_15 : CellCertificate 13115 (218862245861681 / 2500000000000000 : ℝ) (1601540996869179 / 1000000000000000000 : ℝ) (323261478512109 / 10000000000000000 : ℝ)
    (cell13115 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · have h := gap_lower (n := 13115) (a := (83549168792271 / 100000000000000 : ℝ)) (b := (156997533683 / 100000000000000 : ℝ)) (q := (34423015119 / 1562500000000 : ℝ))
      (E := (cell13115 ⟨15, by decide⟩).energy) (xi := (323261478512109 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13115 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13115]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13115])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13115) (a := (83549168792271 / 100000000000000 : ℝ)) (b := (156997533683 / 100000000000000 : ℝ)) (q := (34423015119 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13115])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13115])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13115]

theorem cert13115_16 : CellCertificate 13115 (218862245861681 / 2500000000000000 : ℝ) (1601540996869179 / 1000000000000000000 : ℝ) (323261478512109 / 10000000000000000 : ℝ)
    (cell13115 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · have h := gap_lower (n := 13115) (a := (83514648530913 / 100000000000000 : ℝ)) (b := (156997533683 / 100000000000000 : ℝ)) (q := (550769242109 / 25000000000000 : ℝ))
      (E := (cell13115 ⟨16, by decide⟩).energy) (xi := (323261478512109 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13115 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13115]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13115])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13115) (a := (83514648530913 / 100000000000000 : ℝ)) (b := (156997533683 / 100000000000000 : ℝ)) (q := (550769242109 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13115])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13115])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13115]

theorem cert13115_17 : CellCertificate 13115 (218862245861681 / 2500000000000000 : ℝ) (1601540996869179 / 1000000000000000000 : ℝ) (323261478512109 / 10000000000000000 : ℝ)
    (cell13115 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · have h := gap_lower (n := 13115) (a := (83480152558381 / 100000000000000 : ℝ)) (b := (156997533683 / 100000000000000 : ℝ)) (q := (2203080953757 / 100000000000000 : ℝ))
      (E := (cell13115 ⟨17, by decide⟩).energy) (xi := (323261478512109 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13115 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13115]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13115])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13115) (a := (83480152558381 / 100000000000000 : ℝ)) (b := (156997533683 / 100000000000000 : ℝ)) (q := (2203080953757 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13115])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13115])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13115]

theorem cert13115_18 : CellCertificate 13115 (218862245861681 / 2500000000000000 : ℝ) (1601540996869179 / 1000000000000000000 : ℝ) (323261478512109 / 10000000000000000 : ℝ)
    (cell13115 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · have h := gap_lower (n := 13115) (a := (83445680841173 / 100000000000000 : ℝ)) (b := (156997533683 / 100000000000000 : ℝ)) (q := (1101542493177 / 50000000000000 : ℝ))
      (E := (cell13115 ⟨18, by decide⟩).energy) (xi := (323261478512109 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13115 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13115]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13115])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13115) (a := (83445680841173 / 100000000000000 : ℝ)) (b := (156997533683 / 100000000000000 : ℝ)) (q := (1101542493177 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13115])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13115])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13115]

theorem cert13115_19 : CellCertificate 13115 (218862245861681 / 2500000000000000 : ℝ) (1601540996869179 / 1000000000000000000 : ℝ) (323261478512109 / 10000000000000000 : ℝ)
    (cell13115 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · have h := gap_lower (n := 13115) (a := (83411233345961 / 100000000000000 : ℝ)) (b := (156997533683 / 100000000000000 : ℝ)) (q := (2203089012263 / 100000000000000 : ℝ))
      (E := (cell13115 ⟨19, by decide⟩).energy) (xi := (323261478512109 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13115 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13115]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13115])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13115) (a := (83411233345961 / 100000000000000 : ℝ)) (b := (156997533683 / 100000000000000 : ℝ)) (q := (2203089012263 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13115])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13115])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13115]

theorem cert13116_0 : CellCertificate 13116 (87542271889563 / 1000000000000000 : ℝ) (160141885209397 / 100000000000000000 : ℝ) (80809066765489 / 2500000000000000 : ℝ)
    (cell13116 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · have h := gap_lower (n := 13116) (a := (8406989651041 / 10000000000000 : ℝ)) (b := (39246356633 / 25000000000000 : ℝ)) (q := (68840657601 / 3125000000000 : ℝ))
      (E := (cell13116 ⟨0, by decide⟩).energy) (xi := (80809066765489 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13116 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13116]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13116])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13116) (a := (8406989651041 / 10000000000000 : ℝ)) (b := (39246356633 / 25000000000000 : ℝ)) (q := (68840657601 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13116])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13116])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13116]

theorem cert13116_1 : CellCertificate 13116 (87542271889563 / 1000000000000000 : ℝ) (160141885209397 / 100000000000000000 : ℝ) (80809066765489 / 2500000000000000 : ℝ)
    (cell13116 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · have h := gap_lower (n := 13116) (a := (8403500778173 / 10000000000000 : ℝ)) (b := (39246356633 / 25000000000000 : ℝ)) (q := (1101452527733 / 50000000000000 : ℝ))
      (E := (cell13116 ⟨1, by decide⟩).energy) (xi := (80809066765489 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13116 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13116]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13116])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13116) (a := (8403500778173 / 10000000000000 : ℝ)) (b := (39246356633 / 25000000000000 : ℝ)) (q := (1101452527733 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13116])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13116])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13116]

theorem cert13116_2 : CellCertificate 13116 (87542271889563 / 1000000000000000 : ℝ) (160141885209397 / 100000000000000000 : ℝ) (80809066765489 / 2500000000000000 : ℝ)
    (cell13116 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · have h := gap_lower (n := 13116) (a := (16800028773183 / 20000000000000 : ℝ)) (b := (39246356633 / 25000000000000 : ℝ)) (q := (550727267553 / 25000000000000 : ℝ))
      (E := (cell13116 ⟨2, by decide⟩).energy) (xi := (80809066765489 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13116 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13116]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13116])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13116) (a := (16800028773183 / 20000000000000 : ℝ)) (b := (39246356633 / 25000000000000 : ℝ)) (q := (550727267553 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13116])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13116])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13116]

theorem cert13116_3 : CellCertificate 13116 (87542271889563 / 1000000000000000 : ℝ) (160141885209397 / 100000000000000000 : ℝ) (80809066765489 / 2500000000000000 : ℝ)
    (cell13116 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · have h := gap_lower (n := 13116) (a := (20991326181683 / 25000000000000 : ℝ)) (b := (39246356633 / 25000000000000 : ℝ)) (q := (440582619169 / 20000000000000 : ℝ))
      (E := (cell13116 ⟨3, by decide⟩).energy) (xi := (80809066765489 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13116 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13116]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13116])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13116) (a := (20991326181683 / 25000000000000 : ℝ)) (b := (39246356633 / 25000000000000 : ℝ)) (q := (440582619169 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13116])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13116])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13116]

theorem cert13116_4 : CellCertificate 13116 (87542271889563 / 1000000000000000 : ℝ) (160141885209397 / 100000000000000000 : ℝ) (80809066765489 / 2500000000000000 : ℝ)
    (cell13116 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · have h := gap_lower (n := 13116) (a := (41965245164069 / 50000000000000 : ℝ)) (b := (39246356633 / 25000000000000 : ℝ)) (q := (2202917140483 / 100000000000000 : ℝ))
      (E := (cell13116 ⟨4, by decide⟩).energy) (xi := (80809066765489 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13116 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13116]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13116])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13116) (a := (41965245164069 / 50000000000000 : ℝ)) (b := (39246356633 / 25000000000000 : ℝ)) (q := (2202917140483 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13116])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13116])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13116]

theorem cert13116_5 : CellCertificate 13116 (87542271889563 / 1000000000000000 : ℝ) (160141885209397 / 100000000000000000 : ℝ) (80809066765489 / 2500000000000000 : ℝ)
    (cell13116 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · have h := gap_lower (n := 13116) (a := (41947850317141 / 50000000000000 : ℝ)) (b := (39246356633 / 25000000000000 : ℝ)) (q := (1101460548027 / 50000000000000 : ℝ))
      (E := (cell13116 ⟨5, by decide⟩).energy) (xi := (80809066765489 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13116 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13116]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13116])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13116) (a := (41947850317141 / 50000000000000 : ℝ)) (b := (39246356633 / 25000000000000 : ℝ)) (q := (1101460548027 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13116])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13116])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13116]

theorem cert13116_6 : CellCertificate 13116 (87542271889563 / 1000000000000000 : ℝ) (160141885209397 / 100000000000000000 : ℝ) (80809066765489 / 2500000000000000 : ℝ)
    (cell13116 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · have h := gap_lower (n := 13116) (a := (83860935609497 / 100000000000000 : ℝ)) (b := (39246356633 / 25000000000000 : ℝ)) (q := (1101462571999 / 50000000000000 : ℝ))
      (E := (cell13116 ⟨6, by decide⟩).energy) (xi := (80809066765489 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13116 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13116]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13116])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13116) (a := (83860935609497 / 100000000000000 : ℝ)) (b := (39246356633 / 25000000000000 : ℝ)) (q := (1101462571999 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13116])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13116])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13116]

theorem cert13116_7 : CellCertificate 13116 (87542271889563 / 1000000000000000 : ℝ) (160141885209397 / 100000000000000000 : ℝ) (80809066765489 / 2500000000000000 : ℝ)
    (cell13116 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · have h := gap_lower (n := 13116) (a := (41913097609153 / 50000000000000 : ℝ)) (b := (39246356633 / 25000000000000 : ℝ)) (q := (68841536741 / 3125000000000 : ℝ))
      (E := (cell13116 ⟨7, by decide⟩).energy) (xi := (80809066765489 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13116 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13116]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13116])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13116) (a := (41913097609153 / 50000000000000 : ℝ)) (b := (39246356633 / 25000000000000 : ℝ)) (q := (68841536741 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13116])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13116])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13116]

theorem cert13116_8 : CellCertificate 13116 (87542271889563 / 1000000000000000 : ℝ) (160141885209397 / 100000000000000000 : ℝ) (80809066765489 / 2500000000000000 : ℝ)
    (cell13116 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · have h := gap_lower (n := 13116) (a := (10473934928177 / 12500000000000 : ℝ)) (b := (39246356633 / 25000000000000 : ℝ)) (q := (2202933140191 / 100000000000000 : ℝ))
      (E := (cell13116 ⟨8, by decide⟩).energy) (xi := (80809066765489 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13116 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13116]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13116])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13116) (a := (10473934928177 / 12500000000000 : ℝ)) (b := (39246356633 / 25000000000000 : ℝ)) (q := (2202933140191 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13116])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13116])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13116]

theorem cert13116_9 : CellCertificate 13116 (87542271889563 / 1000000000000000 : ℝ) (160141885209397 / 100000000000000000 : ℝ) (80809066765489 / 2500000000000000 : ℝ)
    (cell13116 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · have h := gap_lower (n := 13116) (a := (41878394097859 / 50000000000000 : ℝ)) (b := (39246356633 / 25000000000000 : ℝ)) (q := (550734290067 / 25000000000000 : ℝ))
      (E := (cell13116 ⟨9, by decide⟩).energy) (xi := (80809066765489 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13116 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13116]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13116])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13116) (a := (41878394097859 / 50000000000000 : ℝ)) (b := (39246356633 / 25000000000000 : ℝ)) (q := (550734290067 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13116])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13116])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13116]

theorem cert13116_10 : CellCertificate 13116 (87542271889563 / 1000000000000000 : ℝ) (160141885209397 / 100000000000000000 : ℝ) (80809066765489 / 2500000000000000 : ℝ)
    (cell13116 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · have h := gap_lower (n := 13116) (a := (5232632593393 / 6250000000000 : ℝ)) (b := (39246356633 / 25000000000000 : ℝ)) (q := (2202941184461 / 100000000000000 : ℝ))
      (E := (cell13116 ⟨10, by decide⟩).energy) (xi := (80809066765489 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13116 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13116]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13116])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13116) (a := (5232632593393 / 6250000000000 : ℝ)) (b := (39246356633 / 25000000000000 : ℝ)) (q := (2202941184461 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13116])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13116])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13116]

theorem cert13116_11 : CellCertificate 13116 (87542271889563 / 1000000000000000 : ℝ) (160141885209397 / 100000000000000000 : ℝ) (80809066765489 / 2500000000000000 : ℝ)
    (cell13116 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · have h := gap_lower (n := 13116) (a := (83687479286383 / 100000000000000 : ℝ)) (b := (39246356633 / 25000000000000 : ℝ)) (q := (550736304763 / 25000000000000 : ℝ))
      (E := (cell13116 ⟨11, by decide⟩).energy) (xi := (80809066765489 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13116 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13116]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13116])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13116) (a := (83687479286383 / 100000000000000 : ℝ)) (b := (39246356633 / 25000000000000 : ℝ)) (q := (550736304763 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13116])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13116])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13116]

theorem cert13116_12 : CellCertificate 13116 (87542271889563 / 1000000000000000 : ℝ) (160141885209397 / 100000000000000000 : ℝ) (80809066765489 / 2500000000000000 : ℝ)
    (cell13116 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · have h := gap_lower (n := 13116) (a := (522830384609 / 625000000000 : ℝ)) (b := (39246356633 / 25000000000000 : ℝ)) (q := (440589842389 / 20000000000000 : ℝ))
      (E := (cell13116 ⟨12, by decide⟩).energy) (xi := (80809066765489 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13116 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13116]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13116])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13116) (a := (522830384609 / 625000000000 : ℝ)) (b := (39246356633 / 25000000000000 : ℝ)) (q := (440589842389 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13116])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13116])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13116]

theorem cert13116_13 : CellCertificate 13116 (87542271889563 / 1000000000000000 : ℝ) (160141885209397 / 100000000000000000 : ℝ) (80809066765489 / 2500000000000000 : ℝ)
    (cell13116 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · have h := gap_lower (n := 13116) (a := (20904567053269 / 25000000000000 : ℝ)) (b := (39246356633 / 25000000000000 : ℝ)) (q := (275369153377 / 12500000000000 : ℝ))
      (E := (cell13116 ⟨13, by decide⟩).energy) (xi := (80809066765489 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13116 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13116]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13116])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13116) (a := (20904567053269 / 25000000000000 : ℝ)) (b := (39246356633 / 25000000000000 : ℝ)) (q := (275369153377 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13116])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13116])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13116]

theorem cert13116_14 : CellCertificate 13116 (87542271889563 / 1000000000000000 : ℝ) (160141885209397 / 100000000000000000 : ℝ) (80809066765489 / 2500000000000000 : ℝ)
    (cell13116 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · have h := gap_lower (n := 13116) (a := (41791849639543 / 50000000000000 : ℝ)) (b := (39246356633 / 25000000000000 : ℝ)) (q := (2202957211629 / 100000000000000 : ℝ))
      (E := (cell13116 ⟨14, by decide⟩).energy) (xi := (80809066765489 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13116 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13116]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13116])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13116) (a := (41791849639543 / 50000000000000 : ℝ)) (b := (39246356633 / 25000000000000 : ℝ)) (q := (2202957211629 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13116])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13116])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13116]

theorem cert13116_15 : CellCertificate 13116 (87542271889563 / 1000000000000000 : ℝ) (160141885209397 / 100000000000000000 : ℝ) (80809066765489 / 2500000000000000 : ℝ)
    (cell13116 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · have h := gap_lower (n := 13116) (a := (16709830940289 / 20000000000000 : ℝ)) (b := (39246356633 / 25000000000000 : ℝ)) (q := (2202961229213 / 100000000000000 : ℝ))
      (E := (cell13116 ⟨15, by decide⟩).energy) (xi := (80809066765489 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13116 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13116]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13116])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13116) (a := (16709830940289 / 20000000000000 : ℝ)) (b := (39246356633 / 25000000000000 : ℝ)) (q := (2202961229213 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13116])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13116])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13116]

theorem cert13116_16 : CellCertificate 13116 (87542271889563 / 1000000000000000 : ℝ) (160141885209397 / 100000000000000000 : ℝ) (80809066765489 / 2500000000000000 : ℝ)
    (cell13116 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · have h := gap_lower (n := 13116) (a := (835146344463 / 1000000000000 : ℝ)) (b := (39246356633 / 25000000000000 : ℝ)) (q := (1101482613301 / 50000000000000 : ℝ))
      (E := (cell13116 ⟨16, by decide⟩).energy) (xi := (80809066765489 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13116 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13116]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13116])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13116) (a := (835146344463 / 1000000000000 : ℝ)) (b := (39246356633 / 25000000000000 : ℝ)) (q := (1101482613301 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13116])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13116])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13116]

theorem cert13116_17 : CellCertificate 13116 (87542271889563 / 1000000000000000 : ℝ) (160141885209397 / 100000000000000000 : ℝ) (80809066765489 / 2500000000000000 : ℝ)
    (cell13116 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · have h := gap_lower (n := 13116) (a := (10435017309997 / 12500000000000 : ℝ)) (b := (39246356633 / 25000000000000 : ℝ)) (q := (2202969266787 / 100000000000000 : ℝ))
      (E := (cell13116 ⟨17, by decide⟩).energy) (xi := (80809066765489 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13116 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13116]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13116])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13116) (a := (10435017309997 / 12500000000000 : ℝ)) (b := (39246356633 / 25000000000000 : ℝ)) (q := (2202969266787 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13116])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13116])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13116]

theorem cert13116_18 : CellCertificate 13116 (87542271889563 / 1000000000000000 : ℝ) (160141885209397 / 100000000000000000 : ℝ) (80809066765489 / 2500000000000000 : ℝ)
    (cell13116 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · have h := gap_lower (n := 13116) (a := (20861416692243 / 25000000000000 : ℝ)) (b := (39246356633 / 25000000000000 : ℝ)) (q := (550743324017 / 25000000000000 : ℝ))
      (E := (cell13116 ⟨18, by decide⟩).energy) (xi := (80809066765489 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13116 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13116]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13116])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13116) (a := (20861416692243 / 25000000000000 : ℝ)) (b := (39246356633 / 25000000000000 : ℝ)) (q := (550743324017 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13116])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13116])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13116]

theorem cert13116_19 : CellCertificate 13116 (87542271889563 / 1000000000000000 : ℝ) (160141885209397 / 100000000000000000 : ℝ) (80809066765489 / 2500000000000000 : ℝ)
    (cell13116 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · have h := gap_lower (n := 13116) (a := (83411219279957 / 100000000000000 : ℝ)) (b := (39246356633 / 25000000000000 : ℝ)) (q := (2202977318711 / 100000000000000 : ℝ))
      (E := (cell13116 ⟨19, by decide⟩).energy) (xi := (80809066765489 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13116 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13116]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13116])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13116) (a := (83411219279957 / 100000000000000 : ℝ)) (b := (39246356633 / 25000000000000 : ℝ)) (q := (2202977318711 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13116])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13116])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13116]

theorem cert13117_0 : CellCertificate 13117 (175079291635497 / 2000000000000000 : ℝ) (50040522685893 / 31250000000000000 : ℝ) (6464221191437 / 200000000000000 : ℝ)
    (cell13117 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · have h := gap_lower (n := 13117) (a := (84069882327881 / 100000000000000 : ℝ)) (b := (31394664251 / 20000000000000 : ℝ)) (q := (1101394707753 / 50000000000000 : ℝ))
      (E := (cell13117 ⟨0, by decide⟩).energy) (xi := (6464221191437 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13117 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13117]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13117])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13117) (a := (84069882327881 / 100000000000000 : ℝ)) (b := (31394664251 / 20000000000000 : ℝ)) (q := (1101394707753 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13117])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13117])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13117]

theorem cert13117_1 : CellCertificate 13117 (175079291635497 / 2000000000000000 : ℝ) (50040522685893 / 31250000000000000 : ℝ) (6464221191437 / 200000000000000 : ℝ)
    (cell13117 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · have h := gap_lower (n := 13117) (a := (42017496802749 / 50000000000000 : ℝ)) (b := (31394664251 / 20000000000000 : ℝ)) (q := (2202793423629 / 100000000000000 : ℝ))
      (E := (cell13117 ⟨1, by decide⟩).energy) (xi := (6464221191437 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13117 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13117]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13117])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13117) (a := (42017496802749 / 50000000000000 : ℝ)) (b := (31394664251 / 20000000000000 : ℝ)) (q := (2202793423629 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13117])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13117])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13117]

theorem cert13117_2 : CellCertificate 13117 (175079291635497 / 2000000000000000 : ℝ) (50040522685893 / 31250000000000000 : ℝ) (6464221191437 / 200000000000000 : ℝ)
    (cell13117 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · have h := gap_lower (n := 13117) (a := (84000129695973 / 100000000000000 : ℝ)) (b := (31394664251 / 20000000000000 : ℝ)) (q := (275349679289 / 12500000000000 : ℝ))
      (E := (cell13117 ⟨2, by decide⟩).energy) (xi := (6464221191437 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13117 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13117]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13117])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13117) (a := (84000129695973 / 100000000000000 : ℝ)) (b := (31394664251 / 20000000000000 : ℝ)) (q := (275349679289 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13117])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13117])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13117]

theorem cert13117_3 : CellCertificate 13117 (175079291635497 / 2000000000000000 : ℝ) (50040522685893 / 31250000000000000 : ℝ) (6464221191437 / 200000000000000 : ℝ)
    (cell13117 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · have h := gap_lower (n := 13117) (a := (3358611622523 / 4000000000000 : ℝ)) (b := (31394664251 / 20000000000000 : ℝ)) (q := (275350174751 / 12500000000000 : ℝ))
      (E := (cell13117 ⟨3, by decide⟩).energy) (xi := (6464221191437 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13117 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13117]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13117])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13117) (a := (3358611622523 / 4000000000000 : ℝ)) (b := (31394664251 / 20000000000000 : ℝ)) (q := (275350174751 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13117])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13117])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13117]

theorem cert13117_4 : CellCertificate 13117 (175079291635497 / 2000000000000000 : ℝ) (50040522685893 / 31250000000000000 : ℝ) (6464221191437 / 200000000000000 : ℝ)
    (cell13117 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · have h := gap_lower (n := 13117) (a := (2098261904269 / 2500000000000 : ℝ)) (b := (31394664251 / 20000000000000 : ℝ)) (q := (1101402719327 / 50000000000000 : ℝ))
      (E := (cell13117 ⟨4, by decide⟩).energy) (xi := (6464221191437 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13117 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13117]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13117])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13117) (a := (2098261904269 / 2500000000000 : ℝ)) (b := (31394664251 / 20000000000000 : ℝ)) (q := (1101402719327 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13117])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13117])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13117]

theorem cert13117_5 : CellCertificate 13117 (175079291635497 / 2000000000000000 : ℝ) (50040522685893 / 31250000000000000 : ℝ) (6464221191437 / 200000000000000 : ℝ)
    (cell13117 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · have h := gap_lower (n := 13117) (a := (83895686483177 / 100000000000000 : ℝ)) (b := (31394664251 / 20000000000000 : ℝ)) (q := (2202809448247 / 100000000000000 : ℝ))
      (E := (cell13117 ⟨5, by decide⟩).energy) (xi := (6464221191437 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13117 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13117]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13117])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13117) (a := (83895686483177 / 100000000000000 : ℝ)) (b := (31394664251 / 20000000000000 : ℝ)) (q := (2202809448247 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13117])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13117])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13117]

theorem cert13117_6 : CellCertificate 13117 (175079291635497 / 2000000000000000 : ℝ) (50040522685893 / 31250000000000000 : ℝ) (6464221191437 / 200000000000000 : ℝ)
    (cell13117 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · have h := gap_lower (n := 13117) (a := (4193046073233 / 5000000000000 : ℝ)) (b := (31394664251 / 20000000000000 : ℝ)) (q := (1101406717163 / 50000000000000 : ℝ))
      (E := (cell13117 ⟨6, by decide⟩).energy) (xi := (6464221191437 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13117 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13117]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13117])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13117) (a := (4193046073233 / 5000000000000 : ℝ)) (b := (31394664251 / 20000000000000 : ℝ)) (q := (1101406717163 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13117])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13117])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13117]

theorem cert13117_7 : CellCertificate 13117 (175079291635497 / 2000000000000000 : ℝ) (50040522685893 / 31250000000000000 : ℝ) (6464221191437 / 200000000000000 : ℝ)
    (cell13117 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · have h := gap_lower (n := 13117) (a := (83826181079731 / 100000000000000 : ℝ)) (b := (31394664251 / 20000000000000 : ℝ)) (q := (2202817462189 / 100000000000000 : ℝ))
      (E := (cell13117 ⟨7, by decide⟩).energy) (xi := (6464221191437 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13117 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13117]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13117])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13117) (a := (83826181079731 / 100000000000000 : ℝ)) (b := (31394664251 / 20000000000000 : ℝ)) (q := (2202817462189 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13117])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13117])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13117]

theorem cert13117_8 : CellCertificate 13117 (175079291635497 / 2000000000000000 : ℝ) (50040522685893 / 31250000000000000 : ℝ) (6464221191437 / 200000000000000 : ℝ)
    (cell13117 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · have h := gap_lower (n := 13117) (a := (41895732646549 / 50000000000000 : ℝ)) (b := (31394664251 / 20000000000000 : ℝ)) (q := (22028214809 / 1000000000000 : ℝ))
      (E := (cell13117 ⟨8, by decide⟩).energy) (xi := (6464221191437 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13117 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13117]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13117])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13117) (a := (41895732646549 / 50000000000000 : ℝ)) (b := (31394664251 / 20000000000000 : ℝ)) (q := (22028214809 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13117])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13117])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13117]

theorem cert13117_9 : CellCertificate 13117 (175079291635497 / 2000000000000000 : ℝ) (50040522685893 / 31250000000000000 : ℝ) (6464221191437 / 200000000000000 : ℝ)
    (cell13117 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · have h := gap_lower (n := 13117) (a := (20939193517413 / 25000000000000 : ℝ)) (b := (31394664251 / 20000000000000 : ℝ)) (q := (1101412748621 / 50000000000000 : ℝ))
      (E := (cell13117 ⟨9, by decide⟩).energy) (xi := (6464221191437 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13117 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13117]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13117])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13117) (a := (20939193517413 / 25000000000000 : ℝ)) (b := (31394664251 / 20000000000000 : ℝ)) (q := (1101412748621 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13117])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13117])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13117]

theorem cert13117_10 : CellCertificate 13117 (175079291635497 / 2000000000000000 : ℝ) (50040522685893 / 31250000000000000 : ℝ) (6464221191437 / 200000000000000 : ℝ)
    (cell13117 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · have h := gap_lower (n := 13117) (a := (83722107374467 / 100000000000000 : ℝ)) (b := (31394664251 / 20000000000000 : ℝ)) (q := (550707379437 / 25000000000000 : ℝ))
      (E := (cell13117 ⟨10, by decide⟩).energy) (xi := (6464221191437 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13117 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13117]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13117])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13117) (a := (83722107374467 / 100000000000000 : ℝ)) (b := (31394664251 / 20000000000000 : ℝ)) (q := (550707379437 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13117])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13117])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13117]

theorem cert13117_11 : CellCertificate 13117 (175079291635497 / 2000000000000000 : ℝ) (50040522685893 / 31250000000000000 : ℝ) (6464221191437 / 200000000000000 : ℝ)
    (cell13117 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · have h := gap_lower (n := 13117) (a := (41843732586401 / 50000000000000 : ℝ)) (b := (31394664251 / 20000000000000 : ℝ)) (q := (2202833490591 / 100000000000000 : ℝ))
      (E := (cell13117 ⟨11, by decide⟩).energy) (xi := (6464221191437 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13117 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13117]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13117])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13117) (a := (41843732586401 / 50000000000000 : ℝ)) (b := (31394664251 / 20000000000000 : ℝ)) (q := (2202833490591 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13117])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13117])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13117]

theorem cert13117_12 : CellCertificate 13117 (175079291635497 / 2000000000000000 : ℝ) (50040522685893 / 31250000000000000 : ℝ) (6464221191437 / 200000000000000 : ℝ)
    (cell13117 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · have h := gap_lower (n := 13117) (a := (83652847430093 / 100000000000000 : ℝ)) (b := (31394664251 / 20000000000000 : ℝ)) (q := (2202837537999 / 100000000000000 : ℝ))
      (E := (cell13117 ⟨12, by decide⟩).energy) (xi := (6464221191437 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13117 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13117]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13117])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13117) (a := (83652847430093 / 100000000000000 : ℝ)) (b := (31394664251 / 20000000000000 : ℝ)) (q := (2202837537999 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13117])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13117])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13117]

theorem cert13117_13 : CellCertificate 13117 (175079291635497 / 2000000000000000 : ℝ) (50040522685893 / 31250000000000000 : ℝ) (6464221191437 / 200000000000000 : ℝ)
    (cell13117 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · have h := gap_lower (n := 13117) (a := (41809127055979 / 50000000000000 : ℝ)) (b := (31394664251 / 20000000000000 : ℝ)) (q := (1101420774761 / 50000000000000 : ℝ))
      (E := (cell13117 ⟨13, by decide⟩).energy) (xi := (6464221191437 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13117 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13117]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13117])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13117) (a := (41809127055979 / 50000000000000 : ℝ)) (b := (31394664251 / 20000000000000 : ℝ)) (q := (1101420774761 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13117])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13117])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13117]

theorem cert13117_14 : CellCertificate 13117 (175079291635497 / 2000000000000000 : ℝ) (50040522685893 / 31250000000000000 : ℝ) (6464221191437 / 200000000000000 : ℝ)
    (cell13117 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · have h := gap_lower (n := 13117) (a := (83583685184193 / 100000000000000 : ℝ)) (b := (31394664251 / 20000000000000 : ℝ)) (q := (2202845530633 / 100000000000000 : ℝ))
      (E := (cell13117 ⟨14, by decide⟩).energy) (xi := (6464221191437 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13117 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13117]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13117])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13117) (a := (83583685184193 / 100000000000000 : ℝ)) (b := (31394664251 / 20000000000000 : ℝ)) (q := (2202845530633 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13117])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13117])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13117]

theorem cert13117_15 : CellCertificate 13117 (175079291635497 / 2000000000000000 : ℝ) (50040522685893 / 31250000000000000 : ℝ) (6464221191437 / 200000000000000 : ℝ)
    (cell13117 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · have h := gap_lower (n := 13117) (a := (83549140612769 / 100000000000000 : ℝ)) (b := (31394664251 / 20000000000000 : ℝ)) (q := (440569908953 / 20000000000000 : ℝ))
      (E := (cell13117 ⟨15, by decide⟩).energy) (xi := (6464221191437 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13117 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13117]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13117])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13117) (a := (83549140612769 / 100000000000000 : ℝ)) (b := (31394664251 / 20000000000000 : ℝ)) (q := (440569908953 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13117])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13117])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13117]

theorem cert13117_16 : CellCertificate 13117 (175079291635497 / 2000000000000000 : ℝ) (50040522685893 / 31250000000000000 : ℝ) (6464221191437 / 200000000000000 : ℝ)
    (cell13117 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · have h := gap_lower (n := 13117) (a := (83514620363837 / 100000000000000 : ℝ)) (b := (31394664251 / 20000000000000 : ℝ)) (q := (550713399243 / 25000000000000 : ℝ))
      (E := (cell13117 ⟨16, by decide⟩).energy) (xi := (6464221191437 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13117 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13117]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13117])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13117) (a := (83514620363837 / 100000000000000 : ℝ)) (b := (31394664251 / 20000000000000 : ℝ)) (q := (550713399243 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13117])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13117])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13117]

theorem cert13117_17 : CellCertificate 13117 (175079291635497 / 2000000000000000 : ℝ) (50040522685893 / 31250000000000000 : ℝ) (6464221191437 / 200000000000000 : ℝ)
    (cell13117 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · have h := gap_lower (n := 13117) (a := (83480124403721 / 100000000000000 : ℝ)) (b := (31394664251 / 20000000000000 : ℝ)) (q := (2202857575571 / 100000000000000 : ℝ))
      (E := (cell13117 ⟨17, by decide⟩).energy) (xi := (6464221191437 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13117 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13117]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13117])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13117) (a := (83480124403721 / 100000000000000 : ℝ)) (b := (31394664251 / 20000000000000 : ℝ)) (q := (2202857575571 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13117])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13117])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13117]

theorem cert13117_18 : CellCertificate 13117 (175079291635497 / 2000000000000000 : ℝ) (50040522685893 / 31250000000000000 : ℝ) (6464221191437 / 200000000000000 : ℝ)
    (cell13117 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · have h := gap_lower (n := 13117) (a := (41722826349459 / 50000000000000 : ℝ)) (b := (31394664251 / 20000000000000 : ℝ)) (q := (110143080077 / 5000000000000 : ℝ))
      (E := (cell13117 ⟨18, by decide⟩).energy) (xi := (6464221191437 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13117 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13117]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13117])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13117) (a := (41722826349459 / 50000000000000 : ℝ)) (b := (31394664251 / 20000000000000 : ℝ)) (q := (110143080077 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13117])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13117])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13117]

theorem cert13117_19 : CellCertificate 13117 (175079291635497 / 2000000000000000 : ℝ) (50040522685893 / 31250000000000000 : ℝ) (6464221191437 / 200000000000000 : ℝ)
    (cell13117 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · have h := gap_lower (n := 13117) (a := (83411205216101 / 100000000000000 : ℝ)) (b := (31394664251 / 20000000000000 : ℝ)) (q := (1101432810457 / 50000000000000 : ℝ))
      (E := (cell13117 ⟨19, by decide⟩).energy) (xi := (6464221191437 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13117 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13117]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13117])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13117) (a := (83411205216101 / 100000000000000 : ℝ)) (b := (31394664251 / 20000000000000 : ℝ)) (q := (1101432810457 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13117])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13117])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13117]

theorem cert13118_0 : CellCertificate 13118 (87537020129141 / 1000000000000000 : ℝ) (1601174618428737 / 1000000000000000000 : ℝ) (323185856040807 / 10000000000000000 : ℝ)
    (cell13118 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · have h := gap_lower (n := 13118) (a := (84069868147517 / 100000000000000 : ℝ)) (b := (156961217851 / 100000000000000 : ℝ)) (q := (2202677725671 / 100000000000000 : ℝ))
      (E := (cell13118 ⟨0, by decide⟩).energy) (xi := (323185856040807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13118 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13118]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13118])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13118) (a := (84069868147517 / 100000000000000 : ℝ)) (b := (156961217851 / 100000000000000 : ℝ)) (q := (2202677725671 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13118])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13118])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13118]

theorem cert13118_1 : CellCertificate 13118 (87537020129141 / 1000000000000000 : ℝ) (1601174618428737 / 1000000000000000000 : ℝ) (323185856040807 / 10000000000000000 : ℝ)
    (cell13118 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · have h := gap_lower (n := 13118) (a := (84034979431429 / 100000000000000 : ℝ)) (b := (156961217851 / 100000000000000 : ℝ)) (q := (1101340864831 / 50000000000000 : ℝ))
      (E := (cell13118 ⟨1, by decide⟩).energy) (xi := (323185856040807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13118 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13118]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13118])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13118) (a := (84034979431429 / 100000000000000 : ℝ)) (b := (156961217851 / 100000000000000 : ℝ)) (q := (1101340864831 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13118])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13118])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13118]

theorem cert13118_2 : CellCertificate 13118 (87537020129141 / 1000000000000000 : ℝ) (1601174618428737 / 1000000000000000000 : ℝ) (323185856040807 / 10000000000000000 : ℝ)
    (cell13118 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · have h := gap_lower (n := 13118) (a := (42000057764097 / 50000000000000 : ℝ)) (b := (156961217851 / 100000000000000 : ℝ)) (q := (2202685736259 / 100000000000000 : ℝ))
      (E := (cell13118 ⟨2, by decide⟩).energy) (xi := (323185856040807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13118 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13118]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13118])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13118) (a := (42000057764097 / 50000000000000 : ℝ)) (b := (156961217851 / 100000000000000 : ℝ)) (q := (2202685736259 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13118])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13118])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13118]

theorem cert13118_3 : CellCertificate 13118 (87537020129141 / 1000000000000000 : ℝ) (1601174618428737 / 1000000000000000000 : ℝ) (323185856040807 / 10000000000000000 : ℝ)
    (cell13118 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · have h := gap_lower (n := 13118) (a := (83965276401579 / 100000000000000 : ℝ)) (b := (156961217851 / 100000000000000 : ℝ)) (q := (1101344876919 / 50000000000000 : ℝ))
      (E := (cell13118 ⟨3, by decide⟩).energy) (xi := (323185856040807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13118 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13118]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13118])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13118) (a := (83965276401579 / 100000000000000 : ℝ)) (b := (156961217851 / 100000000000000 : ℝ)) (q := (1101344876919 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13118])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13118])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13118]

theorem cert13118_4 : CellCertificate 13118 (87537020129141 / 1000000000000000 : ℝ) (1601174618428737 / 1000000000000000000 : ℝ) (323185856040807 / 10000000000000000 : ℝ)
    (cell13118 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · have h := gap_lower (n := 13118) (a := (83930462015543 / 100000000000000 : ℝ)) (b := (156961217851 / 100000000000000 : ℝ)) (q := (440538758103 / 20000000000000 : ℝ))
      (E := (cell13118 ⟨4, by decide⟩).energy) (xi := (323185856040807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13118 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13118]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13118])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13118) (a := (83930462015543 / 100000000000000 : ℝ)) (b := (156961217851 / 100000000000000 : ℝ)) (q := (440538758103 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13118])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13118])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13118]

theorem cert13118_5 : CellCertificate 13118 (87537020129141 / 1000000000000000 : ℝ) (1601174618428737 / 1000000000000000000 : ℝ) (323185856040807 / 10000000000000000 : ℝ)
    (cell13118 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · have h := gap_lower (n := 13118) (a := (83895672334233 / 100000000000000 : ℝ)) (b := (156961217851 / 100000000000000 : ℝ)) (q := (1101348898093 / 50000000000000 : ℝ))
      (E := (cell13118 ⟨5, by decide⟩).energy) (xi := (323185856040807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13118 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13118]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13118])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13118) (a := (83895672334233 / 100000000000000 : ℝ)) (b := (156961217851 / 100000000000000 : ℝ)) (q := (1101348898093 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13118])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13118])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13118]

theorem cert13118_6 : CellCertificate 13118 (87537020129141 / 1000000000000000 : ℝ) (1601174618428737 / 1000000000000000000 : ℝ) (323185856040807 / 10000000000000000 : ℝ)
    (cell13118 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · have h := gap_lower (n := 13118) (a := (83860907321983 / 100000000000000 : ℝ)) (b := (156961217851 / 100000000000000 : ℝ)) (q := (2202701778391 / 100000000000000 : ℝ))
      (E := (cell13118 ⟨6, by decide⟩).energy) (xi := (323185856040807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13118 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13118]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13118])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13118) (a := (83860907321983 / 100000000000000 : ℝ)) (b := (156961217851 / 100000000000000 : ℝ)) (q := (2202701778391 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13118])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13118])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13118]

theorem cert13118_7 : CellCertificate 13118 (87537020129141 / 1000000000000000 : ℝ) (1601174618428737 / 1000000000000000000 : ℝ) (323185856040807 / 10000000000000000 : ℝ)
    (cell13118 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · have h := gap_lower (n := 13118) (a := (16765233388663 / 20000000000000 : ℝ)) (b := (156961217851 / 100000000000000 : ℝ)) (q := (1101352901213 / 50000000000000 : ℝ))
      (E := (cell13118 ⟨7, by decide⟩).energy) (xi := (323185856040807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13118 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13118]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13118])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13118) (a := (16765233388663 / 20000000000000 : ℝ)) (b := (156961217851 / 100000000000000 : ℝ)) (q := (1101352901213 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13118])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13118])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13118]

theorem cert13118_8 : CellCertificate 13118 (87537020129141 / 1000000000000000 : ℝ) (1601174618428737 / 1000000000000000000 : ℝ) (323185856040807 / 10000000000000000 : ℝ)
    (cell13118 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · have h := gap_lower (n := 13118) (a := (83791451162937 / 100000000000000 : ℝ)) (b := (156961217851 / 100000000000000 : ℝ)) (q := (1101354908679 / 50000000000000 : ℝ))
      (E := (cell13118 ⟨8, by decide⟩).energy) (xi := (323185856040807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13118 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13118]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13118])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13118) (a := (83791451162937 / 100000000000000 : ℝ)) (b := (156961217851 / 100000000000000 : ℝ)) (q := (1101354908679 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13118])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13118])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13118]

theorem cert13118_9 : CellCertificate 13118 (87537020129141 / 1000000000000000 : ℝ) (1601174618428737 / 1000000000000000000 : ℝ) (323185856040807 / 10000000000000000 : ℝ)
    (cell13118 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · have h := gap_lower (n := 13118) (a := (83756759945741 / 100000000000000 : ℝ)) (b := (156961217851 / 100000000000000 : ℝ)) (q := (2202713829967 / 100000000000000 : ℝ))
      (E := (cell13118 ⟨9, by decide⟩).energy) (xi := (323185856040807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13118 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13118]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13118])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13118) (a := (83756759945741 / 100000000000000 : ℝ)) (b := (156961217851 / 100000000000000 : ℝ)) (q := (2202713829967 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13118])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13118])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13118]

theorem cert13118_10 : CellCertificate 13118 (87537020129141 / 1000000000000000 : ℝ) (1601174618428737 / 1000000000000000000 : ℝ) (323185856040807 / 10000000000000000 : ℝ)
    (cell13118 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · have h := gap_lower (n := 13118) (a := (41861046628401 / 50000000000000 : ℝ)) (b := (156961217851 / 100000000000000 : ℝ)) (q := (440543569357 / 20000000000000 : ℝ))
      (E := (cell13118 ⟨10, by decide⟩).energy) (xi := (323185856040807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13118 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13118]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13118])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13118) (a := (41861046628401 / 50000000000000 : ℝ)) (b := (156961217851 / 100000000000000 : ℝ)) (q := (440543569357 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13118])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13118])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13118]

theorem cert13118_11 : CellCertificate 13118 (87537020129141 / 1000000000000000 : ℝ) (1601174618428737 / 1000000000000000000 : ℝ) (323185856040807 / 10000000000000000 : ℝ)
    (cell13118 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · have h := gap_lower (n := 13118) (a := (653808211417 / 781250000000 : ℝ)) (b := (156961217851 / 100000000000000 : ℝ)) (q := (137670117131 / 6250000000000 : ℝ))
      (E := (cell13118 ⟨11, by decide⟩).energy) (xi := (323185856040807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13118 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13118]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13118])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13118) (a := (653808211417 / 781250000000 : ℝ)) (b := (156961217851 / 100000000000000 : ℝ)) (q := (137670117131 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13118])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13118])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13118]

theorem cert13118_12 : CellCertificate 13118 (87537020129141 / 1000000000000000 : ℝ) (1601174618428737 / 1000000000000000000 : ℝ) (323185856040807 / 10000000000000000 : ℝ)
    (cell13118 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · have h := gap_lower (n := 13118) (a := (83652833324901 / 100000000000000 : ℝ)) (b := (156961217851 / 100000000000000 : ℝ)) (q := (2202725859803 / 100000000000000 : ℝ))
      (E := (cell13118 ⟨12, by decide⟩).energy) (xi := (323185856040807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13118 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13118]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13118])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13118) (a := (83652833324901 / 100000000000000 : ℝ)) (b := (156961217851 / 100000000000000 : ℝ)) (q := (2202725859803 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13118])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13118])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13118]

theorem cert13118_13 : CellCertificate 13118 (87537020129141 / 1000000000000000 : ℝ) (1601174618428737 / 1000000000000000000 : ℝ) (323185856040807 / 10000000000000000 : ℝ)
    (cell13118 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · have h := gap_lower (n := 13118) (a := (41809120006497 / 50000000000000 : ℝ)) (b := (156961217851 / 100000000000000 : ℝ)) (q := (110136493389 / 5000000000000 : ℝ))
      (E := (cell13118 ⟨13, by decide⟩).energy) (xi := (323185856040807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13118 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13118]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13118])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13118) (a := (41809120006497 / 50000000000000 : ℝ)) (b := (156961217851 / 100000000000000 : ℝ)) (q := (110136493389 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13118])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13118])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13118]

theorem cert13118_14 : CellCertificate 13118 (87537020129141 / 1000000000000000 : ℝ) (1601174618428737 / 1000000000000000000 : ℝ) (323185856040807 / 10000000000000000 : ℝ)
    (cell13118 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · have h := gap_lower (n := 13118) (a := (83583671091451 / 100000000000000 : ℝ)) (b := (156961217851 / 100000000000000 : ℝ)) (q := (220273390357 / 10000000000000 : ℝ))
      (E := (cell13118 ⟨14, by decide⟩).energy) (xi := (323185856040807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13118 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13118]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13118])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13118) (a := (83583671091451 / 100000000000000 : ℝ)) (b := (156961217851 / 100000000000000 : ℝ)) (q := (220273390357 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13118])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13118])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13118]

theorem cert13118_15 : CellCertificate 13118 (87537020129141 / 1000000000000000 : ℝ) (1601174618428737 / 1000000000000000000 : ℝ) (323185856040807 / 10000000000000000 : ℝ)
    (cell13118 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · have h := gap_lower (n := 13118) (a := (20887281631561 / 25000000000000 : ℝ)) (b := (156961217851 / 100000000000000 : ℝ)) (q := (2202737914273 / 100000000000000 : ℝ))
      (E := (cell13118 ⟨15, by decide⟩).energy) (xi := (323185856040807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13118 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13118]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13118])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13118) (a := (20887281631561 / 25000000000000 : ℝ)) (b := (156961217851 / 100000000000000 : ℝ)) (q := (2202737914273 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13118])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13118])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13118]

theorem cert13118_16 : CellCertificate 13118 (87537020129141 / 1000000000000000 : ℝ) (1601174618428737 / 1000000000000000000 : ℝ) (323185856040807 / 10000000000000000 : ℝ)
    (cell13118 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · have h := gap_lower (n := 13118) (a := (20878651570881 / 25000000000000 : ℝ)) (b := (156961217851 / 100000000000000 : ℝ)) (q := (275342738109 / 12500000000000 : ℝ))
      (E := (cell13118 ⟨16, by decide⟩).energy) (xi := (323185856040807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13118 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13118]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13118])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13118) (a := (20878651570881 / 25000000000000 : ℝ)) (b := (156961217851 / 100000000000000 : ℝ)) (q := (275342738109 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13118])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13118])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13118]

theorem cert13118_17 : CellCertificate 13118 (87537020129141 / 1000000000000000 : ℝ) (1601174618428737 / 1000000000000000000 : ℝ) (323185856040807 / 10000000000000000 : ℝ)
    (cell13118 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · have h := gap_lower (n := 13118) (a := (41740055164807 / 50000000000000 : ℝ)) (b := (156961217851 / 100000000000000 : ℝ)) (q := (2202745938361 / 100000000000000 : ℝ))
      (E := (cell13118 ⟨17, by decide⟩).energy) (xi := (323185856040807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13118 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13118]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13118])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13118) (a := (41740055164807 / 50000000000000 : ℝ)) (b := (156961217851 / 100000000000000 : ℝ)) (q := (2202745938361 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13118])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13118])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13118]

theorem cert13118_18 : CellCertificate 13118 (87537020129141 / 1000000000000000 : ℝ) (1601174618428737 / 1000000000000000000 : ℝ) (323185856040807 / 10000000000000000 : ℝ)
    (cell13118 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · have h := gap_lower (n := 13118) (a := (83445638631013 / 100000000000000 : ℝ)) (b := (156961217851 / 100000000000000 : ℝ)) (q := (27534374513 / 1250000000000 : ℝ))
      (E := (cell13118 ⟨18, by decide⟩).energy) (xi := (323185856040807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13118 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13118]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13118])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13118) (a := (83445638631013 / 100000000000000 : ℝ)) (b := (156961217851 / 100000000000000 : ℝ)) (q := (27534374513 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13118])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13118])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13118]

theorem cert13118_19 : CellCertificate 13118 (87537020129141 / 1000000000000000 : ℝ) (1601174618428737 / 1000000000000000000 : ℝ) (323185856040807 / 10000000000000000 : ℝ)
    (cell13118 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · have h := gap_lower (n := 13118) (a := (83411191154391 / 100000000000000 : ℝ)) (b := (156961217851 / 100000000000000 : ℝ)) (q := (2202753918877 / 100000000000000 : ℝ))
      (E := (cell13118 ⟨19, by decide⟩).energy) (xi := (323185856040807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13118 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13118]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13118])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13118) (a := (83411191154391 / 100000000000000 : ℝ)) (b := (156961217851 / 100000000000000 : ℝ)) (q := (2202753918877 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13118])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13118])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13118]

theorem cert13119_0 : CellCertificate 13119 (35013757929461 / 400000000000000 : ℝ) (100065783095637 / 62500000000000000 : ℝ) (323160656467843 / 10000000000000000 : ℝ)
    (cell13119 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · have h := gap_lower (n := 13119) (a := (42034926984659 / 50000000000000 : ℝ)) (b := (156949116321 / 100000000000000 : ℝ)) (q := (2202566089427 / 100000000000000 : ℝ))
      (E := (cell13119 ⟨0, by decide⟩).energy) (xi := (323160656467843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13119 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13119]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13119])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13119) (a := (42034926984659 / 50000000000000 : ℝ)) (b := (156949116321 / 100000000000000 : ℝ)) (q := (2202566089427 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13119])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13119])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13119]

theorem cert13119_1 : CellCertificate 13119 (35013757929461 / 400000000000000 : ℝ) (100065783095637 / 62500000000000000 : ℝ) (323160656467843 / 10000000000000000 : ℝ)
    (cell13119 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · have h := gap_lower (n := 13119) (a := (21008741314881 / 25000000000000 : ℝ)) (b := (156949116321 / 100000000000000 : ℝ)) (q := (220257008931 / 10000000000000 : ℝ))
      (E := (cell13119 ⟨1, by decide⟩).energy) (xi := (323160656467843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13119 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13119]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13119])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13119) (a := (21008741314881 / 25000000000000 : ℝ)) (b := (156949116321 / 100000000000000 : ℝ)) (q := (220257008931 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13119])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13119])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13119]

theorem cert13119_2 : CellCertificate 13119 (35013757929461 / 400000000000000 : ℝ) (100065783095637 / 62500000000000000 : ℝ) (323160656467843 / 10000000000000000 : ℝ)
    (cell13119 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · have h := gap_lower (n := 13119) (a := (84000101362577 / 100000000000000 : ℝ)) (b := (156949116321 / 100000000000000 : ℝ)) (q := (1101287045923 / 50000000000000 : ℝ))
      (E := (cell13119 ⟨2, by decide⟩).energy) (xi := (323160656467843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13119 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13119]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13119])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13119) (a := (84000101362577 / 100000000000000 : ℝ)) (b := (156949116321 / 100000000000000 : ℝ)) (q := (1101287045923 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13119])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13119])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13119]

theorem cert13119_3 : CellCertificate 13119 (35013757929461 / 400000000000000 : ℝ) (100065783095637 / 62500000000000000 : ℝ) (323160656467843 / 10000000000000000 : ℝ)
    (cell13119 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · have h := gap_lower (n := 13119) (a := (41982631121123 / 50000000000000 : ℝ)) (b := (156949116321 / 100000000000000 : ℝ)) (q := (220257810541 / 10000000000000 : ℝ))
      (E := (cell13119 ⟨3, by decide⟩).energy) (xi := (323160656467843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13119 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13119]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13119])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13119) (a := (41982631121123 / 50000000000000 : ℝ)) (b := (156949116321 / 100000000000000 : ℝ)) (q := (220257810541 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13119])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13119])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13119]

theorem cert13119_4 : CellCertificate 13119 (35013757929461 / 400000000000000 : ℝ) (100065783095637 / 62500000000000000 : ℝ) (323160656467843 / 10000000000000000 : ℝ)
    (cell13119 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · have h := gap_lower (n := 13119) (a := (83930447862487 / 100000000000000 : ℝ)) (b := (156949116321 / 100000000000000 : ℝ)) (q := (55064553453 / 2500000000000 : ℝ))
      (E := (cell13119 ⟨4, by decide⟩).energy) (xi := (323160656467843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13119 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13119]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13119])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13119) (a := (83930447862487 / 100000000000000 : ℝ)) (b := (156949116321 / 100000000000000 : ℝ)) (q := (55064553453 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13119])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13119])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13119]

theorem cert13119_5 : CellCertificate 13119 (35013757929461 / 400000000000000 : ℝ) (100065783095637 / 62500000000000000 : ℝ) (323160656467843 / 10000000000000000 : ℝ)
    (cell13119 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · have h := gap_lower (n := 13119) (a := (10486957273431 / 12500000000000 : ℝ)) (b := (156949116321 / 100000000000000 : ℝ)) (q := (68830816871 / 3125000000000 : ℝ))
      (E := (cell13119 ⟨5, by decide⟩).energy) (xi := (323160656467843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13119 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13119]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13119])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13119) (a := (10486957273431 / 12500000000000 : ℝ)) (b := (156949116321 / 100000000000000 : ℝ)) (q := (68830816871 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13119])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13119])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13119]

theorem cert13119_6 : CellCertificate 13119 (35013757929461 / 400000000000000 : ℝ) (100065783095637 / 62500000000000000 : ℝ) (323160656467843 / 10000000000000000 : ℝ)
    (cell13119 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · have h := gap_lower (n := 13119) (a := (10482611647683 / 12500000000000 : ℝ)) (b := (156949116321 / 100000000000000 : ℝ)) (q := (1101295088097 / 50000000000000 : ℝ))
      (E := (cell13119 ⟨6, by decide⟩).energy) (xi := (323160656467843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13119 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13119]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13119])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13119) (a := (10482611647683 / 12500000000000 : ℝ)) (b := (156949116321 / 100000000000000 : ℝ)) (q := (1101295088097 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13119])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13119])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13119]

theorem cert13119_7 : CellCertificate 13119 (35013757929461 / 400000000000000 : ℝ) (100065783095637 / 62500000000000000 : ℝ) (323160656467843 / 10000000000000000 : ℝ)
    (cell13119 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · have h := gap_lower (n := 13119) (a := (83826152809057 / 100000000000000 : ℝ)) (b := (156949116321 / 100000000000000 : ℝ)) (q := (550648534603 / 25000000000000 : ℝ))
      (E := (cell13119 ⟨7, by decide⟩).energy) (xi := (323160656467843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13119 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13119]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13119])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13119) (a := (83826152809057 / 100000000000000 : ℝ)) (b := (156949116321 / 100000000000000 : ℝ)) (q := (550648534603 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13119])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13119])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13119]

theorem cert13119_8 : CellCertificate 13119 (35013757929461 / 400000000000000 : ℝ) (100065783095637 / 62500000000000000 : ℝ) (323160656467843 / 10000000000000000 : ℝ)
    (cell13119 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · have h := gap_lower (n := 13119) (a := (41895718517467 / 50000000000000 : ℝ)) (b := (156949116321 / 100000000000000 : ℝ)) (q := (550649537391 / 25000000000000 : ℝ))
      (E := (cell13119 ⟨8, by decide⟩).energy) (xi := (323160656467843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13119 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13119]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13119])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13119) (a := (41895718517467 / 50000000000000 : ℝ)) (b := (156949116321 / 100000000000000 : ℝ)) (q := (550649537391 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13119])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13119])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13119]

theorem cert13119_9 : CellCertificate 13119 (35013757929461 / 400000000000000 : ℝ) (100065783095637 / 62500000000000000 : ℝ) (323160656467843 / 10000000000000000 : ℝ)
    (cell13119 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · have h := gap_lower (n := 13119) (a := (83756745823987 / 100000000000000 : ℝ)) (b := (156949116321 / 100000000000000 : ℝ)) (q := (55065053961 / 2500000000000 : ℝ))
      (E := (cell13119 ⟨9, by decide⟩).energy) (xi := (323160656467843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13119 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13119]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13119])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13119) (a := (83756745823987 / 100000000000000 : ℝ)) (b := (156949116321 / 100000000000000 : ℝ)) (q := (55065053961 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13119])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13119])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13119]

theorem cert13119_10 : CellCertificate 13119 (35013757929461 / 400000000000000 : ℝ) (100065783095637 / 62500000000000000 : ℝ) (323160656467843 / 10000000000000000 : ℝ)
    (cell13119 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · have h := gap_lower (n := 13119) (a := (83722079141291 / 100000000000000 : ℝ)) (b := (156949116321 / 100000000000000 : ℝ)) (q := (2202606171573 / 100000000000000 : ℝ))
      (E := (cell13119 ⟨10, by decide⟩).energy) (xi := (323160656467843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13119 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13119]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13119])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13119) (a := (83722079141291 / 100000000000000 : ℝ)) (b := (156949116321 / 100000000000000 : ℝ)) (q := (2202606171573 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13119])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13119])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13119]

theorem cert13119_11 : CellCertificate 13119 (35013757929461 / 400000000000000 : ℝ) (100065783095637 / 62500000000000000 : ℝ) (323160656467843 / 10000000000000000 : ℝ)
    (cell13119 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · have h := gap_lower (n := 13119) (a := (83687436952103 / 100000000000000 : ℝ)) (b := (156949116321 / 100000000000000 : ℝ)) (q := (440522039049 / 20000000000000 : ℝ))
      (E := (cell13119 ⟨11, by decide⟩).energy) (xi := (323160656467843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13119 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13119]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13119])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13119) (a := (83687436952103 / 100000000000000 : ℝ)) (b := (156949116321 / 100000000000000 : ℝ)) (q := (440522039049 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13119])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13119])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13119]

theorem cert13119_12 : CellCertificate 13119 (35013757929461 / 400000000000000 : ℝ) (100065783095637 / 62500000000000000 : ℝ) (323160656467843 / 10000000000000000 : ℝ)
    (cell13119 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · have h := gap_lower (n := 13119) (a := (83652819221861 / 100000000000000 : ℝ)) (b := (156949116321 / 100000000000000 : ℝ)) (q := (2202614235491 / 100000000000000 : ℝ))
      (E := (cell13119 ⟨12, by decide⟩).energy) (xi := (323160656467843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13119 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13119]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13119])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13119) (a := (83652819221861 / 100000000000000 : ℝ)) (b := (156949116321 / 100000000000000 : ℝ)) (q := (2202614235491 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13119])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13119])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13119]

theorem cert13119_13 : CellCertificate 13119 (35013757929461 / 400000000000000 : ℝ) (100065783095637 / 62500000000000000 : ℝ) (323160656467843 / 10000000000000000 : ℝ)
    (cell13119 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · have h := gap_lower (n := 13119) (a := (83618225916181 / 100000000000000 : ℝ)) (b := (156949116321 / 100000000000000 : ℝ)) (q := (2202618239947 / 100000000000000 : ℝ))
      (E := (cell13119 ⟨13, by decide⟩).energy) (xi := (323160656467843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13119 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13119]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13119])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13119) (a := (83618225916181 / 100000000000000 : ℝ)) (b := (156949116321 / 100000000000000 : ℝ)) (q := (2202618239947 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13119])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13119])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13119]

theorem cert13119_14 : CellCertificate 13119 (35013757929461 / 400000000000000 : ℝ) (100065783095637 / 62500000000000000 : ℝ) (323160656467843 / 10000000000000000 : ℝ)
    (cell13119 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · have h := gap_lower (n := 13119) (a := (4179182850043 / 5000000000000 : ℝ)) (b := (156949116321 / 100000000000000 : ℝ)) (q := (550655553521 / 25000000000000 : ℝ))
      (E := (cell13119 ⟨14, by decide⟩).energy) (xi := (323160656467843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13119 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13119]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13119])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13119) (a := (4179182850043 / 5000000000000 : ℝ)) (b := (156949116321 / 100000000000000 : ℝ)) (q := (550655553521 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13119])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13119])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13119]

theorem cert13119_15 : CellCertificate 13119 (35013757929461 / 400000000000000 : ℝ) (100065783095637 / 62500000000000000 : ℝ) (323160656467843 / 10000000000000000 : ℝ)
    (cell13119 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · have h := gap_lower (n := 13119) (a := (8354911244187 / 10000000000000 : ℝ)) (b := (156949116321 / 100000000000000 : ℝ)) (q := (440525255907 / 20000000000000 : ℝ))
      (E := (cell13119 ⟨15, by decide⟩).energy) (xi := (323160656467843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13119 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13119]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13119])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13119) (a := (8354911244187 / 10000000000000 : ℝ)) (b := (156949116321 / 100000000000000 : ℝ)) (q := (440525255907 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13119])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13119])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13119]

theorem cert13119_16 : CellCertificate 13119 (35013757929461 / 400000000000000 : ℝ) (100065783095637 / 62500000000000000 : ℝ) (323160656467843 / 10000000000000000 : ℝ)
    (cell13119 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · have h := gap_lower (n := 13119) (a := (83514592205361 / 100000000000000 : ℝ)) (b := (156949116321 / 100000000000000 : ℝ)) (q := (2202630266753 / 100000000000000 : ℝ))
      (E := (cell13119 ⟨16, by decide⟩).energy) (xi := (323160656467843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13119 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13119]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13119])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13119) (a := (83514592205361 / 100000000000000 : ℝ)) (b := (156949116321 / 100000000000000 : ℝ)) (q := (2202630266753 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13119])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13119])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13119]

theorem cert13119_17 : CellCertificate 13119 (35013757929461 / 400000000000000 : ℝ) (100065783095637 / 62500000000000000 : ℝ) (323160656467843 / 10000000000000000 : ℝ)
    (cell13119 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · have h := gap_lower (n := 13119) (a := (10435012032207 / 12500000000000 : ℝ)) (b := (156949116321 / 100000000000000 : ℝ)) (q := (2202634296907 / 100000000000000 : ℝ))
      (E := (cell13119 ⟨17, by decide⟩).energy) (xi := (323160656467843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13119 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13119]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13119])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13119) (a := (10435012032207 / 12500000000000 : ℝ)) (b := (156949116321 / 100000000000000 : ℝ)) (q := (2202634296907 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13119])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13119])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13119]

theorem cert13119_18 : CellCertificate 13119 (35013757929461 / 400000000000000 : ℝ) (100065783095637 / 62500000000000000 : ℝ) (323160656467843 / 10000000000000000 : ℝ)
    (cell13119 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · have h := gap_lower (n := 13119) (a := (16689124913051 / 20000000000000 : ℝ)) (b := (156949116321 / 100000000000000 : ℝ)) (q := (2202638316297 / 100000000000000 : ℝ))
      (E := (cell13119 ⟨18, by decide⟩).energy) (xi := (323160656467843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13119 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13119]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13119])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13119) (a := (16689124913051 / 20000000000000 : ℝ)) (b := (156949116321 / 100000000000000 : ℝ)) (q := (2202638316297 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13119])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13119])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13119]

theorem cert13119_19 : CellCertificate 13119 (35013757929461 / 400000000000000 : ℝ) (100065783095637 / 62500000000000000 : ℝ) (323160656467843 / 10000000000000000 : ℝ)
    (cell13119 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · have h := gap_lower (n := 13119) (a := (83411177094827 / 100000000000000 : ℝ)) (b := (156949116321 / 100000000000000 : ℝ)) (q := (550660582297 / 25000000000000 : ℝ))
      (E := (cell13119 ⟨19, by decide⟩).energy) (xi := (323160656467843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13119 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13119]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13119])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13119) (a := (83411177094827 / 100000000000000 : ℝ)) (b := (156949116321 / 100000000000000 : ℝ)) (q := (550660582297 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13119])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13119])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13119]

theorem cert13120_0 : CellCertificate 13120 (875317699011949 / 10000000000000000 : ℝ) (1600930459248681 / 1000000000000000000 : ℝ) (323135460851973 / 10000000000000000 : ℝ)
    (cell13120 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · have h := gap_lower (n := 13120) (a := (84069839793283 / 100000000000000 : ℝ)) (b := (19617127083 / 12500000000000 : ℝ)) (q := (2202454448927 / 100000000000000 : ℝ))
      (E := (cell13120 ⟨0, by decide⟩).energy) (xi := (323135460851973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13120 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13120]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13120])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13120) (a := (84069839793283 / 100000000000000 : ℝ)) (b := (19617127083 / 12500000000000 : ℝ)) (q := (2202454448927 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13120])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13120])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13120]

theorem cert13120_1 : CellCertificate 13120 (875317699011949 / 10000000000000000 : ℝ) (1600930459248681 / 1000000000000000000 : ℝ) (323135460851973 / 10000000000000000 : ℝ)
    (cell13120 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · have h := gap_lower (n := 13120) (a := (42017475544891 / 50000000000000 : ℝ)) (b := (19617127083 / 12500000000000 : ℝ)) (q := (1101229222351 / 50000000000000 : ℝ))
      (E := (cell13120 ⟨1, by decide⟩).energy) (xi := (323135460851973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13120 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13120]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13120])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13120) (a := (42017475544891 / 50000000000000 : ℝ)) (b := (19617127083 / 12500000000000 : ℝ)) (q := (1101229222351 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13120])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13120])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13120]

theorem cert13120_2 : CellCertificate 13120 (875317699011949 / 10000000000000000 : ℝ) (1600930459248681 / 1000000000000000000 : ℝ) (323135460851973 / 10000000000000000 : ℝ)
    (cell13120 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · have h := gap_lower (n := 13120) (a := (84000087199123 / 100000000000000 : ℝ)) (b := (19617127083 / 12500000000000 : ℝ)) (q := (88098500043 / 4000000000000 : ℝ))
      (E := (cell13120 ⟨2, by decide⟩).energy) (xi := (323135460851973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13120 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13120]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13120])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13120) (a := (84000087199123 / 100000000000000 : ℝ)) (b := (19617127083 / 12500000000000 : ℝ)) (q := (88098500043 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13120])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13120])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13120]

theorem cert13120_3 : CellCertificate 13120 (875317699011949 / 10000000000000000 : ℝ) (1600930459248681 / 1000000000000000000 : ℝ) (323135460851973 / 10000000000000000 : ℝ)
    (cell13120 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · have h := gap_lower (n := 13120) (a := (83965248085073 / 100000000000000 : ℝ)) (b := (19617127083 / 12500000000000 : ℝ)) (q := (44049330213 / 2000000000000 : ℝ))
      (E := (cell13120 ⟨3, by decide⟩).energy) (xi := (323135460851973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13120 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13120]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13120])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13120) (a := (83965248085073 / 100000000000000 : ℝ)) (b := (19617127083 / 12500000000000 : ℝ)) (q := (44049330213 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13120])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13120])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13120]

theorem cert13120_4 : CellCertificate 13120 (875317699011949 / 10000000000000000 : ℝ) (1600930459248681 / 1000000000000000000 : ℝ) (323135460851973 / 10000000000000000 : ℝ)
    (cell13120 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · have h := gap_lower (n := 13120) (a := (83930433711591 / 100000000000000 : ℝ)) (b := (19617127083 / 12500000000000 : ℝ)) (q := (34413601273 / 1562500000000 : ℝ))
      (E := (cell13120 ⟨4, by decide⟩).energy) (xi := (323135460851973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13120 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13120]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13120])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13120) (a := (83930433711591 / 100000000000000 : ℝ)) (b := (19617127083 / 12500000000000 : ℝ)) (q := (34413601273 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13120])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13120])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13120]

theorem cert13120_5 : CellCertificate 13120 (875317699011949 / 10000000000000000 : ℝ) (1600930459248681 / 1000000000000000000 : ℝ) (323135460851973 / 10000000000000000 : ℝ)
    (cell13120 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · have h := gap_lower (n := 13120) (a := (41947822021411 / 50000000000000 : ℝ)) (b := (19617127083 / 12500000000000 : ℝ)) (q := (2202474537273 / 100000000000000 : ℝ))
      (E := (cell13120 ⟨5, by decide⟩).energy) (xi := (323135460851973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13120 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13120]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13120])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13120) (a := (41947822021411 / 50000000000000 : ℝ)) (b := (19617127083 / 12500000000000 : ℝ)) (q := (2202474537273 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13120])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13120])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13120]

theorem cert13120_6 : CellCertificate 13120 (875317699011949 / 10000000000000000 : ℝ) (1600930459248681 / 1000000000000000000 : ℝ) (323135460851973 / 10000000000000000 : ℝ)
    (cell13120 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · have h := gap_lower (n := 13120) (a := (83860879043103 / 100000000000000 : ℝ)) (b := (19617127083 / 12500000000000 : ℝ)) (q := (1101239255877 / 50000000000000 : ℝ))
      (E := (cell13120 ⟨6, by decide⟩).energy) (xi := (323135460851973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13120 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13120]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13120])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13120) (a := (83860879043103 / 100000000000000 : ℝ)) (b := (19617127083 / 12500000000000 : ℝ)) (q := (1101239255877 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13120])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13120])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13120]

theorem cert13120_7 : CellCertificate 13120 (875317699011949 / 10000000000000000 : ℝ) (1600930459248681 / 1000000000000000000 : ℝ) (323135460851973 / 10000000000000000 : ℝ)
    (cell13120 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · have h := gap_lower (n := 13120) (a := (20956534669239 / 25000000000000 : ℝ)) (b := (19617127083 / 12500000000000 : ℝ)) (q := (13765515801 / 625000000000 : ℝ))
      (E := (cell13120 ⟨7, by decide⟩).energy) (xi := (323135460851973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13120 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13120]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13120])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13120) (a := (20956534669239 / 25000000000000 : ℝ)) (b := (19617127083 / 12500000000000 : ℝ)) (q := (13765515801 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13120])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13120])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13120]

theorem cert13120_8 : CellCertificate 13120 (875317699011949 / 10000000000000000 : ℝ) (1600930459248681 / 1000000000000000000 : ℝ) (323135460851973 / 10000000000000000 : ℝ)
    (cell13120 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · have h := gap_lower (n := 13120) (a := (83791422909087 / 100000000000000 : ℝ)) (b := (19617127083 / 12500000000000 : ℝ)) (q := (2202486535557 / 100000000000000 : ℝ))
      (E := (cell13120 ⟨8, by decide⟩).energy) (xi := (323135460851973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13120 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13120]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13120])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13120) (a := (83791422909087 / 100000000000000 : ℝ)) (b := (19617127083 / 12500000000000 : ℝ)) (q := (2202486535557 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13120])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13120])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13120]

theorem cert13120_9 : CellCertificate 13120 (875317699011949 / 10000000000000000 : ℝ) (1600930459248681 / 1000000000000000000 : ℝ) (323135460851973 / 10000000000000000 : ℝ)
    (cell13120 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · have h := gap_lower (n := 13120) (a := (20939182926097 / 25000000000000 : ℝ)) (b := (19617127083 / 12500000000000 : ℝ)) (q := (1101245270363 / 50000000000000 : ℝ))
      (E := (cell13120 ⟨9, by decide⟩).energy) (xi := (323135460851973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13120 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13120]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13120])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13120) (a := (20939182926097 / 25000000000000 : ℝ)) (b := (19617127083 / 12500000000000 : ℝ)) (q := (1101245270363 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13120])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13120])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13120]

theorem cert13120_10 : CellCertificate 13120 (875317699011949 / 10000000000000000 : ℝ) (1600930459248681 / 1000000000000000000 : ℝ) (323135460851973 / 10000000000000000 : ℝ)
    (cell13120 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · have h := gap_lower (n := 13120) (a := (16744413005587 / 20000000000000 : ℝ)) (b := (19617127083 / 12500000000000 : ℝ)) (q := (2202494550197 / 100000000000000 : ℝ))
      (E := (cell13120 ⟨10, by decide⟩).energy) (xi := (323135460851973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13120 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13120]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13120])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13120) (a := (16744413005587 / 20000000000000 : ℝ)) (b := (19617127083 / 12500000000000 : ℝ)) (q := (2202494550197 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13120])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13120])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13120]

theorem cert13120_11 : CellCertificate 13120 (875317699011949 / 10000000000000000 : ℝ) (1600930459248681 / 1000000000000000000 : ℝ) (323135460851973 / 10000000000000000 : ℝ)
    (cell13120 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · have h := gap_lower (n := 13120) (a := (10460927855623 / 12500000000000 : ℝ)) (b := (19617127083 / 12500000000000 : ℝ)) (q := (440499714051 / 20000000000000 : ℝ))
      (E := (cell13120 ⟨11, by decide⟩).energy) (xi := (323135460851973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13120 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13120]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13120])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13120) (a := (10460927855623 / 12500000000000 : ℝ)) (b := (19617127083 / 12500000000000 : ℝ)) (q := (440499714051 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13120])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13120])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13120]

theorem cert13120_12 : CellCertificate 13120 (875317699011949 / 10000000000000000 : ℝ) (1600930459248681 / 1000000000000000000 : ℝ) (323135460851973 / 10000000000000000 : ℝ)
    (cell13120 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · have h := gap_lower (n := 13120) (a := (41826402560487 / 50000000000000 : ℝ)) (b := (19617127083 / 12500000000000 : ℝ)) (q := (2202502606933 / 100000000000000 : ℝ))
      (E := (cell13120 ⟨12, by decide⟩).energy) (xi := (323135460851973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13120 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13120]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13120])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13120) (a := (41826402560487 / 50000000000000 : ℝ)) (b := (19617127083 / 12500000000000 : ℝ)) (q := (2202502606933 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13120])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13120])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13120]

theorem cert13120_13 : CellCertificate 13120 (875317699011949 / 10000000000000000 : ℝ) (1600930459248681 / 1000000000000000000 : ℝ) (323135460851973 / 10000000000000000 : ℝ)
    (cell13120 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · have h := gap_lower (n := 13120) (a := (1045227647769 / 1250000000000 : ℝ)) (b := (19617127083 / 12500000000000 : ℝ)) (q := (2202506607867 / 100000000000000 : ℝ))
      (E := (cell13120 ⟨13, by decide⟩).energy) (xi := (323135460851973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13120 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13120]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13120])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13120) (a := (1045227647769 / 1250000000000 : ℝ)) (b := (19617127083 / 12500000000000 : ℝ)) (q := (2202506607867 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13120])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13120])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13120]

theorem cert13120_14 : CellCertificate 13120 (875317699011949 / 10000000000000000 : ℝ) (1600930459248681 / 1000000000000000000 : ℝ) (323135460851973 / 10000000000000000 : ℝ)
    (cell13120 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · have h := gap_lower (n := 13120) (a := (4179182145621 / 5000000000000 : ℝ)) (b := (19617127083 / 12500000000000 : ℝ)) (q := (550627659177 / 25000000000000 : ℝ))
      (E := (cell13120 ⟨14, by decide⟩).energy) (xi := (323135460851973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13120 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13120]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13120])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13120) (a := (4179182145621 / 5000000000000 : ℝ)) (b := (19617127083 / 12500000000000 : ℝ)) (q := (550627659177 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13120])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13120])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13120]

theorem cert13120_15 : CellCertificate 13120 (875317699011949 / 10000000000000000 : ℝ) (1600930459248681 / 1000000000000000000 : ℝ) (323135460851973 / 10000000000000000 : ℝ)
    (cell13120 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · have h := gap_lower (n := 13120) (a := (16709819671929 / 20000000000000 : ℝ)) (b := (19617127083 / 12500000000000 : ℝ)) (q := (1101257320277 / 50000000000000 : ℝ))
      (E := (cell13120 ⟨15, by decide⟩).energy) (xi := (323135460851973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13120 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13120]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13120])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13120) (a := (16709819671929 / 20000000000000 : ℝ)) (b := (19617127083 / 12500000000000 : ℝ)) (q := (1101257320277 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13120])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13120])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13120]

theorem cert13120_16 : CellCertificate 13120 (875317699011949 / 10000000000000000 : ℝ) (1600930459248681 / 1000000000000000000 : ℝ) (323135460851973 / 10000000000000000 : ℝ)
    (cell13120 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · have h := gap_lower (n := 13120) (a := (41757289064673 / 50000000000000 : ℝ)) (b := (19617127083 / 12500000000000 : ℝ)) (q := (2202518624391 / 100000000000000 : ℝ))
      (E := (cell13120 ⟨16, by decide⟩).energy) (xi := (323135460851973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13120 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13120]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13120])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13120) (a := (41757289064673 / 50000000000000 : ℝ)) (b := (19617127083 / 12500000000000 : ℝ)) (q := (2202518624391 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13120])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13120])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13120]

theorem cert13120_17 : CellCertificate 13120 (875317699011949 / 10000000000000000 : ℝ) (1600930459248681 / 1000000000000000000 : ℝ) (323135460851973 / 10000000000000000 : ℝ)
    (cell13120 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · have h := gap_lower (n := 13120) (a := (41740041093923 / 50000000000000 : ℝ)) (b := (19617127083 / 12500000000000 : ℝ)) (q := (220252265121 / 10000000000000 : ℝ))
      (E := (cell13120 ⟨17, by decide⟩).energy) (xi := (323135460851973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13120 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13120]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13120])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13120) (a := (41740041093923 / 50000000000000 : ℝ)) (b := (19617127083 / 12500000000000 : ℝ)) (q := (220252265121 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13120])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13120])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13120]

theorem cert13120_18 : CellCertificate 13120 (875317699011949 / 10000000000000000 : ℝ) (1600930459248681 / 1000000000000000000 : ℝ) (323135460851973 / 10000000000000000 : ℝ)
    (cell13120 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · have h := gap_lower (n := 13120) (a := (83445610501643 / 100000000000000 : ℝ)) (b := (19617127083 / 12500000000000 : ℝ)) (q := (1101263333657 / 50000000000000 : ℝ))
      (E := (cell13120 ⟨18, by decide⟩).energy) (xi := (323135460851973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13120 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13120]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13120])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13120) (a := (83445610501643 / 100000000000000 : ℝ)) (b := (19617127083 / 12500000000000 : ℝ)) (q := (1101263333657 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13120])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13120])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13120]

theorem cert13120_19 : CellCertificate 13120 (875317699011949 / 10000000000000000 : ℝ) (1600930459248681 / 1000000000000000000 : ℝ) (323135460851973 / 10000000000000000 : ℝ)
    (cell13120 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · have h := gap_lower (n := 13120) (a := (8341116303741 / 10000000000000 : ℝ)) (b := (19617127083 / 12500000000000 : ℝ)) (q := (2202530676963 / 100000000000000 : ℝ))
      (E := (cell13120 ⟨19, by decide⟩).energy) (xi := (323135460851973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13120 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13120]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13120])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13120) (a := (8341116303741 / 10000000000000 : ℝ)) (b := (19617127083 / 12500000000000 : ℝ)) (q := (2202530676963 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13120])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13120])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13120]

theorem cert13121_0 : CellCertificate 13121 (175058290723361 / 2000000000000000 : ℝ) (800404203789973 / 500000000000000000 : ℝ) (323110269192213 / 10000000000000000 : ℝ)
    (cell13121 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · have h := gap_lower (n := 13121) (a := (84069825619411 / 100000000000000 : ℝ)) (b := (78462459439 / 50000000000000 : ℝ)) (q := (2202342862023 / 100000000000000 : ℝ))
      (E := (cell13121 ⟨0, by decide⟩).energy) (xi := (323110269192213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13121 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13121]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13121])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13121) (a := (84069825619411 / 100000000000000 : ℝ)) (b := (78462459439 / 50000000000000 : ℝ)) (q := (2202342862023 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13121])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13121])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13121]

theorem cert13121_1 : CellCertificate 13121 (175058290723361 / 2000000000000000 : ℝ) (800404203789973 / 500000000000000000 : ℝ) (323110269192213 / 10000000000000000 : ℝ)
    (cell13121 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · have h := gap_lower (n := 13121) (a := (84034936922203 / 100000000000000 : ℝ)) (b := (78462459439 / 50000000000000 : ℝ)) (q := (440469370743 / 20000000000000 : ℝ))
      (E := (cell13121 ⟨1, by decide⟩).energy) (xi := (323110269192213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13121 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13121]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13121])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13121) (a := (84034936922203 / 100000000000000 : ℝ)) (b := (78462459439 / 50000000000000 : ℝ)) (q := (440469370743 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13121])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13121])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13121]

theorem cert13121_2 : CellCertificate 13121 (175058290723361 / 2000000000000000 : ℝ) (800404203789973 / 500000000000000000 : ℝ) (323110269192213 / 10000000000000000 : ℝ)
    (cell13121 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · have h := gap_lower (n := 13121) (a := (8400007303783 / 10000000000000 : ℝ)) (b := (78462459439 / 50000000000000 : ℝ)) (q := (550587726513 / 25000000000000 : ℝ))
      (E := (cell13121 ⟨2, by decide⟩).energy) (xi := (323110269192213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13121 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13121]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13121])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13121) (a := (8400007303783 / 10000000000000 : ℝ)) (b := (78462459439 / 50000000000000 : ℝ)) (q := (550587726513 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13121])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13121])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13121]

theorem cert13121_3 : CellCertificate 13121 (175058290723361 / 2000000000000000 : ℝ) (800404203789973 / 500000000000000000 : ℝ) (323110269192213 / 10000000000000000 : ℝ)
    (cell13121 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · have h := gap_lower (n := 13121) (a := (41982616965031 / 50000000000000 : ℝ)) (b := (78462459439 / 50000000000000 : ℝ)) (q := (550588727909 / 25000000000000 : ℝ))
      (E := (cell13121 ⟨3, by decide⟩).energy) (xi := (323110269192213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13121 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13121]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13121])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13121) (a := (41982616965031 / 50000000000000 : ℝ)) (b := (78462459439 / 50000000000000 : ℝ)) (q := (550588727909 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13121])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13121])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13121]

theorem cert13121_4 : CellCertificate 13121 (175058290723361 / 2000000000000000 : ℝ) (800404203789973 / 500000000000000000 : ℝ) (323110269192213 / 10000000000000000 : ℝ)
    (cell13121 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · have h := gap_lower (n := 13121) (a := (41965209781427 / 50000000000000 : ℝ)) (b := (78462459439 / 50000000000000 : ℝ)) (q := (1101179439259 / 50000000000000 : ℝ))
      (E := (cell13121 ⟨4, by decide⟩).energy) (xi := (323110269192213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13121 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13121]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13121])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13121) (a := (41965209781427 / 50000000000000 : ℝ)) (b := (78462459439 / 50000000000000 : ℝ)) (q := (1101179439259 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13121])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13121])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13121]

theorem cert13121_5 : CellCertificate 13121 (175058290723361 / 2000000000000000 : ℝ) (800404203789973 / 500000000000000000 : ℝ) (323110269192213 / 10000000000000000 : ℝ)
    (cell13121 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · have h := gap_lower (n := 13121) (a := (20973907475089 / 25000000000000 : ℝ)) (b := (78462459439 / 50000000000000 : ℝ)) (q := (1101181465211 / 50000000000000 : ℝ))
      (E := (cell13121 ⟨5, by decide⟩).energy) (xi := (323110269192213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13121 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13121]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13121])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13121) (a := (20973907475089 / 25000000000000 : ℝ)) (b := (78462459439 / 50000000000000 : ℝ)) (q := (1101181465211 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13121])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13121])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13121]

theorem cert13121_6 : CellCertificate 13121 (175058290723361 / 2000000000000000 : ℝ) (800404203789973 / 500000000000000000 : ℝ) (323110269192213 / 10000000000000000 : ℝ)
    (cell13121 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · have h := gap_lower (n := 13121) (a := (83860864906901 / 100000000000000 : ℝ)) (b := (78462459439 / 50000000000000 : ℝ)) (q := (34411982829 / 1562500000000 : ℝ))
      (E := (cell13121 ⟨6, by decide⟩).energy) (xi := (323110269192213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13121 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13121]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13121])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13121) (a := (83860864906901 / 100000000000000 : ℝ)) (b := (78462459439 / 50000000000000 : ℝ)) (q := (34411982829 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13121])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13121])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13121]

theorem cert13121_7 : CellCertificate 13121 (175058290723361 / 2000000000000000 : ℝ) (800404203789973 / 500000000000000000 : ℝ) (323110269192213 / 10000000000000000 : ℝ)
    (cell13121 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · have h := gap_lower (n := 13121) (a := (83826124547011 / 100000000000000 : ℝ)) (b := (78462459439 / 50000000000000 : ℝ)) (q := (1101185456831 / 50000000000000 : ℝ))
      (E := (cell13121 ⟨7, by decide⟩).energy) (xi := (323110269192213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13121 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13121]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13121])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13121) (a := (83826124547011 / 100000000000000 : ℝ)) (b := (78462459439 / 50000000000000 : ℝ)) (q := (1101185456831 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13121])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13121])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13121]

theorem cert13121_8 : CellCertificate 13121 (175058290723361 / 2000000000000000 : ℝ) (800404203789973 / 500000000000000000 : ℝ) (323110269192213 / 10000000000000000 : ℝ)
    (cell13121 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · have h := gap_lower (n := 13121) (a := (16758281757079 / 20000000000000 : ℝ)) (b := (78462459439 / 50000000000000 : ℝ)) (q := (1101187487671 / 50000000000000 : ℝ))
      (E := (cell13121 ⟨8, by decide⟩).energy) (xi := (323110269192213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13121 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13121]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13121])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13121) (a := (16758281757079 / 20000000000000 : ℝ)) (b := (78462459439 / 50000000000000 : ℝ)) (q := (1101187487671 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13121])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13121])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13121]

theorem cert13121_9 : CellCertificate 13121 (175058290723361 / 2000000000000000 : ℝ) (800404203789973 / 500000000000000000 : ℝ) (323110269192213 / 10000000000000000 : ℝ)
    (cell13121 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · have h := gap_lower (n := 13121) (a := (163587339037 / 195312500000 : ℝ)) (b := (78462459439 / 50000000000000 : ℝ)) (q := (1101189488413 / 50000000000000 : ℝ))
      (E := (cell13121 ⟨9, by decide⟩).energy) (xi := (323110269192213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13121 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13121]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13121])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13121) (a := (163587339037 / 195312500000 : ℝ)) (b := (78462459439 / 50000000000000 : ℝ)) (q := (1101189488413 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13121])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13121])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13121]

theorem cert13121_10 : CellCertificate 13121 (175058290723361 / 2000000000000000 : ℝ) (800404203789973 / 500000000000000000 : ℝ) (323110269192213 / 10000000000000000 : ℝ)
    (cell13121 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · have h := gap_lower (n := 13121) (a := (83722050916733 / 100000000000000 : ℝ)) (b := (78462459439 / 50000000000000 : ℝ)) (q := (110119149133 / 5000000000000 : ℝ))
      (E := (cell13121 ⟨10, by decide⟩).energy) (xi := (323110269192213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13121 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13121]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13121])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13121) (a := (83722050916733 / 100000000000000 : ℝ)) (b := (78462459439 / 50000000000000 : ℝ)) (q := (110119149133 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13121])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13121])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13121]

theorem cert13121_11 : CellCertificate 13121 (175058290723361 / 2000000000000000 : ℝ) (800404203789973 / 500000000000000000 : ℝ) (323110269192213 / 10000000000000000 : ℝ)
    (cell13121 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · have h := gap_lower (n := 13121) (a := (41843704370009 / 50000000000000 : ℝ)) (b := (78462459439 / 50000000000000 : ℝ)) (q := (2202386999127 / 100000000000000 : ℝ))
      (E := (cell13121 ⟨11, by decide⟩).energy) (xi := (323110269192213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13121 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13121]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13121])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13121) (a := (41843704370009 / 50000000000000 : ℝ)) (b := (78462459439 / 50000000000000 : ℝ)) (q := (2202386999127 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13121])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13121])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13121]

theorem cert13121_12 : CellCertificate 13121 (175058290723361 / 2000000000000000 : ℝ) (800404203789973 / 500000000000000000 : ℝ) (323110269192213 / 10000000000000000 : ℝ)
    (cell13121 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · have h := gap_lower (n := 13121) (a := (83652791022239 / 100000000000000 : ℝ)) (b := (78462459439 / 50000000000000 : ℝ)) (q := (220239097413 / 10000000000000 : ℝ))
      (E := (cell13121 ⟨12, by decide⟩).energy) (xi := (323110269192213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13121 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13121]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13121])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13121) (a := (83652791022239 / 100000000000000 : ℝ)) (b := (78462459439 / 50000000000000 : ℝ)) (q := (220239097413 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13121])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13121])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13121]

theorem cert13121_13 : CellCertificate 13121 (175058290723361 / 2000000000000000 : ℝ) (800404203789973 / 500000000000000000 : ℝ) (323110269192213 / 10000000000000000 : ℝ)
    (cell13121 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · have h := gap_lower (n := 13121) (a := (8361819772901 / 10000000000000 : ℝ)) (b := (78462459439 / 50000000000000 : ℝ)) (q := (22023950297 / 1000000000000 : ℝ))
      (E := (cell13121 ⟨13, by decide⟩).energy) (xi := (323110269192213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13121 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13121]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13121])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13121) (a := (8361819772901 / 10000000000000 : ℝ)) (b := (78462459439 / 50000000000000 : ℝ)) (q := (22023950297 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13121])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13121])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13121]

theorem cert13121_14 : CellCertificate 13121 (175058290723361 / 2000000000000000 : ℝ) (800404203789973 / 500000000000000000 : ℝ) (323110269192213 / 10000000000000000 : ℝ)
    (cell13121 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · have h := gap_lower (n := 13121) (a := (8358362882613 / 10000000000000 : ℝ)) (b := (78462459439 / 50000000000000 : ℝ)) (q := (137649937307 / 6250000000000 : ℝ))
      (E := (cell13121 ⟨14, by decide⟩).energy) (xi := (323110269192213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13121 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13121]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13121])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13121) (a := (8358362882613 / 10000000000000 : ℝ)) (b := (78462459439 / 50000000000000 : ℝ)) (q := (137649937307 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13121])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13121])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13121]

theorem cert13121_15 : CellCertificate 13121 (175058290723361 / 2000000000000000 : ℝ) (800404203789973 / 500000000000000000 : ℝ) (323110269192213 / 10000000000000000 : ℝ)
    (cell13121 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · have h := gap_lower (n := 13121) (a := (83549084279569 / 100000000000000 : ℝ)) (b := (78462459439 / 50000000000000 : ℝ)) (q := (1101201527767 / 50000000000000 : ℝ))
      (E := (cell13121 ⟨15, by decide⟩).energy) (xi := (323110269192213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13121 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13121]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13121])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13121) (a := (83549084279569 / 100000000000000 : ℝ)) (b := (78462459439 / 50000000000000 : ℝ)) (q := (1101201527767 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13121])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13121])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13121]

theorem cert13121_16 : CellCertificate 13121 (175058290723361 / 2000000000000000 : ℝ) (800404203789973 / 500000000000000000 : ℝ) (323110269192213 / 10000000000000000 : ℝ)
    (cell13121 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · have h := gap_lower (n := 13121) (a := (83514564055479 / 100000000000000 : ℝ)) (b := (78462459439 / 50000000000000 : ℝ)) (q := (2202407036013 / 100000000000000 : ℝ))
      (E := (cell13121 ⟨16, by decide⟩).energy) (xi := (323110269192213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13121 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13121]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13121])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13121) (a := (83514564055479 / 100000000000000 : ℝ)) (b := (78462459439 / 50000000000000 : ℝ)) (q := (2202407036013 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13121])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13121])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13121]

theorem cert13121_17 : CellCertificate 13121 (175058290723361 / 2000000000000000 : ℝ) (800404203789973 / 500000000000000000 : ℝ) (323110269192213 / 10000000000000000 : ℝ)
    (cell13121 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · have h := gap_lower (n := 13121) (a := (83480068120183 / 100000000000000 : ℝ)) (b := (78462459439 / 50000000000000 : ℝ)) (q := (2202411059523 / 100000000000000 : ℝ))
      (E := (cell13121 ⟨17, by decide⟩).energy) (xi := (323110269192213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13121 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13121]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13121])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13121) (a := (83480068120183 / 100000000000000 : ℝ)) (b := (78462459439 / 50000000000000 : ℝ)) (q := (2202411059523 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13121])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13121])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13121]

theorem cert13121_18 : CellCertificate 13121 (175058290723361 / 2000000000000000 : ℝ) (800404203789973 / 500000000000000000 : ℝ) (323110269192213 / 10000000000000000 : ℝ)
    (cell13121 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · have h := gap_lower (n := 13121) (a := (41722798220089 / 50000000000000 : ℝ)) (b := (78462459439 / 50000000000000 : ℝ)) (q := (2202415072363 / 100000000000000 : ℝ))
      (E := (cell13121 ⟨18, by decide⟩).energy) (xi := (323110269192213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13121 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13121]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13121])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13121) (a := (41722798220089 / 50000000000000 : ℝ)) (b := (78462459439 / 50000000000000 : ℝ)) (q := (2202415072363 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13121])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13121])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13121]

theorem cert13121_19 : CellCertificate 13121 (175058290723361 / 2000000000000000 : ℝ) (800404203789973 / 500000000000000000 : ℝ) (323110269192213 / 10000000000000000 : ℝ)
    (cell13121 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · have h := gap_lower (n := 13121) (a := (41705574491069 / 50000000000000 : ℝ)) (b := (78462459439 / 50000000000000 : ℝ)) (q := (550604769699 / 25000000000000 : ℝ))
      (E := (cell13121 ⟨19, by decide⟩).energy) (xi := (323110269192213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13121 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13121]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13121])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13121) (a := (41705574491069 / 50000000000000 : ℝ)) (b := (78462459439 / 50000000000000 : ℝ)) (q := (550604769699 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13121])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13121])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13121]

theorem cert13122_0 : CellCertificate 13122 (875265212050213 / 10000000000000000 : ℝ) (160068637451973 / 100000000000000000 : ℝ) (323085081487579 / 10000000000000000 : ℝ)
    (cell13122 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · have h := gap_lower (n := 13122) (a := (42034905723851 / 50000000000000 : ℝ)) (b := (31382564593 / 20000000000000 : ℝ)) (q := (137639454429 / 6250000000000 : ℝ))
      (E := (cell13122 ⟨0, by decide⟩).energy) (xi := (323085081487579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13122 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13122]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13122])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13122) (a := (42034905723851 / 50000000000000 : ℝ)) (b := (31382564593 / 20000000000000 : ℝ)) (q := (137639454429 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13122])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13122])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13122]

theorem cert13122_1 : CellCertificate 13122 (875265212050213 / 10000000000000000 : ℝ) (160068637451973 / 100000000000000000 : ℝ) (323085081487579 / 10000000000000000 : ℝ)
    (cell13122 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · have h := gap_lower (n := 13122) (a := (16806984551357 / 20000000000000 : ℝ)) (b := (31382564593 / 20000000000000 : ℝ)) (q := (2202235316347 / 100000000000000 : ℝ))
      (E := (cell13122 ⟨1, by decide⟩).energy) (xi := (323085081487579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13122 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13122]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13122])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13122) (a := (16806984551357 / 20000000000000 : ℝ)) (b := (31382564593 / 20000000000000 : ℝ)) (q := (2202235316347 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13122])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13122])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13122]

theorem cert13122_2 : CellCertificate 13122 (875265212050213 / 10000000000000000 : ℝ) (160068637451973 / 100000000000000000 : ℝ) (323085081487579 / 10000000000000000 : ℝ)
    (cell13122 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · have h := gap_lower (n := 13122) (a := (84000058878699 / 100000000000000 : ℝ)) (b := (31382564593 / 20000000000000 : ℝ)) (q := (1101119653387 / 50000000000000 : ℝ))
      (E := (cell13122 ⟨2, by decide⟩).energy) (xi := (323085081487579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13122 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13122]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13122])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13122) (a := (84000058878699 / 100000000000000 : ℝ)) (b := (31382564593 / 20000000000000 : ℝ)) (q := (1101119653387 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13122])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13122])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13122]

theorem cert13122_3 : CellCertificate 13122 (875265212050213 / 10000000000000000 : ℝ) (160068637451973 / 100000000000000000 : ℝ) (323085081487579 / 10000000000000000 : ℝ)
    (cell13122 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · have h := gap_lower (n := 13122) (a := (8396521977721 / 10000000000000 : ℝ)) (b := (31382564593 / 20000000000000 : ℝ)) (q := (2202243308371 / 100000000000000 : ℝ))
      (E := (cell13122 ⟨3, by decide⟩).energy) (xi := (323085081487579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13122 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13122]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13122])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13122) (a := (8396521977721 / 10000000000000 : ℝ)) (b := (31382564593 / 20000000000000 : ℝ)) (q := (2202243308371 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13122])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13122])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13122]

theorem cert13122_4 : CellCertificate 13122 (875265212050213 / 10000000000000000 : ℝ) (160068637451973 / 100000000000000000 : ℝ) (323085081487579 / 10000000000000000 : ℝ)
    (cell13122 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · have h := gap_lower (n := 13122) (a := (83930405416277 / 100000000000000 : ℝ)) (b := (31382564593 / 20000000000000 : ℝ)) (q := (440449465851 / 20000000000000 : ℝ))
      (E := (cell13122 ⟨4, by decide⟩).energy) (xi := (323085081487579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13122 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13122]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13122])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13122) (a := (83930405416277 / 100000000000000 : ℝ)) (b := (31382564593 / 20000000000000 : ℝ)) (q := (440449465851 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13122])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13122])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13122]

theorem cert13122_5 : CellCertificate 13122 (875265212050213 / 10000000000000000 : ℝ) (160068637451973 / 100000000000000000 : ℝ) (323085081487579 / 10000000000000000 : ℝ)
    (cell13122 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · have h := gap_lower (n := 13122) (a := (83895615760047 / 100000000000000 : ℝ)) (b := (31382564593 / 20000000000000 : ℝ)) (q := (2202251319321 / 100000000000000 : ℝ))
      (E := (cell13122 ⟨5, by decide⟩).energy) (xi := (323085081487579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13122 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13122]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13122])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13122) (a := (83895615760047 / 100000000000000 : ℝ)) (b := (31382564593 / 20000000000000 : ℝ)) (q := (2202251319321 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13122])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13122])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13122]

theorem cert13122_6 : CellCertificate 13122 (875265212050213 / 10000000000000000 : ℝ) (160068637451973 / 100000000000000000 : ℝ) (323085081487579 / 10000000000000000 : ℝ)
    (cell13122 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · have h := gap_lower (n := 13122) (a := (16772170154571 / 20000000000000 : ℝ)) (b := (31382564593 / 20000000000000 : ℝ)) (q := (2202255344099 / 100000000000000 : ℝ))
      (E := (cell13122 ⟨6, by decide⟩).energy) (xi := (323085081487579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13122 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13122]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13122])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13122) (a := (16772170154571 / 20000000000000 : ℝ)) (b := (31382564593 / 20000000000000 : ℝ)) (q := (2202255344099 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13122])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13122])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13122]

theorem cert13122_7 : CellCertificate 13122 (875265212050213 / 10000000000000000 : ℝ) (160068637451973 / 100000000000000000 : ℝ) (323085081487579 / 10000000000000000 : ℝ)
    (cell13122 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · have h := gap_lower (n := 13122) (a := (10478263802403 / 12500000000000 : ℝ)) (b := (31382564593 / 20000000000000 : ℝ)) (q := (1101129676463 / 50000000000000 : ℝ))
      (E := (cell13122 ⟨7, by decide⟩).energy) (xi := (323085081487579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13122 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13122]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13122])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13122) (a := (10478263802403 / 12500000000000 : ℝ)) (b := (31382564593 / 20000000000000 : ℝ)) (q := (1101129676463 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13122])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13122])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13122]

theorem cert13122_8 : CellCertificate 13122 (875265212050213 / 10000000000000000 : ℝ) (160068637451973 / 100000000000000000 : ℝ) (323085081487579 / 10000000000000000 : ℝ)
    (cell13122 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · have h := gap_lower (n := 13122) (a := (83791394663859 / 100000000000000 : ℝ)) (b := (31382564593 / 20000000000000 : ℝ)) (q := (55056583821 / 2500000000000 : ℝ))
      (E := (cell13122 ⟨8, by decide⟩).energy) (xi := (323085081487579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13122 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13122]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13122])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13122) (a := (83791394663859 / 100000000000000 : ℝ)) (b := (31382564593 / 20000000000000 : ℝ)) (q := (55056583821 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13122])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13122])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13122]

theorem cert13122_9 : CellCertificate 13122 (875265212050213 / 10000000000000000 : ℝ) (160068637451973 / 100000000000000000 : ℝ) (323085081487579 / 10000000000000000 : ℝ)
    (cell13122 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · have h := gap_lower (n := 13122) (a := (16751340694331 / 20000000000000 : ℝ)) (b := (31382564593 / 20000000000000 : ℝ)) (q := (1101133704339 / 50000000000000 : ℝ))
      (E := (cell13122 ⟨9, by decide⟩).energy) (xi := (323085081487579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13122 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13122]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13122])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13122) (a := (16751340694331 / 20000000000000 : ℝ)) (b := (31382564593 / 20000000000000 : ℝ)) (q := (1101133704339 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13122])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13122])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13122]

theorem cert13122_10 : CellCertificate 13122 (875265212050213 / 10000000000000000 : ℝ) (160068637451973 / 100000000000000000 : ℝ) (323085081487579 / 10000000000000000 : ℝ)
    (cell13122 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · have h := gap_lower (n := 13122) (a := (20930509201921 / 25000000000000 : ℝ)) (b := (31382564593 / 20000000000000 : ℝ)) (q := (550567852719 / 25000000000000 : ℝ))
      (E := (cell13122 ⟨10, by decide⟩).energy) (xi := (323085081487579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13122 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13122]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13122])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13122) (a := (20930509201921 / 25000000000000 : ℝ)) (b := (31382564593 / 20000000000000 : ℝ)) (q := (550567852719 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13122])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13122])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13122]

theorem cert13122_11 : CellCertificate 13122 (875265212050213 / 10000000000000000 : ℝ) (160068637451973 / 100000000000000000 : ℝ) (323085081487579 / 10000000000000000 : ℝ)
    (cell13122 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · have h := gap_lower (n := 13122) (a := (16737478927441 / 20000000000000 : ℝ)) (b := (31382564593 / 20000000000000 : ℝ)) (q := (2202275423753 / 100000000000000 : ℝ))
      (E := (cell13122 ⟨11, by decide⟩).energy) (xi := (323085081487579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13122 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13122]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13122])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13122) (a := (16737478927441 / 20000000000000 : ℝ)) (b := (31382564593 / 20000000000000 : ℝ)) (q := (2202275423753 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13122])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13122])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13122]

theorem cert13122_12 : CellCertificate 13122 (875265212050213 / 10000000000000000 : ℝ) (160068637451973 / 100000000000000000 : ℝ) (323085081487579 / 10000000000000000 : ℝ)
    (cell13122 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · have h := gap_lower (n := 13122) (a := (16730555385131 / 20000000000000 : ℝ)) (b := (31382564593 / 20000000000000 : ℝ)) (q := (1101139697607 / 50000000000000 : ℝ))
      (E := (cell13122 ⟨12, by decide⟩).energy) (xi := (323085081487579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13122 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13122]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13122])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13122) (a := (16730555385131 / 20000000000000 : ℝ)) (b := (31382564593 / 20000000000000 : ℝ)) (q := (1101139697607 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13122])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13122])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13122]

theorem cert13122_13 : CellCertificate 13122 (875265212050213 / 10000000000000000 : ℝ) (160068637451973 / 100000000000000000 : ℝ) (323085081487579 / 10000000000000000 : ℝ)
    (cell13122 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · have h := gap_lower (n := 13122) (a := (83618183638651 / 100000000000000 : ℝ)) (b := (31382564593 / 20000000000000 : ℝ)) (q := (2202283447287 / 100000000000000 : ℝ))
      (E := (cell13122 ⟨13, by decide⟩).energy) (xi := (323085081487579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13122 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13122]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13122])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13122) (a := (83618183638651 / 100000000000000 : ℝ)) (b := (31382564593 / 20000000000000 : ℝ)) (q := (2202283447287 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13122])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13122])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13122]

theorem cert13122_14 : CellCertificate 13122 (875265212050213 / 10000000000000000 : ℝ) (160068637451973 / 100000000000000000 : ℝ) (323085081487579 / 10000000000000000 : ℝ)
    (cell13122 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · have h := gap_lower (n := 13122) (a := (83583614741989 / 100000000000000 : ℝ)) (b := (31382564593 / 20000000000000 : ℝ)) (q := (220228746923 / 10000000000000 : ℝ))
      (E := (cell13122 ⟨14, by decide⟩).energy) (xi := (323085081487579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13122 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13122]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13122])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13122) (a := (83583614741989 / 100000000000000 : ℝ)) (b := (31382564593 / 20000000000000 : ℝ)) (q := (220228746923 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13122])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13122])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13122]

theorem cert13122_15 : CellCertificate 13122 (875265212050213 / 10000000000000000 : ℝ) (160068637451973 / 100000000000000000 : ℝ) (323085081487579 / 10000000000000000 : ℝ)
    (cell13122 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · have h := gap_lower (n := 13122) (a := (83549070201643 / 100000000000000 : ℝ)) (b := (31382564593 / 20000000000000 : ℝ)) (q := (2202291466269 / 100000000000000 : ℝ))
      (E := (cell13122 ⟨15, by decide⟩).energy) (xi := (323085081487579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13122 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13122]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13122])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13122) (a := (83549070201643 / 100000000000000 : ℝ)) (b := (31382564593 / 20000000000000 : ℝ)) (q := (2202291466269 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13122])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13122])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13122]

theorem cert13122_16 : CellCertificate 13122 (875265212050213 / 10000000000000000 : ℝ) (160068637451973 / 100000000000000000 : ℝ) (323085081487579 / 10000000000000000 : ℝ)
    (cell13122 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · have h := gap_lower (n := 13122) (a := (1043931874797 / 1250000000000 : ℝ)) (b := (31382564593 / 20000000000000 : ℝ)) (q := (1101147721697 / 50000000000000 : ℝ))
      (E := (cell13122 ⟨16, by decide⟩).energy) (xi := (323085081487579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13122 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13122]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13122])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13122) (a := (1043931874797 / 1250000000000 : ℝ)) (b := (31382564593 / 20000000000000 : ℝ)) (q := (1101147721697 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13122])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13122])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13122]

theorem cert13122_17 : CellCertificate 13122 (875265212050213 / 10000000000000000 : ℝ) (160068637451973 / 100000000000000000 : ℝ) (323085081487579 / 10000000000000000 : ℝ)
    (cell13122 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · have h := gap_lower (n := 13122) (a := (41740027027333 / 50000000000000 : ℝ)) (b := (31382564593 / 20000000000000 : ℝ)) (q := (440459892719 / 20000000000000 : ℝ))
      (E := (cell13122 ⟨17, by decide⟩).energy) (xi := (323085081487579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13122 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13122]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13122])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13122) (a := (41740027027333 / 50000000000000 : ℝ)) (b := (31382564593 / 20000000000000 : ℝ)) (q := (440459892719 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13122])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13122])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13122]

theorem cert13122_18 : CellCertificate 13122 (875265212050213 / 10000000000000000 : ℝ) (160068637451973 / 100000000000000000 : ℝ) (323085081487579 / 10000000000000000 : ℝ)
    (cell13122 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · have h := gap_lower (n := 13122) (a := (83445582380859 / 100000000000000 : ℝ)) (b := (31382564593 / 20000000000000 : ℝ)) (q := (2202303473173 / 100000000000000 : ℝ))
      (E := (cell13122 ⟨18, by decide⟩).energy) (xi := (323085081487579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13122 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13122]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13122])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13122) (a := (83445582380859 / 100000000000000 : ℝ)) (b := (31382564593 / 20000000000000 : ℝ)) (q := (2202303473173 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13122])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13122])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13122]

theorem cert13122_19 : CellCertificate 13122 (875265212050213 / 10000000000000000 : ℝ) (160068637451973 / 100000000000000000 : ℝ) (323085081487579 / 10000000000000000 : ℝ)
    (cell13122 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · have h := gap_lower (n := 13122) (a := (83411134929011 / 100000000000000 : ℝ)) (b := (31382564593 / 20000000000000 : ℝ)) (q := (550576883671 / 25000000000000 : ℝ))
      (E := (cell13122 ⟨19, by decide⟩).energy) (xi := (323085081487579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13122 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13122]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13122])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13122) (a := (83411134929011 / 100000000000000 : ℝ)) (b := (31382564593 / 20000000000000 : ℝ)) (q := (550576883671 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13122])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13122])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13122]

theorem cert13123_0 : CellCertificate 13123 (437619487155647 / 5000000000000000 : ℝ) (1600564360063779 / 1000000000000000000 : ℝ) (323059897737089 / 10000000000000000 : ℝ)
    (cell13123 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · have h := gap_lower (n := 13123) (a := (21017449319539 / 25000000000000 : ℝ)) (b := (156900728923 / 100000000000000 : ℝ)) (q := (1101059866651 / 50000000000000 : ℝ))
      (E := (cell13123 ⟨0, by decide⟩).energy) (xi := (323059897737089 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13123 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13123]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13123])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13123) (a := (21017449319539 / 25000000000000 : ℝ)) (b := (156900728923 / 100000000000000 : ℝ)) (q := (1101059866651 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13123])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13123])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13123]

theorem cert13123_1 : CellCertificate 13123 (437619487155647 / 5000000000000000 : ℝ) (1600564360063779 / 1000000000000000000 : ℝ) (323059897737089 / 10000000000000000 : ℝ)
    (cell13123 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · have h := gap_lower (n := 13123) (a := (8403490859353 / 10000000000000 : ℝ)) (b := (156900728923 / 100000000000000 : ℝ)) (q := (550530929213 / 25000000000000 : ℝ))
      (E := (cell13123 ⟨1, by decide⟩).energy) (xi := (323059897737089 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13123 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13123]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13123])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13123) (a := (8403490859353 / 10000000000000 : ℝ)) (b := (156900728923 / 100000000000000 : ℝ)) (q := (550530929213 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13123])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13123])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13123]

theorem cert13123_2 : CellCertificate 13123 (437619487155647 / 5000000000000000 : ℝ) (1600564360063779 / 1000000000000000000 : ℝ) (323059897737089 / 10000000000000000 : ℝ)
    (cell13123 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · have h := gap_lower (n := 13123) (a := (1312500698777 / 1562500000000 : ℝ)) (b := (156900728923 / 100000000000000 : ℝ)) (q := (2202127761143 / 100000000000000 : ℝ))
      (E := (cell13123 ⟨2, by decide⟩).energy) (xi := (323059897737089 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13123 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13123]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13123])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13123) (a := (1312500698777 / 1562500000000 : ℝ)) (b := (156900728923 / 100000000000000 : ℝ)) (q := (2202127761143 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13123])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13123])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13123]

theorem cert13123_3 : CellCertificate 13123 (437619487155647 / 5000000000000000 : ℝ) (1600564360063779 / 1000000000000000000 : ℝ) (323059897737089 / 10000000000000000 : ℝ)
    (cell13123 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · have h := gap_lower (n := 13123) (a := (41982602813259 / 50000000000000 : ℝ)) (b := (156900728923 / 100000000000000 : ℝ)) (q := (88085270351 / 4000000000000 : ℝ))
      (E := (cell13123 ⟨3, by decide⟩).energy) (xi := (323059897737089 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13123 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13123]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13123])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13123) (a := (41982602813259 / 50000000000000 : ℝ)) (b := (156900728923 / 100000000000000 : ℝ)) (q := (88085270351 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13123])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13123])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13123]

theorem cert13123_4 : CellCertificate 13123 (437619487155647 / 5000000000000000 : ℝ) (1600564360063779 / 1000000000000000000 : ℝ) (323059897737089 / 10000000000000000 : ℝ)
    (cell13123 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · have h := gap_lower (n := 13123) (a := (83930391271859 / 100000000000000 : ℝ)) (b := (156900728923 / 100000000000000 : ℝ)) (q := (1101067887871 / 50000000000000 : ℝ))
      (E := (cell13123 ⟨4, by decide⟩).energy) (xi := (323059897737089 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13123 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13123]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13123])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13123) (a := (83930391271859 / 100000000000000 : ℝ)) (b := (156900728923 / 100000000000000 : ℝ)) (q := (1101067887871 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13123])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13123])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13123]

theorem cert13123_5 : CellCertificate 13123 (437619487155647 / 5000000000000000 : ℝ) (1600564360063779 / 1000000000000000000 : ℝ) (323059897737089 / 10000000000000000 : ℝ)
    (cell13123 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · have h := gap_lower (n := 13123) (a := (10486950202737 / 12500000000000 : ℝ)) (b := (156900728923 / 100000000000000 : ℝ)) (q := (2202139761939 / 100000000000000 : ℝ))
      (E := (cell13123 ⟨5, by decide⟩).energy) (xi := (323059897737089 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13123 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13123]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13123])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13123) (a := (10486950202737 / 12500000000000 : ℝ)) (b := (156900728923 / 100000000000000 : ℝ)) (q := (2202139761939 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13123])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13123])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13123]

theorem cert13123_6 : CellCertificate 13123 (437619487155647 / 5000000000000000 : ℝ) (1600564360063779 / 1000000000000000000 : ℝ) (323059897737089 / 10000000000000000 : ℝ)
    (cell13123 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · have h := gap_lower (n := 13123) (a := (83860836640967 / 100000000000000 : ℝ)) (b := (156900728923 / 100000000000000 : ℝ)) (q := (550535945723 / 25000000000000 : ℝ))
      (E := (cell13123 ⟨6, by decide⟩).energy) (xi := (323059897737089 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13123 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13123]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13123])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13123) (a := (83860836640967 / 100000000000000 : ℝ)) (b := (156900728923 / 100000000000000 : ℝ)) (q := (550535945723 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13123])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13123])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13123]

theorem cert13123_7 : CellCertificate 13123 (437619487155647 / 5000000000000000 : ℝ) (1600564360063779 / 1000000000000000000 : ℝ) (323059897737089 / 10000000000000000 : ℝ)
    (cell13123 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · have h := gap_lower (n := 13123) (a := (10478262036699 / 12500000000000 : ℝ)) (b := (156900728923 / 100000000000000 : ℝ)) (q := (440429557589 / 20000000000000 : ℝ))
      (E := (cell13123 ⟨7, by decide⟩).energy) (xi := (323059897737089 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13123 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13123]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13123])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13123) (a := (10478262036699 / 12500000000000 : ℝ)) (b := (156900728923 / 100000000000000 : ℝ)) (q := (440429557589 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13123])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13123])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13123]

theorem cert13123_8 : CellCertificate 13123 (437619487155647 / 5000000000000000 : ℝ) (1600564360063779 / 1000000000000000000 : ℝ) (323059897737089 / 10000000000000000 : ℝ)
    (cell13123 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · have h := gap_lower (n := 13123) (a := (41895690272239 / 50000000000000 : ℝ)) (b := (156900728923 / 100000000000000 : ℝ)) (q := (2202151784129 / 100000000000000 : ℝ))
      (E := (cell13123 ⟨8, by decide⟩).energy) (xi := (323059897737089 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13123 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13123]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13123])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13123) (a := (41895690272239 / 50000000000000 : ℝ)) (b := (156900728923 / 100000000000000 : ℝ)) (q := (2202151784129 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13123])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13123])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13123]

theorem cert13123_9 : CellCertificate 13123 (437619487155647 / 5000000000000000 : ℝ) (1600564360063779 / 1000000000000000000 : ℝ) (323059897737089 / 10000000000000000 : ℝ)
    (cell13123 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · have h := gap_lower (n := 13123) (a := (83756689358519 / 100000000000000 : ℝ)) (b := (156900728923 / 100000000000000 : ℝ)) (q := (440431167257 / 20000000000000 : ℝ))
      (E := (cell13123 ⟨9, by decide⟩).energy) (xi := (323059897737089 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13123 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13123]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13123])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13123) (a := (83756689358519 / 100000000000000 : ℝ)) (b := (156900728923 / 100000000000000 : ℝ)) (q := (440431167257 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13123])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13123])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13123]

theorem cert13123_10 : CellCertificate 13123 (437619487155647 / 5000000000000000 : ℝ) (1600564360063779 / 1000000000000000000 : ℝ) (323059897737089 / 10000000000000000 : ℝ)
    (cell13123 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · have h := gap_lower (n := 13123) (a := (20930505675197 / 25000000000000 : ℝ)) (b := (156900728923 / 100000000000000 : ℝ)) (q := (68817494839 / 3125000000000 : ℝ))
      (E := (cell13123 ⟨10, by decide⟩).energy) (xi := (323059897737089 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13123 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13123]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13123])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13123) (a := (20930505675197 / 25000000000000 : ℝ)) (b := (156900728923 / 100000000000000 : ℝ)) (q := (68817494839 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13123])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13123])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13123]

theorem cert13123_11 : CellCertificate 13123 (437619487155647 / 5000000000000000 : ℝ) (1600564360063779 / 1000000000000000000 : ℝ) (323059897737089 / 10000000000000000 : ℝ)
    (cell13123 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · have h := gap_lower (n := 13123) (a := (2615230641767 / 3125000000000 : ℝ)) (b := (156900728923 / 100000000000000 : ℝ)) (q := (275270480517 / 12500000000000 : ℝ))
      (E := (cell13123 ⟨11, by decide⟩).energy) (xi := (323059897737089 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13123 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13123]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13123])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13123) (a := (2615230641767 / 3125000000000 : ℝ)) (b := (156900728923 / 100000000000000 : ℝ)) (q := (275270480517 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13123])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13123])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13123]

theorem cert13123_12 : CellCertificate 13123 (437619487155647 / 5000000000000000 : ℝ) (1600564360063779 / 1000000000000000000 : ℝ) (323059897737089 / 10000000000000000 : ℝ)
    (cell13123 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · have h := gap_lower (n := 13123) (a := (83652762831223 / 100000000000000 : ℝ)) (b := (156900728923 / 100000000000000 : ℝ)) (q := (1101083935093 / 50000000000000 : ℝ))
      (E := (cell13123 ⟨12, by decide⟩).energy) (xi := (323059897737089 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13123 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13123]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13123])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13123) (a := (83652762831223 / 100000000000000 : ℝ)) (b := (156900728923 / 100000000000000 : ℝ)) (q := (1101083935093 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13123])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13123])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13123]

theorem cert13123_13 : CellCertificate 13123 (437619487155647 / 5000000000000000 : ℝ) (1600564360063779 / 1000000000000000000 : ℝ) (323059897737089 / 10000000000000000 : ℝ)
    (cell13123 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · have h := gap_lower (n := 13123) (a := (41809084775221 / 50000000000000 : ℝ)) (b := (156900728923 / 100000000000000 : ℝ)) (q := (2202171860633 / 100000000000000 : ℝ))
      (E := (cell13123 ⟨13, by decide⟩).energy) (xi := (323059897737089 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13123 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13123]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13123])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13123) (a := (41809084775221 / 50000000000000 : ℝ)) (b := (156900728923 / 100000000000000 : ℝ)) (q := (2202171860633 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13123])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13123])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13123]

theorem cert13123_14 : CellCertificate 13123 (437619487155647 / 5000000000000000 : ℝ) (1600564360063779 / 1000000000000000000 : ℝ) (323059897737089 / 10000000000000000 : ℝ)
    (cell13123 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · have h := gap_lower (n := 13123) (a := (41791800329999 / 50000000000000 : ℝ)) (b := (156900728923 / 100000000000000 : ℝ)) (q := (2202175879127 / 100000000000000 : ℝ))
      (E := (cell13123 ⟨14, by decide⟩).energy) (xi := (323059897737089 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13123 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13123]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13123])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13123) (a := (41791800329999 / 50000000000000 : ℝ)) (b := (156900728923 / 100000000000000 : ℝ)) (q := (2202175879127 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13123])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13123])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13123]

theorem cert13123_15 : CellCertificate 13123 (437619487155647 / 5000000000000000 : ℝ) (1600564360063779 / 1000000000000000000 : ℝ) (323059897737089 / 10000000000000000 : ℝ)
    (cell13123 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · have h := gap_lower (n := 13123) (a := (10443632015733 / 12500000000000 : ℝ)) (b := (156900728923 / 100000000000000 : ℝ)) (q := (1101089936383 / 50000000000000 : ℝ))
      (E := (cell13123 ⟨15, by decide⟩).energy) (xi := (323059897737089 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13123 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13123]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13123])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13123) (a := (10443632015733 / 12500000000000 : ℝ)) (b := (156900728923 / 100000000000000 : ℝ)) (q := (1101089936383 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13123])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13123])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13123]

theorem cert13123_16 : CellCertificate 13123 (437619487155647 / 5000000000000000 : ℝ) (1600564360063779 / 1000000000000000000 : ℝ) (323059897737089 / 10000000000000000 : ℝ)
    (cell13123 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · have h := gap_lower (n := 13123) (a := (83514535914189 / 100000000000000 : ℝ)) (b := (156900728923 / 100000000000000 : ℝ)) (q := (55054597619 / 2500000000000 : ℝ))
      (E := (cell13123 ⟨16, by decide⟩).energy) (xi := (323059897737089 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13123 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13123]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13123])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13123) (a := (83514535914189 / 100000000000000 : ℝ)) (b := (156900728923 / 100000000000000 : ℝ)) (q := (55054597619 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13123])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13123])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13123]

theorem cert13123_17 : CellCertificate 13123 (437619487155647 / 5000000000000000 : ℝ) (1600564360063779 / 1000000000000000000 : ℝ) (323059897737089 / 10000000000000000 : ℝ)
    (cell13123 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · have h := gap_lower (n := 13123) (a := (40761738277 / 48828125000 : ℝ)) (b := (156900728923 / 100000000000000 : ℝ)) (q := (2202187921677 / 100000000000000 : ℝ))
      (E := (cell13123 ⟨17, by decide⟩).energy) (xi := (323059897737089 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13123 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13123]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13123])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13123) (a := (40761738277 / 48828125000 : ℝ)) (b := (156900728923 / 100000000000000 : ℝ)) (q := (2202187921677 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13123])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13123])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13123]

theorem cert13123_18 : CellCertificate 13123 (437619487155647 / 5000000000000000 : ℝ) (1600564360063779 / 1000000000000000000 : ℝ) (323059897737089 / 10000000000000000 : ℝ)
    (cell13123 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · have h := gap_lower (n := 13123) (a := (41722784161843 / 50000000000000 : ℝ)) (b := (156900728923 / 100000000000000 : ℝ)) (q := (137636995501 / 6250000000000 : ℝ))
      (E := (cell13123 ⟨18, by decide⟩).energy) (xi := (323059897737089 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13123 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13123]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13123])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13123) (a := (41722784161843 / 50000000000000 : ℝ)) (b := (156900728923 / 100000000000000 : ℝ)) (q := (137636995501 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13123])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13123])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13123]

theorem cert13123_19 : CellCertificate 13123 (437619487155647 / 5000000000000000 : ℝ) (1600564360063779 / 1000000000000000000 : ℝ) (323059897737089 / 10000000000000000 : ℝ)
    (cell13123 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · have h := gap_lower (n := 13123) (a := (20852780219507 / 25000000000000 : ℝ)) (b := (156900728923 / 100000000000000 : ℝ)) (q := (2202195928041 / 100000000000000 : ℝ))
      (E := (cell13123 ⟨19, by decide⟩).energy) (xi := (323059897737089 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13123 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13123]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13123])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13123) (a := (20852780219507 / 25000000000000 : ℝ)) (b := (156900728923 / 100000000000000 : ℝ)) (q := (2202195928041 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13123])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13123])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13123]

theorem cert13124_0 : CellCertificate 13124 (875212740399169 / 10000000000000000 : ℝ) (800221182103919 / 500000000000000000 : ℝ) (323034717939759 / 10000000000000000 : ℝ)
    (cell13124 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · have h := gap_lower (n := 13124) (a := (21017445777693 / 25000000000000 : ℝ)) (b := (9805539797 / 6250000000000 : ℝ)) (q := (1101004095743 / 50000000000000 : ℝ))
      (E := (cell13124 ⟨0, by decide⟩).energy) (xi := (323034717939759 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13124 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13124]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13124])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13124) (a := (21017445777693 / 25000000000000 : ℝ)) (b := (9805539797 / 6250000000000 : ℝ)) (q := (1101004095743 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13124])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13124])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13124]

theorem cert13124_1 : CellCertificate 13124 (875212740399169 / 10000000000000000 : ℝ) (800221182103919 / 500000000000000000 : ℝ) (323034717939759 / 10000000000000000 : ℝ)
    (cell13124 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · have h := gap_lower (n := 13124) (a := (16806978886487 / 20000000000000 : ℝ)) (b := (9805539797 / 6250000000000 : ℝ)) (q := (110100608549 / 5000000000000 : ℝ))
      (E := (cell13124 ⟨1, by decide⟩).energy) (xi := (323034717939759 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13124 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13124]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13124])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13124) (a := (16806978886487 / 20000000000000 : ℝ)) (b := (9805539797 / 6250000000000 : ℝ)) (q := (110100608549 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13124])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13124])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13124]

theorem cert13124_2 : CellCertificate 13124 (875212740399169 / 10000000000000000 : ℝ) (800221182103919 / 500000000000000000 : ℝ) (323034717939759 / 10000000000000000 : ℝ)
    (cell13124 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · have h := gap_lower (n := 13124) (a := (84000030566917 / 100000000000000 : ℝ)) (b := (9805539797 / 6250000000000 : ℝ)) (q := (110100810563 / 5000000000000 : ℝ))
      (E := (cell13124 ⟨2, by decide⟩).energy) (xi := (323034717939759 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13124 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13124]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13124])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13124) (a := (84000030566917 / 100000000000000 : ℝ)) (b := (9805539797 / 6250000000000 : ℝ)) (q := (110100810563 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13124])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13124])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13124]

theorem cert13124_3 : CellCertificate 13124 (875212740399169 / 10000000000000000 : ℝ) (800221182103919 / 500000000000000000 : ℝ) (323034717939759 / 10000000000000000 : ℝ)
    (cell13124 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · have h := gap_lower (n := 13124) (a := (16793038295597 / 20000000000000 : ℝ)) (b := (9805539797 / 6250000000000 : ℝ)) (q := (220202020493 / 10000000000000 : ℝ))
      (E := (cell13124 ⟨3, by decide⟩).energy) (xi := (323034717939759 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13124 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13124]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13124])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13124) (a := (16793038295597 / 20000000000000 : ℝ)) (b := (9805539797 / 6250000000000 : ℝ)) (q := (220202020493 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13124])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13124])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13124]

theorem cert13124_4 : CellCertificate 13124 (875212740399169 / 10000000000000000 : ℝ) (800221182103919 / 500000000000000000 : ℝ) (323034717939759 / 10000000000000000 : ℝ)
    (cell13124 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · have h := gap_lower (n := 13124) (a := (41965188564799 / 50000000000000 : ℝ)) (b := (9805539797 / 6250000000000 : ℝ)) (q := (2202024217981 / 100000000000000 : ℝ))
      (E := (cell13124 ⟨4, by decide⟩).energy) (xi := (323034717939759 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13124 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13124]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13124])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13124) (a := (41965188564799 / 50000000000000 : ℝ)) (b := (9805539797 / 6250000000000 : ℝ)) (q := (2202024217981 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13124])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13124])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13124]

theorem cert13124_5 : CellCertificate 13124 (875212740399169 / 10000000000000000 : ℝ) (800221182103919 / 500000000000000000 : ℝ) (323034717939759 / 10000000000000000 : ℝ)
    (cell13124 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · have h := gap_lower (n := 13124) (a := (83895587485903 / 100000000000000 : ℝ)) (b := (9805539797 / 6250000000000 : ℝ)) (q := (88081130331 / 4000000000000 : ℝ))
      (E := (cell13124 ⟨5, by decide⟩).energy) (xi := (323034717939759 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13124 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13124]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13124])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13124) (a := (83895587485903 / 100000000000000 : ℝ)) (b := (9805539797 / 6250000000000 : ℝ)) (q := (88081130331 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13124])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13124])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13124]

theorem cert13124_6 : CellCertificate 13124 (875212740399169 / 10000000000000000 : ℝ) (800221182103919 / 500000000000000000 : ℝ) (323034717939759 / 10000000000000000 : ℝ)
    (cell13124 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · have h := gap_lower (n := 13124) (a := (41930411255617 / 50000000000000 : ℝ)) (b := (9805539797 / 6250000000000 : ℝ)) (q := (2202032275431 / 100000000000000 : ℝ))
      (E := (cell13124 ⟨6, by decide⟩).energy) (xi := (323034717939759 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13124 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13124]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13124])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13124) (a := (41930411255617 / 50000000000000 : ℝ)) (b := (9805539797 / 6250000000000 : ℝ)) (q := (2202032275431 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13124])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13124])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13124]

theorem cert13124_7 : CellCertificate 13124 (875212740399169 / 10000000000000000 : ℝ) (800221182103919 / 500000000000000000 : ℝ) (323034717939759 / 10000000000000000 : ℝ)
    (cell13124 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · have h := gap_lower (n := 13124) (a := (16765216434023 / 20000000000000 : ℝ)) (b := (9805539797 / 6250000000000 : ℝ)) (q := (2202036276731 / 100000000000000 : ℝ))
      (E := (cell13124 ⟨7, by decide⟩).energy) (xi := (323034717939759 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13124 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13124]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13124])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13124) (a := (16765216434023 / 20000000000000 : ℝ)) (b := (9805539797 / 6250000000000 : ℝ)) (q := (2202036276731 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13124])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13124])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13124]

theorem cert13124_8 : CellCertificate 13124 (875212740399169 / 10000000000000000 : ℝ) (800221182103919 / 500000000000000000 : ℝ) (323034717939759 / 10000000000000000 : ℝ)
    (cell13124 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · have h := gap_lower (n := 13124) (a := (20947841606813 / 25000000000000 : ℝ)) (b := (9805539797 / 6250000000000 : ℝ)) (q := (220204026921 / 10000000000000 : ℝ))
      (E := (cell13124 ⟨8, by decide⟩).energy) (xi := (323034717939759 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13124 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13124]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13124])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13124) (a := (20947841606813 / 25000000000000 : ℝ)) (b := (9805539797 / 6250000000000 : ℝ)) (q := (220204026921 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13124])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13124])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13124]

theorem cert13124_9 : CellCertificate 13124 (875212740399169 / 10000000000000000 : ℝ) (800221182103919 / 500000000000000000 : ℝ) (323034717939759 / 10000000000000000 : ℝ)
    (cell13124 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · have h := gap_lower (n := 13124) (a := (83756675247537 / 100000000000000 : ℝ)) (b := (9805539797 / 6250000000000 : ℝ)) (q := (2202044259647 / 100000000000000 : ℝ))
      (E := (cell13124 ⟨9, by decide⟩).energy) (xi := (323034717939759 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13124 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13124]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13124])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13124) (a := (83756675247537 / 100000000000000 : ℝ)) (b := (9805539797 / 6250000000000 : ℝ)) (q := (2202044259647 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13124])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13124])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13124]

theorem cert13124_10 : CellCertificate 13124 (875212740399169 / 10000000000000000 : ℝ) (800221182103919 / 500000000000000000 : ℝ) (323034717939759 / 10000000000000000 : ℝ)
    (cell13124 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · have h := gap_lower (n := 13124) (a := (16744401719209 / 20000000000000 : ℝ)) (b := (9805539797 / 6250000000000 : ℝ)) (q := (110102415633 / 5000000000000 : ℝ))
      (E := (cell13124 ⟨10, by decide⟩).energy) (xi := (323034717939759 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13124 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13124]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13124])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13124) (a := (16744401719209 / 20000000000000 : ℝ)) (b := (9805539797 / 6250000000000 : ℝ)) (q := (110102415633 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13124])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13124])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13124]

theorem cert13124_11 : CellCertificate 13124 (875212740399169 / 10000000000000000 : ℝ) (800221182103919 / 500000000000000000 : ℝ) (323034717939759 / 10000000000000000 : ℝ)
    (cell13124 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · have h := gap_lower (n := 13124) (a := (41843683219017 / 50000000000000 : ℝ)) (b := (9805539797 / 6250000000000 : ℝ)) (q := (137628269899 / 6250000000000 : ℝ))
      (E := (cell13124 ⟨11, by decide⟩).energy) (xi := (323034717939759 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13124 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13124]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13124])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13124) (a := (41843683219017 / 50000000000000 : ℝ)) (b := (9805539797 / 6250000000000 : ℝ)) (q := (137628269899 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13124])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13124])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13124]

theorem cert13124_12 : CellCertificate 13124 (875212740399169 / 10000000000000000 : ℝ) (800221182103919 / 500000000000000000 : ℝ) (323034717939759 / 10000000000000000 : ℝ)
    (cell13124 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · have h := gap_lower (n := 13124) (a := (83652748738941 / 100000000000000 : ℝ)) (b := (9805539797 / 6250000000000 : ℝ)) (q := (2202056340917 / 100000000000000 : ℝ))
      (E := (cell13124 ⟨12, by decide⟩).energy) (xi := (323034717939759 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13124 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13124]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13124])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13124) (a := (83652748738941 / 100000000000000 : ℝ)) (b := (9805539797 / 6250000000000 : ℝ)) (q := (2202056340917 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13124])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13124])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13124]

theorem cert13124_13 : CellCertificate 13124 (875212740399169 / 10000000000000000 : ℝ) (800221182103919 / 500000000000000000 : ℝ) (323034717939759 / 10000000000000000 : ℝ)
    (cell13124 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · have h := gap_lower (n := 13124) (a := (83618155464383 / 100000000000000 : ℝ)) (b := (9805539797 / 6250000000000 : ℝ)) (q := (2202060327893 / 100000000000000 : ℝ))
      (E := (cell13124 ⟨13, by decide⟩).energy) (xi := (323034717939759 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13124 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13124]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13124])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13124) (a := (83618155464383 / 100000000000000 : ℝ)) (b := (9805539797 / 6250000000000 : ℝ)) (q := (2202060327893 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13124])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13124])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13124]

theorem cert13124_14 : CellCertificate 13124 (875212740399169 / 10000000000000000 : ℝ) (800221182103919 / 500000000000000000 : ℝ) (323034717939759 / 10000000000000000 : ℝ)
    (cell13124 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · have h := gap_lower (n := 13124) (a := (20895896645039 / 25000000000000 : ℝ)) (b := (9805539797 / 6250000000000 : ℝ)) (q := (2202064342963 / 100000000000000 : ℝ))
      (E := (cell13124 ⟨14, by decide⟩).energy) (xi := (323034717939759 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13124 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13124]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13124])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13124) (a := (20895896645039 / 25000000000000 : ℝ)) (b := (9805539797 / 6250000000000 : ℝ)) (q := (2202064342963 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13124])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13124])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13124]

theorem cert13124_15 : CellCertificate 13124 (875212740399169 / 10000000000000000 : ℝ) (800221182103919 / 500000000000000000 : ℝ) (323034717939759 / 10000000000000000 : ℝ)
    (cell13124 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · have h := gap_lower (n := 13124) (a := (83549042052233 / 100000000000000 : ℝ)) (b := (9805539797 / 6250000000000 : ℝ)) (q := (275258541653 / 12500000000000 : ℝ))
      (E := (cell13124 ⟨15, by decide⟩).energy) (xi := (323034717939759 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13124 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13124]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13124])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13124) (a := (83549042052233 / 100000000000000 : ℝ)) (b := (9805539797 / 6250000000000 : ℝ)) (q := (275258541653 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13124])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13124])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13124]

theorem cert13124_16 : CellCertificate 13124 (875212740399169 / 10000000000000000 : ℝ) (800221182103919 / 500000000000000000 : ℝ) (323034717939759 / 10000000000000000 : ℝ)
    (cell13124 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · have h := gap_lower (n := 13124) (a := (20878630461691 / 25000000000000 : ℝ)) (b := (9805539797 / 6250000000000 : ℝ)) (q := (68814761309 / 3125000000000 : ℝ))
      (E := (cell13124 ⟨16, by decide⟩).energy) (xi := (323034717939759 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13124 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13124]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13124])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13124) (a := (20878630461691 / 25000000000000 : ℝ)) (b := (9805539797 / 6250000000000 : ℝ)) (q := (68814761309 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13124])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13124])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13124]

theorem cert13124_17 : CellCertificate 13124 (875212740399169 / 10000000000000000 : ℝ) (800221182103919 / 500000000000000000 : ℝ) (323034717939759 / 10000000000000000 : ℝ)
    (cell13124 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · have h := gap_lower (n := 13124) (a := (10435003241259 / 12500000000000 : ℝ)) (b := (9805539797 / 6250000000000 : ℝ)) (q := (2202076375521 / 100000000000000 : ℝ))
      (E := (cell13124 ⟨17, by decide⟩).energy) (xi := (323034717939759 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13124 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13124]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13124])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13124) (a := (10435003241259 / 12500000000000 : ℝ)) (b := (9805539797 / 6250000000000 : ℝ)) (q := (2202076375521 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13124])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13124])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13124]

theorem cert13124_18 : CellCertificate 13124 (875212740399169 / 10000000000000000 : ℝ) (800221182103919 / 500000000000000000 : ℝ) (323034717939759 / 10000000000000000 : ℝ)
    (cell13124 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · have h := gap_lower (n := 13124) (a := (83445554268657 / 100000000000000 : ℝ)) (b := (9805539797 / 6250000000000 : ℝ)) (q := (2202080378623 / 100000000000000 : ℝ))
      (E := (cell13124 ⟨18, by decide⟩).energy) (xi := (323034717939759 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13124 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13124]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13124])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13124) (a := (83445554268657 / 100000000000000 : ℝ)) (b := (9805539797 / 6250000000000 : ℝ)) (q := (2202080378623 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13124])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13124])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13124]

theorem cert13124_19 : CellCertificate 13124 (875212740399169 / 10000000000000000 : ℝ) (800221182103919 / 500000000000000000 : ℝ) (323034717939759 / 10000000000000000 : ℝ)
    (cell13124 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · have h := gap_lower (n := 13124) (a := (83411106829189 / 100000000000000 : ℝ)) (b := (9805539797 / 6250000000000 : ℝ)) (q := (2202084433753 / 100000000000000 : ℝ))
      (E := (cell13124 ⟨19, by decide⟩).energy) (xi := (323034717939759 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13124 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13124]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13124])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13124) (a := (83411106829189 / 100000000000000 : ℝ)) (b := (9805539797 / 6250000000000 : ℝ)) (q := (2202084433753 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13124])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13124])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13124]

end BstLean.Part268
