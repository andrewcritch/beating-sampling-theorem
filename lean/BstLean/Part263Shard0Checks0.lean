import BstLean.Part263Shard0Data

/-! Twenty scalar cells per dimension in a 25-dimension shard. -/
namespace BstLean.Part263
open Real

theorem cert12225_0 : CellCertificate 12225 (450227846321489 / 5000000000000000 : ℝ) (1718175626812061 / 1000000000000000000 : ℝ) (347397722670537 / 10000000000000000 : ℝ)
    (cell12225 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · have h := gap_lower (n := 12225) (a := (4204172821037 / 5000000000000 : ℝ)) (b := (168573401311 / 100000000000000 : ℝ)) (q := (2315077302999 / 100000000000000 : ℝ))
      (E := (cell12225 ⟨0, by decide⟩).energy) (xi := (347397722670537 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12225 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12225]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12225])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12225) (a := (4204172821037 / 5000000000000 : ℝ)) (b := (168573401311 / 100000000000000 : ℝ)) (q := (2315077302999 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12225])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12225])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12225]

theorem cert12225_1 : CellCertificate 12225 (450227846321489 / 5000000000000000 : ℝ) (1718175626812061 / 1000000000000000000 : ℝ) (347397722670537 / 10000000000000000 : ℝ)
    (cell12225 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · have h := gap_lower (n := 12225) (a := (16809664970243 / 20000000000000 : ℝ)) (b := (168573401311 / 100000000000000 : ℝ)) (q := (2315081304167 / 100000000000000 : ℝ))
      (E := (cell12225 ⟨1, by decide⟩).energy) (xi := (347397722670537 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12225 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12225]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12225])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12225) (a := (16809664970243 / 20000000000000 : ℝ)) (b := (168573401311 / 100000000000000 : ℝ)) (q := (2315081304167 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12225])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12225])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12225]

theorem cert12225_2 : CellCertificate 12225 (450227846321489 / 5000000000000000 : ℝ) (1718175626812061 / 1000000000000000000 : ℝ) (347397722670537 / 10000000000000000 : ℝ)
    (cell12225 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · have h := gap_lower (n := 12225) (a := (8401321843789 / 10000000000000 : ℝ)) (b := (168573401311 / 100000000000000 : ℝ)) (q := (2315085306739 / 100000000000000 : ℝ))
      (E := (cell12225 ⟨2, by decide⟩).energy) (xi := (347397722670537 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12225 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12225]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12225])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12225) (a := (8401321843789 / 10000000000000 : ℝ)) (b := (168573401311 / 100000000000000 : ℝ)) (q := (2315085306739 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12225])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12225])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12225]

theorem cert12225_3 : CellCertificate 12225 (450227846321489 / 5000000000000000 : ℝ) (1718175626812061 / 1000000000000000000 : ℝ) (347397722670537 / 10000000000000000 : ℝ)
    (cell12225 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · have h := gap_lower (n := 12225) (a := (83978137143771 / 100000000000000 : ℝ)) (b := (168573401311 / 100000000000000 : ℝ)) (q := (1157544631347 / 50000000000000 : ℝ))
      (E := (cell12225 ⟨3, by decide⟩).energy) (xi := (347397722670537 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12225 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12225]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12225])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12225) (a := (83978137143771 / 100000000000000 : ℝ)) (b := (168573401311 / 100000000000000 : ℝ)) (q := (1157544631347 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12225])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12225])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12225]

theorem cert12225_4 : CellCertificate 12225 (450227846321489 / 5000000000000000 : ℝ) (1718175626812061 / 1000000000000000000 : ℝ) (347397722670537 / 10000000000000000 : ℝ)
    (cell12225 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · have h := gap_lower (n := 12225) (a := (83943080932061 / 100000000000000 : ℝ)) (b := (168573401311 / 100000000000000 : ℝ)) (q := (463018647871 / 20000000000000 : ℝ))
      (E := (cell12225 ⟨4, by decide⟩).energy) (xi := (347397722670537 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12225 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12225]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12225])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12225) (a := (83943080932061 / 100000000000000 : ℝ)) (b := (168573401311 / 100000000000000 : ℝ)) (q := (463018647871 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12225])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12225])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12225]

theorem cert12225_5 : CellCertificate 12225 (450227846321489 / 5000000000000000 : ℝ) (1718175626812061 / 1000000000000000000 : ℝ) (347397722670537 / 10000000000000000 : ℝ)
    (cell12225 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · have h := gap_lower (n := 12225) (a := (20977012441539 / 25000000000000 : ℝ)) (b := (168573401311 / 100000000000000 : ℝ)) (q := (2315097246007 / 100000000000000 : ℝ))
      (E := (cell12225 ⟨5, by decide⟩).energy) (xi := (347397722670537 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12225 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12225]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12225])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12225) (a := (20977012441539 / 25000000000000 : ℝ)) (b := (168573401311 / 100000000000000 : ℝ)) (q := (2315097246007 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12225])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12225])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12225]

theorem cert12225_6 : CellCertificate 12225 (450227846321489 / 5000000000000000 : ℝ) (1718175626812061 / 1000000000000000000 : ℝ) (347397722670537 / 10000000000000000 : ℝ)
    (cell12225 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · have h := gap_lower (n := 12225) (a := (5242065225603 / 6250000000000 : ℝ)) (b := (168573401311 / 100000000000000 : ℝ)) (q := (578775308443 / 25000000000000 : ℝ))
      (E := (cell12225 ⟨6, by decide⟩).energy) (xi := (347397722670537 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12225 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12225]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12225])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12225) (a := (5242065225603 / 6250000000000 : ℝ)) (b := (168573401311 / 100000000000000 : ℝ)) (q := (578775308443 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12225])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12225])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12225]

theorem cert12225_7 : CellCertificate 12225 (450227846321489 / 5000000000000000 : ℝ) (1718175626812061 / 1000000000000000000 : ℝ) (347397722670537 / 10000000000000000 : ℝ)
    (cell12225 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · have h := gap_lower (n := 12225) (a := (83838062426317 / 100000000000000 : ℝ)) (b := (168573401311 / 100000000000000 : ℝ)) (q := (2315105211347 / 100000000000000 : ℝ))
      (E := (cell12225 ⟨7, by decide⟩).energy) (xi := (347397722670537 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12225 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12225]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12225])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12225) (a := (83838062426317 / 100000000000000 : ℝ)) (b := (168573401311 / 100000000000000 : ℝ)) (q := (2315105211347 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12225])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12225])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12225]

theorem cert12225_8 : CellCertificate 12225 (450227846321489 / 5000000000000000 : ℝ) (1718175626812061 / 1000000000000000000 : ℝ) (347397722670537 / 10000000000000000 : ℝ)
    (cell12225 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · have h := gap_lower (n := 12225) (a := (83803106180137 / 100000000000000 : ℝ)) (b := (168573401311 / 100000000000000 : ℝ)) (q := (463021849023 / 20000000000000 : ℝ))
      (E := (cell12225 ⟨8, by decide⟩).energy) (xi := (347397722670537 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12225 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12225]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12225])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12225) (a := (83803106180137 / 100000000000000 : ℝ)) (b := (168573401311 / 100000000000000 : ℝ)) (q := (463021849023 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12225])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12225])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12225]

theorem cert12225_9 : CellCertificate 12225 (450227846321489 / 5000000000000000 : ℝ) (1718175626812061 / 1000000000000000000 : ℝ) (347397722670537 / 10000000000000000 : ℝ)
    (cell12225 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · have h := gap_lower (n := 12225) (a := (83768174835271 / 100000000000000 : ℝ)) (b := (168573401311 / 100000000000000 : ℝ)) (q := (578778306847 / 25000000000000 : ℝ))
      (E := (cell12225 ⟨9, by decide⟩).energy) (xi := (347397722670537 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12225 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12225]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12225])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12225) (a := (83768174835271 / 100000000000000 : ℝ)) (b := (168573401311 / 100000000000000 : ℝ)) (q := (578778306847 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12225])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12225])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12225]

theorem cert12225_10 : CellCertificate 12225 (450227846321489 / 5000000000000000 : ℝ) (1718175626812061 / 1000000000000000000 : ℝ) (347397722670537 / 10000000000000000 : ℝ)
    (cell12225 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · have h := gap_lower (n := 12225) (a := (83733268356069 / 100000000000000 : ℝ)) (b := (168573401311 / 100000000000000 : ℝ)) (q := (2315117224017 / 100000000000000 : ℝ))
      (E := (cell12225 ⟨10, by decide⟩).energy) (xi := (347397722670537 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12225 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12225]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12225])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12225) (a := (83733268356069 / 100000000000000 : ℝ)) (b := (168573401311 / 100000000000000 : ℝ)) (q := (2315117224017 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12225])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12225])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12225]

theorem cert12225_11 : CellCertificate 12225 (450227846321489 / 5000000000000000 : ℝ) (1718175626812061 / 1000000000000000000 : ℝ) (347397722670537 / 10000000000000000 : ℝ)
    (cell12225 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · have h := gap_lower (n := 12225) (a := (20924596676767 / 25000000000000 : ℝ)) (b := (168573401311 / 100000000000000 : ℝ)) (q := (115756059233 / 5000000000000 : ℝ))
      (E := (cell12225 ⟨11, by decide⟩).energy) (xi := (347397722670537 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12225 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12225]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12225])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12225) (a := (20924596676767 / 25000000000000 : ℝ)) (b := (168573401311 / 100000000000000 : ℝ)) (q := (115756059233 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12225])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12225])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12225]

theorem cert12225_12 : CellCertificate 12225 (450227846321489 / 5000000000000000 : ℝ) (1718175626812061 / 1000000000000000000 : ℝ) (347397722670537 / 10000000000000000 : ℝ)
    (cell12225 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · have h := gap_lower (n := 12225) (a := (1307242653953 / 1562500000000 : ℝ)) (b := (168573401311 / 100000000000000 : ℝ)) (q := (1157562587353 / 50000000000000 : ℝ))
      (E := (cell12225 ⟨12, by decide⟩).energy) (xi := (347397722670537 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12225 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12225]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12225])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12225) (a := (1307242653953 / 1562500000000 : ℝ)) (b := (168573401311 / 100000000000000 : ℝ)) (q := (1157562587353 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12225])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12225])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12225]

theorem cert12225_13 : CellCertificate 12225 (450227846321489 / 5000000000000000 : ℝ) (1718175626812061 / 1000000000000000000 : ℝ) (347397722670537 / 10000000000000000 : ℝ)
    (cell12225 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · have h := gap_lower (n := 12225) (a := (20907174439687 / 25000000000000 : ℝ)) (b := (168573401311 / 100000000000000 : ℝ)) (q := (2315129201329 / 100000000000000 : ℝ))
      (E := (cell12225 ⟨13, by decide⟩).energy) (xi := (347397722670537 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12225 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12225]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12225])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12225) (a := (20907174439687 / 25000000000000 : ℝ)) (b := (168573401311 / 100000000000000 : ℝ)) (q := (2315129201329 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12225])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12225])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12225]

theorem cert12225_14 : CellCertificate 12225 (450227846321489 / 5000000000000000 : ℝ) (1718175626812061 / 1000000000000000000 : ℝ) (347397722670537 / 10000000000000000 : ℝ)
    (cell12225 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · have h := gap_lower (n := 12225) (a := (83593890389429 / 100000000000000 : ℝ)) (b := (168573401311 / 100000000000000 : ℝ)) (q := (2315133155271 / 100000000000000 : ℝ))
      (E := (cell12225 ⟨14, by decide⟩).energy) (xi := (347397722670537 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12225 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12225]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12225])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12225) (a := (83593890389429 / 100000000000000 : ℝ)) (b := (168573401311 / 100000000000000 : ℝ)) (q := (2315133155271 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12225])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12225])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12225]

theorem cert12225_15 : CellCertificate 12225 (450227846321489 / 5000000000000000 : ℝ) (1718175626812061 / 1000000000000000000 : ℝ) (347397722670537 / 10000000000000000 : ℝ)
    (cell12225 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · have h := gap_lower (n := 12225) (a := (83559107710307 / 100000000000000 : ℝ)) (b := (168573401311 / 100000000000000 : ℝ)) (q := (2315137159287 / 100000000000000 : ℝ))
      (E := (cell12225 ⟨15, by decide⟩).energy) (xi := (347397722670537 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12225 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12225]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12225])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12225) (a := (83559107710307 / 100000000000000 : ℝ)) (b := (168573401311 / 100000000000000 : ℝ)) (q := (2315137159287 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12225])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12225])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12225]

theorem cert12225_16 : CellCertificate 12225 (450227846321489 / 5000000000000000 : ℝ) (1718175626812061 / 1000000000000000000 : ℝ) (347397722670537 / 10000000000000000 : ℝ)
    (cell12225 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · have h := gap_lower (n := 12225) (a := (83524349686837 / 100000000000000 : ℝ)) (b := (168573401311 / 100000000000000 : ℝ)) (q := (463028232333 / 20000000000000 : ℝ))
      (E := (cell12225 ⟨16, by decide⟩).energy) (xi := (347397722670537 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12225 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12225]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12225])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12225) (a := (83524349686837 / 100000000000000 : ℝ)) (b := (168573401311 / 100000000000000 : ℝ)) (q := (463028232333 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12225])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12225])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12225]

theorem cert12225_17 : CellCertificate 12225 (450227846321489 / 5000000000000000 : ℝ) (1718175626812061 / 1000000000000000000 : ℝ) (347397722670537 / 10000000000000000 : ℝ)
    (cell12225 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · have h := gap_lower (n := 12225) (a := (83489616284653 / 100000000000000 : ℝ)) (b := (168573401311 / 100000000000000 : ℝ)) (q := (18087071629 / 781250000000 : ℝ))
      (E := (cell12225 ⟨17, by decide⟩).energy) (xi := (347397722670537 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12225 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12225]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12225])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12225) (a := (83489616284653 / 100000000000000 : ℝ)) (b := (168573401311 / 100000000000000 : ℝ)) (q := (18087071629 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12225])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12225])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12225]

theorem cert12225_18 : CellCertificate 12225 (450227846321489 / 5000000000000000 : ℝ) (1718175626812061 / 1000000000000000000 : ℝ) (347397722670537 / 10000000000000000 : ℝ)
    (cell12225 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · have h := gap_lower (n := 12225) (a := (325995732303 / 390625000000 : ℝ)) (b := (168573401311 / 100000000000000 : ℝ)) (q := (2315149127509 / 100000000000000 : ℝ))
      (E := (cell12225 ⟨18, by decide⟩).energy) (xi := (347397722670537 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12225 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12225]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12225])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12225) (a := (325995732303 / 390625000000 : ℝ)) (b := (168573401311 / 100000000000000 : ℝ)) (q := (2315149127509 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12225])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12225])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12225]

theorem cert12225_19 : CellCertificate 12225 (450227846321489 / 5000000000000000 : ℝ) (1718175626812061 / 1000000000000000000 : ℝ) (347397722670537 / 10000000000000000 : ℝ)
    (cell12225 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · have h := gap_lower (n := 12225) (a := (83420223207573 / 100000000000000 : ℝ)) (b := (168573401311 / 100000000000000 : ℝ)) (q := (1157576551203 / 50000000000000 : ℝ))
      (E := (cell12225 ⟨19, by decide⟩).energy) (xi := (347397722670537 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12225 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12225]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12225])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12225) (a := (83420223207573 / 100000000000000 : ℝ)) (b := (168573401311 / 100000000000000 : ℝ)) (q := (1157576551203 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12225])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12225])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12225]

theorem cert12226_0 : CellCertificate 12226 (450212816205331 / 5000000000000000 : ℝ) (343607008849341 / 200000000000000000 : ℝ) (347368541485789 / 10000000000000000 : ℝ)
    (cell12226 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · have h := gap_lower (n := 12226) (a := (84083440092637 / 100000000000000 : ℝ)) (b := (168559427229 / 100000000000000 : ℝ)) (q := (578731965013 / 25000000000000 : ℝ))
      (E := (cell12226 ⟨0, by decide⟩).energy) (xi := (347368541485789 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12226 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12226]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12226])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12226) (a := (84083440092637 / 100000000000000 : ℝ)) (b := (168559427229 / 100000000000000 : ℝ)) (q := (578731965013 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12226])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12226])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12226]

theorem cert12226_1 : CellCertificate 12226 (450212816205331 / 5000000000000000 : ℝ) (343607008849341 / 200000000000000000 : ℝ) (347368541485789 / 10000000000000000 : ℝ)
    (cell12226 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · have h := gap_lower (n := 12226) (a := (42024154431293 / 50000000000000 : ℝ)) (b := (168559427229 / 100000000000000 : ℝ)) (q := (2314931853253 / 100000000000000 : ℝ))
      (E := (cell12226 ⟨1, by decide⟩).energy) (xi := (347368541485789 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12226 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12226]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12226])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12226) (a := (42024154431293 / 50000000000000 : ℝ)) (b := (168559427229 / 100000000000000 : ℝ)) (q := (2314931853253 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12226])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12226])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12226]

theorem cert12226_2 : CellCertificate 12226 (450212816205331 / 5000000000000000 : ℝ) (343607008849341 / 200000000000000000 : ℝ) (347368541485789 / 10000000000000000 : ℝ)
    (cell12226 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · have h := gap_lower (n := 12226) (a := (21003300697063 / 25000000000000 : ℝ)) (b := (168559427229 / 100000000000000 : ℝ)) (q := (289366981083 / 12500000000000 : ℝ))
      (E := (cell12226 ⟨2, by decide⟩).energy) (xi := (347368541485789 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12226 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12226]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12226])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12226) (a := (21003300697063 / 25000000000000 : ℝ)) (b := (168559427229 / 100000000000000 : ℝ)) (q := (289366981083 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12226])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12226])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12226]

theorem cert12226_3 : CellCertificate 12226 (450212816205331 / 5000000000000000 : ℝ) (343607008849341 / 200000000000000000 : ℝ) (347368541485789 / 10000000000000000 : ℝ)
    (cell12226 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · have h := gap_lower (n := 12226) (a := (20994530458161 / 25000000000000 : ℝ)) (b := (168559427229 / 100000000000000 : ℝ)) (q := (1157469899129 / 50000000000000 : ℝ))
      (E := (cell12226 ⟨3, by decide⟩).energy) (xi := (347368541485789 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12226 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12226]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12226])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12226) (a := (20994530458161 / 25000000000000 : ℝ)) (b := (168559427229 / 100000000000000 : ℝ)) (q := (1157469899129 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12226])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12226])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12226]

theorem cert12226_4 : CellCertificate 12226 (450212816205331 / 5000000000000000 : ℝ) (343607008849341 / 200000000000000000 : ℝ) (347368541485789 / 10000000000000000 : ℝ)
    (cell12226 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · have h := gap_lower (n := 12226) (a := (83943065958963 / 100000000000000 : ℝ)) (b := (168559427229 / 100000000000000 : ℝ)) (q := (462988765443 / 20000000000000 : ℝ))
      (E := (cell12226 ⟨4, by decide⟩).energy) (xi := (347368541485789 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12226 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12226]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12226])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12226) (a := (83943065958963 / 100000000000000 : ℝ)) (b := (168559427229 / 100000000000000 : ℝ)) (q := (462988765443 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12226])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12226])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12226]

theorem cert12226_5 : CellCertificate 12226 (450212816205331 / 5000000000000000 : ℝ) (343607008849341 / 200000000000000000 : ℝ) (347368541485789 / 10000000000000000 : ℝ)
    (cell12226 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · have h := gap_lower (n := 12226) (a := (8390803513061 / 10000000000000 : ℝ)) (b := (168559427229 / 100000000000000 : ℝ)) (q := (2314947829133 / 100000000000000 : ℝ))
      (E := (cell12226 ⟨5, by decide⟩).energy) (xi := (347368541485789 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12226 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12226]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12226])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12226) (a := (8390803513061 / 10000000000000 : ℝ)) (b := (168559427229 / 100000000000000 : ℝ)) (q := (2314947829133 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12226])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12226])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12226]

theorem cert12226_6 : CellCertificate 12226 (450212816205331 / 5000000000000000 : ℝ) (343607008849341 / 200000000000000000 : ℝ) (347368541485789 / 10000000000000000 : ℝ)
    (cell12226 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · have h := gap_lower (n := 12226) (a := (41936514655587 / 50000000000000 : ℝ)) (b := (168559427229 / 100000000000000 : ℝ)) (q := (578737953241 / 25000000000000 : ℝ))
      (E := (cell12226 ⟨6, by decide⟩).energy) (xi := (347368541485789 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12226 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12226]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12226])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12226) (a := (41936514655587 / 50000000000000 : ℝ)) (b := (168559427229 / 100000000000000 : ℝ)) (q := (578737953241 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12226])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12226])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12226]

theorem cert12226_7 : CellCertificate 12226 (450212816205331 / 5000000000000000 : ℝ) (343607008849341 / 200000000000000000 : ℝ) (347368541485789 / 10000000000000000 : ℝ)
    (cell12226 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · have h := gap_lower (n := 12226) (a := (2095951211611 / 2500000000000 : ℝ)) (b := (168559427229 / 100000000000000 : ℝ)) (q := (1157477893701 / 50000000000000 : ℝ))
      (E := (cell12226 ⟨7, by decide⟩).energy) (xi := (347368541485789 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12226 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12226]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12226])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12226) (a := (2095951211611 / 2500000000000 : ℝ)) (b := (168559427229 / 100000000000000 : ℝ)) (q := (1157477893701 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12226])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12226])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12226]

theorem cert12226_8 : CellCertificate 12226 (450212816205331 / 5000000000000000 : ℝ) (343607008849341 / 200000000000000000 : ℝ) (347368541485789 / 10000000000000000 : ℝ)
    (cell12226 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · have h := gap_lower (n := 12226) (a := (83803092554381 / 100000000000000 : ℝ)) (b := (168559427229 / 100000000000000 : ℝ)) (q := (578739940221 / 25000000000000 : ℝ))
      (E := (cell12226 ⟨8, by decide⟩).energy) (xi := (347368541485789 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12226 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12226]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12226])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12226) (a := (83803092554381 / 100000000000000 : ℝ)) (b := (168559427229 / 100000000000000 : ℝ)) (q := (578739940221 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12226])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12226])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12226]

theorem cert12226_9 : CellCertificate 12226 (450212816205331 / 5000000000000000 : ℝ) (343607008849341 / 200000000000000000 : ℝ) (347368541485789 / 10000000000000000 : ℝ)
    (cell12226 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · have h := gap_lower (n := 12226) (a := (2094204038629 / 2500000000000 : ℝ)) (b := (168559427229 / 100000000000000 : ℝ)) (q := (289370467699 / 12500000000000 : ℝ))
      (E := (cell12226 ⟨9, by decide⟩).energy) (xi := (347368541485789 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12226 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12226]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12226])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12226) (a := (2094204038629 / 2500000000000 : ℝ)) (b := (168559427229 / 100000000000000 : ℝ)) (q := (289370467699 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12226])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12226])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12226]

theorem cert12226_10 : CellCertificate 12226 (450212816205331 / 5000000000000000 : ℝ) (343607008849341 / 200000000000000000 : ℝ) (347368541485789 / 10000000000000000 : ℝ)
    (cell12226 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · have h := gap_lower (n := 12226) (a := (83733255401129 / 100000000000000 : ℝ)) (b := (168559427229 / 100000000000000 : ℝ)) (q := (2314967737451 / 100000000000000 : ℝ))
      (E := (cell12226 ⟨10, by decide⟩).energy) (xi := (347368541485789 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12226 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12226]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12226])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12226) (a := (83733255401129 / 100000000000000 : ℝ)) (b := (168559427229 / 100000000000000 : ℝ)) (q := (2314967737451 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12226])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12226])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12226]

theorem cert12226_11 : CellCertificate 12226 (450212816205331 / 5000000000000000 : ℝ) (343607008849341 / 200000000000000000 : ℝ) (347368541485789 / 10000000000000000 : ℝ)
    (cell12226 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · have h := gap_lower (n := 12226) (a := (83698374086827 / 100000000000000 : ℝ)) (b := (168559427229 / 100000000000000 : ℝ)) (q := (2314971756133 / 100000000000000 : ℝ))
      (E := (cell12226 ⟨11, by decide⟩).energy) (xi := (347368541485789 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12226 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12226]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12226])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12226) (a := (83698374086827 / 100000000000000 : ℝ)) (b := (168559427229 / 100000000000000 : ℝ)) (q := (2314971756133 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12226])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12226])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12226]

theorem cert12226_12 : CellCertificate 12226 (450212816205331 / 5000000000000000 : ℝ) (343607008849341 / 200000000000000000 : ℝ) (347368541485789 / 10000000000000000 : ℝ)
    (cell12226 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · have h := gap_lower (n := 12226) (a := (41831758783489 / 50000000000000 : ℝ)) (b := (168559427229 / 100000000000000 : ℝ)) (q := (2314975747021 / 100000000000000 : ℝ))
      (E := (cell12226 ⟨12, by decide⟩).energy) (xi := (347368541485789 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12226 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12226]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12226])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12226) (a := (41831758783489 / 50000000000000 : ℝ)) (b := (168559427229 / 100000000000000 : ℝ)) (q := (2314975747021 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12226])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12226])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12226]

theorem cert12226_13 : CellCertificate 12226 (450212816205331 / 5000000000000000 : ℝ) (343607008849341 / 200000000000000000 : ℝ) (347368541485789 / 10000000000000000 : ℝ)
    (cell12226 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · have h := gap_lower (n := 12226) (a := (83628685806491 / 100000000000000 : ℝ)) (b := (168559427229 / 100000000000000 : ℝ)) (q := (578744929303 / 25000000000000 : ℝ))
      (E := (cell12226 ⟨13, by decide⟩).energy) (xi := (347368541485789 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12226 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12226]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12226])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12226) (a := (83628685806491 / 100000000000000 : ℝ)) (b := (168559427229 / 100000000000000 : ℝ)) (q := (578744929303 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12226])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12226])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12226]

theorem cert12226_14 : CellCertificate 12226 (450212816205331 / 5000000000000000 : ℝ) (343607008849341 / 200000000000000000 : ℝ) (347368541485789 / 10000000000000000 : ℝ)
    (cell12226 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · have h := gap_lower (n := 12226) (a := (41796939385229 / 50000000000000 : ℝ)) (b := (168559427229 / 100000000000000 : ℝ)) (q := (2314983731643 / 100000000000000 : ℝ))
      (E := (cell12226 ⟨14, by decide⟩).energy) (xi := (347368541485789 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12226 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12226]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12226])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12226) (a := (41796939385229 / 50000000000000 : ℝ)) (b := (168559427229 / 100000000000000 : ℝ)) (q := (2314983731643 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12226])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12226])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12226]

theorem cert12226_15 : CellCertificate 12226 (450212816205331 / 5000000000000000 : ℝ) (343607008849341 / 200000000000000000 : ℝ) (347368541485789 / 10000000000000000 : ℝ)
    (cell12226 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · have h := gap_lower (n := 12226) (a := (41779548212077 / 50000000000000 : ℝ)) (b := (168559427229 / 100000000000000 : ℝ)) (q := (1157493869437 / 50000000000000 : ℝ))
      (E := (cell12226 ⟨15, by decide⟩).energy) (xi := (347368541485789 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12226 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12226]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12226])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12226) (a := (41779548212077 / 50000000000000 : ℝ)) (b := (168559427229 / 100000000000000 : ℝ)) (q := (1157493869437 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12226])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12226])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12226]

theorem cert12226_16 : CellCertificate 12226 (450212816205331 / 5000000000000000 : ℝ) (343607008849341 / 200000000000000000 : ℝ) (347368541485789 / 10000000000000000 : ℝ)
    (cell12226 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · have h := gap_lower (n := 12226) (a := (83524338733033 / 100000000000000 : ℝ)) (b := (168559427229 / 100000000000000 : ℝ)) (q := (2314991687123 / 100000000000000 : ℝ))
      (E := (cell12226 ⟨16, by decide⟩).energy) (xi := (347368541485789 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12226 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12226]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12226])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12226) (a := (83524338733033 / 100000000000000 : ℝ)) (b := (168559427229 / 100000000000000 : ℝ)) (q := (2314991687123 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12226])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12226])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12226]

theorem cert12226_17 : CellCertificate 12226 (450212816205331 / 5000000000000000 : ℝ) (343607008849341 / 200000000000000000 : ℝ) (347368541485789 / 10000000000000000 : ℝ)
    (cell12226 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · have h := gap_lower (n := 12226) (a := (20872401415683 / 25000000000000 : ℝ)) (b := (168559427229 / 100000000000000 : ℝ)) (q := (115749784937 / 5000000000000 : ℝ))
      (E := (cell12226 ⟨17, by decide⟩).energy) (xi := (347368541485789 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12226 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12226]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12226])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12226) (a := (20872401415683 / 25000000000000 : ℝ)) (b := (168559427229 / 100000000000000 : ℝ)) (q := (115749784937 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12226])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12226])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12226]

theorem cert12226_18 : CellCertificate 12226 (450212816205331 / 5000000000000000 : ℝ) (343607008849341 / 200000000000000000 : ℝ) (347368541485789 / 10000000000000000 : ℝ)
    (cell12226 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · have h := gap_lower (n := 12226) (a := (16690979435813 / 20000000000000 : ℝ)) (b := (168559427229 / 100000000000000 : ℝ)) (q := (1157499831647 / 50000000000000 : ℝ))
      (E := (cell12226 ⟨18, by decide⟩).energy) (xi := (347368541485789 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12226 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12226]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12226])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12226) (a := (16690979435813 / 20000000000000 : ℝ)) (b := (168559427229 / 100000000000000 : ℝ)) (q := (1157499831647 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12226])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12226])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12226]

theorem cert12226_19 : CellCertificate 12226 (450212816205331 / 5000000000000000 : ℝ) (343607008849341 / 200000000000000000 : ℝ) (347368541485789 / 10000000000000000 : ℝ)
    (cell12226 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · have h := gap_lower (n := 12226) (a := (41710106624011 / 50000000000000 : ℝ)) (b := (168559427229 / 100000000000000 : ℝ)) (q := (115750185137 / 5000000000000 : ℝ))
      (E := (cell12226 ⟨19, by decide⟩).energy) (xi := (347368541485789 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12226 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12226]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12226])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12226) (a := (41710106624011 / 50000000000000 : ℝ)) (b := (168559427229 / 100000000000000 : ℝ)) (q := (115750185137 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12226])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12226])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12226]

theorem cert12227_0 : CellCertificate 12227 (450197788458709 / 5000000000000000 : ℝ) (171789448468463 / 100000000000000000 : ℝ) (69467873066693 / 2000000000000000 : ℝ)
    (cell12227 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · have h := gap_lower (n := 12227) (a := (84083423767209 / 100000000000000 : ℝ)) (b := (33709091099 / 20000000000000 : ℝ)) (q := (2314778469467 / 100000000000000 : ℝ))
      (E := (cell12227 ⟨0, by decide⟩).energy) (xi := (69467873066693 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12227 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12227]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12227])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12227) (a := (84083423767209 / 100000000000000 : ℝ)) (b := (33709091099 / 20000000000000 : ℝ)) (q := (2314778469467 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12227])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12227])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12227]

theorem cert12227_1 : CellCertificate 12227 (450197788458709 / 5000000000000000 : ℝ) (171789448468463 / 100000000000000000 : ℝ) (69467873066693 / 2000000000000000 : ℝ)
    (cell12227 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · have h := gap_lower (n := 12227) (a := (21012073219147 / 25000000000000 : ℝ)) (b := (33709091099 / 20000000000000 : ℝ)) (q := (2314782512553 / 100000000000000 : ℝ))
      (E := (cell12227 ⟨1, by decide⟩).energy) (xi := (69467873066693 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12227 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12227]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12227])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12227) (a := (21012073219147 / 25000000000000 : ℝ)) (b := (33709091099 / 20000000000000 : ℝ)) (q := (2314782512553 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12227])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12227])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12227]

theorem cert12227_2 : CellCertificate 12227 (450197788458709 / 5000000000000000 : ℝ) (171789448468463 / 100000000000000000 : ℝ) (69467873066693 / 2000000000000000 : ℝ)
    (cell12227 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · have h := gap_lower (n := 12227) (a := (84013187141203 / 100000000000000 : ℝ)) (b := (33709091099 / 20000000000000 : ℝ)) (q := (2314786500893 / 100000000000000 : ℝ))
      (E := (cell12227 ⟨2, by decide⟩).energy) (xi := (69467873066693 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12227 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12227]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12227])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12227) (a := (84013187141203 / 100000000000000 : ℝ)) (b := (33709091099 / 20000000000000 : ℝ)) (q := (2314786500893 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12227])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12227])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12227]

theorem cert12227_3 : CellCertificate 12227 (450197788458709 / 5000000000000000 : ℝ) (171789448468463 / 100000000000000000 : ℝ) (69467873066693 / 2000000000000000 : ℝ)
    (cell12227 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · have h := gap_lower (n := 12227) (a := (41989053262031 / 50000000000000 : ℝ)) (b := (33709091099 / 20000000000000 : ℝ)) (q := (2314790444219 / 100000000000000 : ℝ))
      (E := (cell12227 ⟨3, by decide⟩).energy) (xi := (69467873066693 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12227 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12227]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12227])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12227) (a := (41989053262031 / 50000000000000 : ℝ)) (b := (33709091099 / 20000000000000 : ℝ)) (q := (2314790444219 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12227])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12227])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12227]

theorem cert12227_4 : CellCertificate 12227 (450197788458709 / 5000000000000000 : ℝ) (171789448468463 / 100000000000000000 : ℝ) (69467873066693 / 2000000000000000 : ℝ)
    (cell12227 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · have h := gap_lower (n := 12227) (a := (83943050988369 / 100000000000000 : ℝ)) (b := (33709091099 / 20000000000000 : ℝ)) (q := (578698616927 / 25000000000000 : ℝ))
      (E := (cell12227 ⟨4, by decide⟩).energy) (xi := (69467873066693 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12227 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12227]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12227])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12227) (a := (83943050988369 / 100000000000000 : ℝ)) (b := (33709091099 / 20000000000000 : ℝ)) (q := (578698616927 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12227])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12227])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12227]

theorem cert12227_5 : CellCertificate 12227 (450197788458709 / 5000000000000000 : ℝ) (171789448468463 / 100000000000000000 : ℝ) (69467873066693 / 2000000000000000 : ℝ)
    (cell12227 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · have h := gap_lower (n := 12227) (a := (20977005124381 / 25000000000000 : ℝ)) (b := (33709091099 / 20000000000000 : ℝ)) (q := (2314798464959 / 100000000000000 : ℝ))
      (E := (cell12227 ⟨5, by decide⟩).energy) (xi := (69467873066693 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12227 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12227]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12227])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12227) (a := (20977005124381 / 25000000000000 : ℝ)) (b := (33709091099 / 20000000000000 : ℝ)) (q := (2314798464959 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12227])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12227])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12227]

theorem cert12227_6 : CellCertificate 12227 (450197788458709 / 5000000000000000 : ℝ) (171789448468463 / 100000000000000000 : ℝ) (69467873066693 / 2000000000000000 : ℝ)
    (cell12227 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · have h := gap_lower (n := 12227) (a := (83873015015119 / 100000000000000 : ℝ)) (b := (33709091099 / 20000000000000 : ℝ)) (q := (2314802444923 / 100000000000000 : ℝ))
      (E := (cell12227 ⟨6, by decide⟩).energy) (xi := (69467873066693 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12227 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12227]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12227])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12227) (a := (83873015015119 / 100000000000000 : ℝ)) (b := (33709091099 / 20000000000000 : ℝ)) (q := (2314802444923 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12227])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12227])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12227]

theorem cert12227_7 : CellCertificate 12227 (450197788458709 / 5000000000000000 : ℝ) (171789448468463 / 100000000000000000 : ℝ) (69467873066693 / 2000000000000000 : ℝ)
    (cell12227 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · have h := gap_lower (n := 12227) (a := (41919017252469 / 50000000000000 : ℝ)) (b := (33709091099 / 20000000000000 : ℝ)) (q := (578701604073 / 25000000000000 : ℝ))
      (E := (cell12227 ⟨7, by decide⟩).energy) (xi := (69467873066693 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12227 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12227]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12227])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12227) (a := (41919017252469 / 50000000000000 : ℝ)) (b := (33709091099 / 20000000000000 : ℝ)) (q := (578701604073 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12227])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12227])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12227]

theorem cert12227_8 : CellCertificate 12227 (450197788458709 / 5000000000000000 : ℝ) (171789448468463 / 100000000000000000 : ℝ) (69467873066693 / 2000000000000000 : ℝ)
    (cell12227 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · have h := gap_lower (n := 12227) (a := (83803078930957 / 100000000000000 : ℝ)) (b := (33709091099 / 20000000000000 : ℝ)) (q := (2314810445449 / 100000000000000 : ℝ))
      (E := (cell12227 ⟨8, by decide⟩).energy) (xi := (69467873066693 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12227 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12227]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12227])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12227) (a := (83803078930957 / 100000000000000 : ℝ)) (b := (33709091099 / 20000000000000 : ℝ)) (q := (2314810445449 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12227])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12227])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12227]

theorem cert12227_9 : CellCertificate 12227 (450197788458709 / 5000000000000000 : ℝ) (171789448468463 / 100000000000000000 : ℝ) (69467873066693 / 2000000000000000 : ℝ)
    (cell12227 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · have h := gap_lower (n := 12227) (a := (83768148257339 / 100000000000000 : ℝ)) (b := (33709091099 / 20000000000000 : ℝ)) (q := (462962884941 / 20000000000000 : ℝ))
      (E := (cell12227 ⟨9, by decide⟩).energy) (xi := (69467873066693 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12227 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12227]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12227])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12227) (a := (83768148257339 / 100000000000000 : ℝ)) (b := (33709091099 / 20000000000000 : ℝ)) (q := (462962884941 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12227])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12227])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12227]

theorem cert12227_10 : CellCertificate 12227 (450197788458709 / 5000000000000000 : ℝ) (171789448468463 / 100000000000000000 : ℝ) (69467873066693 / 2000000000000000 : ℝ)
    (cell12227 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · have h := gap_lower (n := 12227) (a := (41866621224219 / 50000000000000 : ℝ)) (b := (33709091099 / 20000000000000 : ℝ)) (q := (1157409209953 / 50000000000000 : ℝ))
      (E := (cell12227 ⟨10, by decide⟩).energy) (xi := (69467873066693 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12227 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12227]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12227])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12227) (a := (41866621224219 / 50000000000000 : ℝ)) (b := (33709091099 / 20000000000000 : ℝ)) (q := (1157409209953 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12227])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12227])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12227]

theorem cert12227_11 : CellCertificate 12227 (450197788458709 / 5000000000000000 : ℝ) (171789448468463 / 100000000000000000 : ℝ) (69467873066693 / 2000000000000000 : ℝ)
    (cell12227 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · have h := gap_lower (n := 12227) (a := (83698361468793 / 100000000000000 : ℝ)) (b := (33709091099 / 20000000000000 : ℝ)) (q := (231482238071 / 10000000000000 : ℝ))
      (E := (cell12227 ⟨11, by decide⟩).energy) (xi := (69467873066693 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12227 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12227]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12227])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12227) (a := (83698361468793 / 100000000000000 : ℝ)) (b := (33709091099 / 20000000000000 : ℝ)) (q := (231482238071 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12227])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12227])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12227]

theorem cert12227_12 : CellCertificate 12227 (450197788458709 / 5000000000000000 : ℝ) (171789448468463 / 100000000000000000 : ℝ) (69467873066693 / 2000000000000000 : ℝ)
    (cell12227 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · have h := gap_lower (n := 12227) (a := (10457938160391 / 12500000000000 : ℝ)) (b := (33709091099 / 20000000000000 : ℝ)) (q := (1157413186253 / 50000000000000 : ℝ))
      (E := (cell12227 ⟨12, by decide⟩).energy) (xi := (69467873066693 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12227 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12227]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12227])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12227) (a := (10457938160391 / 12500000000000 : ℝ)) (b := (33709091099 / 20000000000000 : ℝ)) (q := (1157413186253 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12227])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12227])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12227]

theorem cert12227_13 : CellCertificate 12227 (450197788458709 / 5000000000000000 : ℝ) (171789448468463 / 100000000000000000 : ℝ) (69467873066693 / 2000000000000000 : ℝ)
    (cell12227 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · have h := gap_lower (n := 12227) (a := (16725734771271 / 20000000000000 : ℝ)) (b := (33709091099 / 20000000000000 : ℝ)) (q := (2314830402461 / 100000000000000 : ℝ))
      (E := (cell12227 ⟨13, by decide⟩).energy) (xi := (69467873066693 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12227 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12227]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12227])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12227) (a := (16725734771271 / 20000000000000 : ℝ)) (b := (33709091099 / 20000000000000 : ℝ)) (q := (2314830402461 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12227])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12227])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12227]

theorem cert12227_14 : CellCertificate 12227 (450197788458709 / 5000000000000000 : ℝ) (171789448468463 / 100000000000000000 : ℝ) (69467873066693 / 2000000000000000 : ℝ)
    (cell12227 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · have h := gap_lower (n := 12227) (a := (83593867153567 / 100000000000000 : ℝ)) (b := (33709091099 / 20000000000000 : ℝ)) (q := (2314834361319 / 100000000000000 : ℝ))
      (E := (cell12227 ⟨14, by decide⟩).energy) (xi := (69467873066693 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12227 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12227]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12227])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12227) (a := (83593867153567 / 100000000000000 : ℝ)) (b := (33709091099 / 20000000000000 : ℝ)) (q := (2314834361319 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12227])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12227])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12227]

theorem cert12227_15 : CellCertificate 12227 (450197788458709 / 5000000000000000 : ℝ) (171789448468463 / 100000000000000000 : ℝ) (69467873066693 / 2000000000000000 : ℝ)
    (cell12227 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · have h := gap_lower (n := 12227) (a := (41779542570019 / 50000000000000 : ℝ)) (b := (33709091099 / 20000000000000 : ℝ)) (q := (289354796479 / 12500000000000 : ℝ))
      (E := (cell12227 ⟨15, by decide⟩).energy) (xi := (69467873066693 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12227 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12227]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12227])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12227) (a := (41779542570019 / 50000000000000 : ℝ)) (b := (33709091099 / 20000000000000 : ℝ)) (q := (289354796479 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12227])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12227])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12227]

theorem cert12227_16 : CellCertificate 12227 (450197788458709 / 5000000000000000 : ℝ) (171789448468463 / 100000000000000000 : ℝ) (69467873066693 / 2000000000000000 : ℝ)
    (cell12227 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · have h := gap_lower (n := 12227) (a := (41762163890613 / 50000000000000 : ℝ)) (b := (33709091099 / 20000000000000 : ℝ)) (q := (2314842324151 / 100000000000000 : ℝ))
      (E := (cell12227 ⟨16, by decide⟩).energy) (xi := (69467873066693 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12227 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12227]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12227])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12227) (a := (41762163890613 / 50000000000000 : ℝ)) (b := (33709091099 / 20000000000000 : ℝ)) (q := (2314842324151 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12227])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12227])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12227]

theorem cert12227_17 : CellCertificate 12227 (450197788458709 / 5000000000000000 : ℝ) (171789448468463 / 100000000000000000 : ℝ) (69467873066693 / 2000000000000000 : ℝ)
    (cell12227 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · have h := gap_lower (n := 12227) (a := (41744797521383 / 50000000000000 : ℝ)) (b := (33709091099 / 20000000000000 : ℝ)) (q := (2314846340629 / 100000000000000 : ℝ))
      (E := (cell12227 ⟨17, by decide⟩).energy) (xi := (69467873066693 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12227 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12227]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12227])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12227) (a := (41744797521383 / 50000000000000 : ℝ)) (b := (33709091099 / 20000000000000 : ℝ)) (q := (2314846340629 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12227])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12227])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12227]

theorem cert12227_18 : CellCertificate 12227 (450197788458709 / 5000000000000000 : ℝ) (171789448468463 / 100000000000000000 : ℝ) (69467873066693 / 2000000000000000 : ℝ)
    (cell12227 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · have h := gap_lower (n := 12227) (a := (83454886890473 / 100000000000000 : ℝ)) (b := (33709091099 / 20000000000000 : ℝ)) (q := (2314850310831 / 100000000000000 : ℝ))
      (E := (cell12227 ⟨18, by decide⟩).energy) (xi := (69467873066693 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12227 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12227]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12227])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12227) (a := (83454886890473 / 100000000000000 : ℝ)) (b := (33709091099 / 20000000000000 : ℝ)) (q := (2314850310831 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12227])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12227])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12227]

theorem cert12227_19 : CellCertificate 12227 (450197788458709 / 5000000000000000 : ℝ) (171789448468463 / 100000000000000000 : ℝ) (69467873066693 / 2000000000000000 : ℝ)
    (cell12227 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · have h := gap_lower (n := 12227) (a := (83420203290341 / 100000000000000 : ℝ)) (b := (33709091099 / 20000000000000 : ℝ)) (q := (1157427149253 / 50000000000000 : ℝ))
      (E := (cell12227 ⟨19, by decide⟩).energy) (xi := (69467873066693 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12227 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12227]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12227])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12227) (a := (83420203290341 / 100000000000000 : ℝ)) (b := (33709091099 / 20000000000000 : ℝ)) (q := (1157427149253 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12227])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12227])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12227]

theorem cert12228_0 : CellCertificate 12228 (450182763081037 / 5000000000000000 : ℝ) (13419952719689 / 7812500000000000 : ℝ) (347310194212083 / 10000000000000000 : ℝ)
    (cell12228 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · have h := gap_lower (n := 12228) (a := (42041703722227 / 50000000000000 : ℝ)) (b := (168531486109 / 100000000000000 : ℝ)) (q := (462925849353 / 20000000000000 : ℝ))
      (E := (cell12228 ⟨0, by decide⟩).energy) (xi := (347310194212083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12228 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12228]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12228])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12228) (a := (42041703722227 / 50000000000000 : ℝ)) (b := (168531486109 / 100000000000000 : ℝ)) (q := (462925849353 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12228])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12228])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12228]

theorem cert12228_1 : CellCertificate 12228 (450182763081037 / 5000000000000000 : ℝ) (13419952719689 / 7812500000000000 : ℝ) (347310194212083 / 10000000000000000 : ℝ)
    (cell12228 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · have h := gap_lower (n := 12228) (a := (84048276893221 / 100000000000000 : ℝ)) (b := (168531486109 / 100000000000000 : ℝ)) (q := (462926644857 / 20000000000000 : ℝ))
      (E := (cell12228 ⟨1, by decide⟩).energy) (xi := (347310194212083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12228 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12228]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12228])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12228) (a := (84048276893221 / 100000000000000 : ℝ)) (b := (168531486109 / 100000000000000 : ℝ)) (q := (462926644857 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12228])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12228])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12228]

theorem cert12228_2 : CellCertificate 12228 (450182763081037 / 5000000000000000 : ℝ) (13419952719689 / 7812500000000000 : ℝ) (347310194212083 / 10000000000000000 : ℝ)
    (cell12228 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · have h := gap_lower (n := 12228) (a := (42006585748371 / 50000000000000 : ℝ)) (b := (168531486109 / 100000000000000 : ℝ)) (q := (2314637205621 / 100000000000000 : ℝ))
      (E := (cell12228 ⟨2, by decide⟩).energy) (xi := (347310194212083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12228 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12228]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12228])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12228) (a := (42006585748371 / 50000000000000 : ℝ)) (b := (168531486109 / 100000000000000 : ℝ)) (q := (2314637205621 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12228])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12228])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12228]

theorem cert12228_3 : CellCertificate 12228 (450182763081037 / 5000000000000000 : ℝ) (13419952719689 / 7812500000000000 : ℝ) (347310194212083 / 10000000000000000 : ℝ)
    (cell12228 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · have h := gap_lower (n := 12228) (a := (3359123648721 / 4000000000000 : ℝ)) (b := (168531486109 / 100000000000000 : ℝ)) (q := (36166268759 / 1562500000000 : ℝ))
      (E := (cell12228 ⟨3, by decide⟩).energy) (xi := (347310194212083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12228 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12228]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12228])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12228) (a := (3359123648721 / 4000000000000 : ℝ)) (b := (168531486109 / 100000000000000 : ℝ)) (q := (36166268759 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12228])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12228])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12228]

theorem cert12228_4 : CellCertificate 12228 (450182763081037 / 5000000000000000 : ℝ) (13419952719689 / 7812500000000000 : ℝ) (347310194212083 / 10000000000000000 : ℝ)
    (cell12228 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · have h := gap_lower (n := 12228) (a := (83943036020277 / 100000000000000 : ℝ)) (b := (168531486109 / 100000000000000 : ℝ)) (q := (2314645218689 / 100000000000000 : ℝ))
      (E := (cell12228 ⟨4, by decide⟩).energy) (xi := (347310194212083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12228 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12228]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12228])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12228) (a := (83943036020277 / 100000000000000 : ℝ)) (b := (168531486109 / 100000000000000 : ℝ)) (q := (2314645218689 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12228])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12228])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12228]

theorem cert12228_5 : CellCertificate 12228 (450182763081037 / 5000000000000000 : ℝ) (13419952719689 / 7812500000000000 : ℝ) (347310194212083 / 10000000000000000 : ℝ)
    (cell12228 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · have h := gap_lower (n := 12228) (a := (41954002933449 / 50000000000000 : ℝ)) (b := (168531486109 / 100000000000000 : ℝ)) (q := (578662302841 / 25000000000000 : ℝ))
      (E := (cell12228 ⟨5, by decide⟩).energy) (xi := (347310194212083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12228 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12228]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12228])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12228) (a := (41954002933449 / 50000000000000 : ℝ)) (b := (168531486109 / 100000000000000 : ℝ)) (q := (578662302841 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12228])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12228])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12228]

theorem cert12228_6 : CellCertificate 12228 (450182763081037 / 5000000000000000 : ℝ) (13419952719689 / 7812500000000000 : ℝ) (347310194212083 / 10000000000000000 : ℝ)
    (cell12228 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · have h := gap_lower (n := 12228) (a := (83873000721481 / 100000000000000 : ℝ)) (b := (168531486109 / 100000000000000 : ℝ)) (q := (2314653187551 / 100000000000000 : ℝ))
      (E := (cell12228 ⟨6, by decide⟩).energy) (xi := (347310194212083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12228 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12228]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12228])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12228) (a := (83873000721481 / 100000000000000 : ℝ)) (b := (168531486109 / 100000000000000 : ℝ)) (q := (2314653187551 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12228])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12228])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12228]

theorem cert12228_7 : CellCertificate 12228 (450182763081037 / 5000000000000000 : ℝ) (13419952719689 / 7812500000000000 : ℝ) (347310194212083 / 10000000000000000 : ℝ)
    (cell12228 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · have h := gap_lower (n := 12228) (a := (83838020547811 / 100000000000000 : ℝ)) (b := (168531486109 / 100000000000000 : ℝ)) (q := (1157328577971 / 50000000000000 : ℝ))
      (E := (cell12228 ⟨7, by decide⟩).energy) (xi := (347310194212083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12228 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12228]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12228])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12228) (a := (83838020547811 / 100000000000000 : ℝ)) (b := (168531486109 / 100000000000000 : ℝ)) (q := (1157328577971 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12228])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12228])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12228]

theorem cert12228_8 : CellCertificate 12228 (450182763081037 / 5000000000000000 : ℝ) (13419952719689 / 7812500000000000 : ℝ) (347310194212083 / 10000000000000000 : ℝ)
    (cell12228 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · have h := gap_lower (n := 12228) (a := (16760613061973 / 20000000000000 : ℝ)) (b := (168531486109 / 100000000000000 : ℝ)) (q := (1157330591459 / 50000000000000 : ℝ))
      (E := (cell12228 ⟨8, by decide⟩).energy) (xi := (347310194212083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12228 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12228]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12228])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12228) (a := (16760613061973 / 20000000000000 : ℝ)) (b := (168531486109 / 100000000000000 : ℝ)) (q := (1157330591459 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12228])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12228])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12228]

theorem cert12228_9 : CellCertificate 12228 (450182763081037 / 5000000000000000 : ℝ) (13419952719689 / 7812500000000000 : ℝ) (347310194212083 / 10000000000000000 : ℝ)
    (cell12228 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · have h := gap_lower (n := 12228) (a := (2617754217869 / 3125000000000 : ℝ)) (b := (168531486109 / 100000000000000 : ℝ)) (q := (2314665160789 / 100000000000000 : ℝ))
      (E := (cell12228 ⟨9, by decide⟩).energy) (xi := (347310194212083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12228 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12228]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12228])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12228) (a := (2617754217869 / 3125000000000 : ℝ)) (b := (168531486109 / 100000000000000 : ℝ)) (q := (2314665160789 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12228])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12228])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12228]

theorem cert12228_10 : CellCertificate 12228 (450182763081037 / 5000000000000000 : ℝ) (13419952719689 / 7812500000000000 : ℝ) (347310194212083 / 10000000000000000 : ℝ)
    (cell12228 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · have h := gap_lower (n := 12228) (a := (41866614748997 / 50000000000000 : ℝ)) (b := (168531486109 / 100000000000000 : ℝ)) (q := (2314669155401 / 100000000000000 : ℝ))
      (E := (cell12228 ⟨10, by decide⟩).energy) (xi := (347310194212083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12228 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12228]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12228])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12228) (a := (41866614748997 / 50000000000000 : ℝ)) (b := (168531486109 / 100000000000000 : ℝ)) (q := (2314669155401 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12228])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12228])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12228]

theorem cert12228_11 : CellCertificate 12228 (450182763081037 / 5000000000000000 : ℝ) (13419952719689 / 7812500000000000 : ℝ) (347310194212083 / 10000000000000000 : ℝ)
    (cell12228 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · have h := gap_lower (n := 12228) (a := (83698348852963 / 100000000000000 : ℝ)) (b := (168531486109 / 100000000000000 : ℝ)) (q := (2314673116409 / 100000000000000 : ℝ))
      (E := (cell12228 ⟨11, by decide⟩).energy) (xi := (347310194212083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12228 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12228]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12228])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12228) (a := (83698348852963 / 100000000000000 : ℝ)) (b := (168531486109 / 100000000000000 : ℝ)) (q := (2314673116409 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12228])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12228])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12228]

theorem cert12228_12 : CellCertificate 12228 (450182763081037 / 5000000000000000 : ℝ) (13419952719689 / 7812500000000000 : ℝ) (347310194212083 / 10000000000000000 : ℝ)
    (cell12228 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · have h := gap_lower (n := 12228) (a := (83663493001441 / 100000000000000 : ℝ)) (b := (168531486109 / 100000000000000 : ℝ)) (q := (1157338554601 / 50000000000000 : ℝ))
      (E := (cell12228 ⟨12, by decide⟩).energy) (xi := (347310194212083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12228 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12228]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12228])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12228) (a := (83663493001441 / 100000000000000 : ℝ)) (b := (168531486109 / 100000000000000 : ℝ)) (q := (1157338554601 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12228])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12228])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12228]

theorem cert12228_13 : CellCertificate 12228 (450182763081037 / 5000000000000000 : ℝ) (13419952719689 / 7812500000000000 : ℝ) (347310194212083 / 10000000000000000 : ℝ)
    (cell12228 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · have h := gap_lower (n := 12228) (a := (4181433095417 / 5000000000000 : ℝ)) (b := (168531486109 / 100000000000000 : ℝ)) (q := (578670285237 / 25000000000000 : ℝ))
      (E := (cell12228 ⟨13, by decide⟩).energy) (xi := (347310194212083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12228 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12228]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12228])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12228) (a := (4181433095417 / 5000000000000 : ℝ)) (b := (168531486109 / 100000000000000 : ℝ)) (q := (578670285237 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12228])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12228])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12228]

theorem cert12228_14 : CellCertificate 12228 (450182763081037 / 5000000000000000 : ℝ) (13419952719689 / 7812500000000000 : ℝ) (347310194212083 / 10000000000000000 : ℝ)
    (cell12228 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · have h := gap_lower (n := 12228) (a := (41796927769377 / 50000000000000 : ℝ)) (b := (168531486109 / 100000000000000 : ℝ)) (q := (578671275597 / 25000000000000 : ℝ))
      (E := (cell12228 ⟨14, by decide⟩).energy) (xi := (347310194212083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12228 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12228]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12228])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12228) (a := (41796927769377 / 50000000000000 : ℝ)) (b := (168531486109 / 100000000000000 : ℝ)) (q := (578671275597 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12228])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12228])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12228]

theorem cert12228_15 : CellCertificate 12228 (450182763081037 / 5000000000000000 : ℝ) (13419952719689 / 7812500000000000 : ℝ) (347310194212083 / 10000000000000000 : ℝ)
    (cell12228 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · have h := gap_lower (n := 12228) (a := (83559073857959 / 100000000000000 : ℝ)) (b := (168531486109 / 100000000000000 : ℝ)) (q := (144668069767 / 6250000000000 : ℝ))
      (E := (cell12228 ⟨15, by decide⟩).energy) (xi := (347310194212083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12228 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12228]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12228])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12228) (a := (83559073857959 / 100000000000000 : ℝ)) (b := (168531486109 / 100000000000000 : ℝ)) (q := (144668069767 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12228])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12228])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12228]

theorem cert12228_16 : CellCertificate 12228 (450182763081037 / 5000000000000000 : ℝ) (13419952719689 / 7812500000000000 : ℝ) (347310194212083 / 10000000000000000 : ℝ)
    (cell12228 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · have h := gap_lower (n := 12228) (a := (20881079207853 / 25000000000000 : ℝ)) (b := (168531486109 / 100000000000000 : ℝ)) (q := (1157346536377 / 50000000000000 : ℝ))
      (E := (cell12228 ⟨16, by decide⟩).energy) (xi := (347310194212083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12228 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12228]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12228])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12228) (a := (20881079207853 / 25000000000000 : ℝ)) (b := (168531486109 / 100000000000000 : ℝ)) (q := (1157346536377 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12228])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12228])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12228]

theorem cert12228_17 : CellCertificate 12228 (450182763081037 / 5000000000000000 : ℝ) (13419952719689 / 7812500000000000 : ℝ) (347310194212083 / 10000000000000000 : ℝ)
    (cell12228 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · have h := gap_lower (n := 12228) (a := (83489584424751 / 100000000000000 : ℝ)) (b := (168531486109 / 100000000000000 : ℝ)) (q := (1157348547091 / 50000000000000 : ℝ))
      (E := (cell12228 ⟨17, by decide⟩).energy) (xi := (347310194212083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12228 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12228]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12228])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12228) (a := (83489584424751 / 100000000000000 : ℝ)) (b := (168531486109 / 100000000000000 : ℝ)) (q := (1157348547091 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12228])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12228])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12228]

theorem cert12228_18 : CellCertificate 12228 (450182763081037 / 5000000000000000 : ℝ) (13419952719689 / 7812500000000000 : ℝ) (347310194212083 / 10000000000000000 : ℝ)
    (cell12228 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · have h := gap_lower (n := 12228) (a := (5215929787737 / 6250000000000 : ℝ)) (b := (168531486109 / 100000000000000 : ℝ)) (q := (2314701070121 / 100000000000000 : ℝ))
      (E := (cell12228 ⟨18, by decide⟩).energy) (xi := (347310194212083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12228 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12228]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12228])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12228) (a := (5215929787737 / 6250000000000 : ℝ)) (b := (168531486109 / 100000000000000 : ℝ)) (q := (2314701070121 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12228])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12228])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12228]

theorem cert12228_19 : CellCertificate 12228 (450182763081037 / 5000000000000000 : ℝ) (13419952719689 / 7812500000000000 : ℝ) (347310194212083 / 10000000000000000 : ℝ)
    (cell12228 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · have h := gap_lower (n := 12228) (a := (325860130213 / 390625000000 : ℝ)) (b := (168531486109 / 100000000000000 : ℝ)) (q := (2314705064321 / 100000000000000 : ℝ))
      (E := (cell12228 ⟨19, by decide⟩).energy) (xi := (347310194212083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12228 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12228]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12228])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12228) (a := (325860130213 / 390625000000 : ℝ)) (b := (168531486109 / 100000000000000 : ℝ)) (q := (2314705064321 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12228])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12228])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12228]

theorem cert12229_0 : CellCertificate 12229 (28135483754483 / 312500000000000 : ℝ) (343522686909549 / 200000000000000000 : ℝ) (173640514060081 / 5000000000000000 : ℝ)
    (cell12229 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · have h := gap_lower (n := 12229) (a := (84083391124373 / 100000000000000 : ℝ)) (b := (16851751907 / 10000000000000 : ℝ)) (q := (2314480076429 / 100000000000000 : ℝ))
      (E := (cell12229 ⟨0, by decide⟩).energy) (xi := (173640514060081 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12229 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12229]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12229])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12229) (a := (84083391124373 / 100000000000000 : ℝ)) (b := (16851751907 / 10000000000000 : ℝ)) (q := (2314480076429 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12229])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12229])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12229]

theorem cert12229_1 : CellCertificate 12229 (28135483754483 / 312500000000000 : ℝ) (343522686909549 / 200000000000000000 : ℝ) (173640514060081 / 5000000000000000 : ℝ)
    (cell12229 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · have h := gap_lower (n := 12229) (a := (16809652182497 / 20000000000000 : ℝ)) (b := (16851751907 / 10000000000000 : ℝ)) (q := (2314484046233 / 100000000000000 : ℝ))
      (E := (cell12229 ⟨1, by decide⟩).energy) (xi := (173640514060081 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12229 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12229]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12229])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12229) (a := (16809652182497 / 20000000000000 : ℝ)) (b := (16851751907 / 10000000000000 : ℝ)) (q := (2314484046233 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12229])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12229])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12229]

theorem cert12229_2 : CellCertificate 12229 (28135483754483 / 312500000000000 : ℝ) (343522686909549 / 200000000000000000 : ℝ) (173640514060081 / 5000000000000000 : ℝ)
    (cell12229 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · have h := gap_lower (n := 12229) (a := (21003288963717 / 25000000000000 : ℝ)) (b := (16851751907 / 10000000000000 : ℝ)) (q := (1157244010329 / 50000000000000 : ℝ))
      (E := (cell12229 ⟨2, by decide⟩).energy) (xi := (173640514060081 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12229 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12229]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12229])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12229) (a := (21003288963717 / 25000000000000 : ℝ)) (b := (16851751907 / 10000000000000 : ℝ)) (q := (1157244010329 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12229])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12229])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12229]

theorem cert12229_3 : CellCertificate 12229 (28135483754483 / 312500000000000 : ℝ) (343522686909549 / 200000000000000000 : ℝ) (173640514060081 / 5000000000000000 : ℝ)
    (cell12229 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · have h := gap_lower (n := 12229) (a := (83978075914533 / 100000000000000 : ℝ)) (b := (16851751907 / 10000000000000 : ℝ)) (q := (1157246004751 / 50000000000000 : ℝ))
      (E := (cell12229 ⟨3, by decide⟩).energy) (xi := (173640514060081 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12229 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12229]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12229])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12229) (a := (83978075914533 / 100000000000000 : ℝ)) (b := (16851751907 / 10000000000000 : ℝ)) (q := (1157246004751 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12229])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12229])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12229]

theorem cert12229_4 : CellCertificate 12229 (28135483754483 / 312500000000000 : ℝ) (343522686909549 / 200000000000000000 : ℝ) (173640514060081 / 5000000000000000 : ℝ)
    (cell12229 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · have h := gap_lower (n := 12229) (a := (83943021054687 / 100000000000000 : ℝ)) (b := (16851751907 / 10000000000000 : ℝ)) (q := (1157248011153 / 50000000000000 : ℝ))
      (E := (cell12229 ⟨4, by decide⟩).energy) (xi := (173640514060081 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12229 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12229]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12229])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12229) (a := (83943021054687 / 100000000000000 : ℝ)) (b := (16851751907 / 10000000000000 : ℝ)) (q := (1157248011153 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12229])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12229])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12229]

theorem cert12229_5 : CellCertificate 12229 (28135483754483 / 312500000000000 : ℝ) (343522686909549 / 200000000000000000 : ℝ) (173640514060081 / 5000000000000000 : ℝ)
    (cell12229 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · have h := gap_lower (n := 12229) (a := (83907991238731 / 100000000000000 : ℝ)) (b := (16851751907 / 10000000000000 : ℝ)) (q := (2314500010473 / 100000000000000 : ℝ))
      (E := (cell12229 ⟨5, by decide⟩).energy) (xi := (173640514060081 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12229 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12229]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12229])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12229) (a := (83907991238731 / 100000000000000 : ℝ)) (b := (16851751907 / 10000000000000 : ℝ)) (q := (2314500010473 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12229])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12229])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12229]

theorem cert12229_6 : CellCertificate 12229 (28135483754483 / 312500000000000 : ℝ) (343522686909549 / 200000000000000000 : ℝ) (173640514060081 / 5000000000000000 : ℝ)
    (cell12229 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · have h := gap_lower (n := 12229) (a := (83872986430259 / 100000000000000 : ℝ)) (b := (16851751907 / 10000000000000 : ℝ)) (q := (46290079659 / 2000000000000 : ℝ))
      (E := (cell12229 ⟨6, by decide⟩).energy) (xi := (173640514060081 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12229 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12229]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12229])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12229) (a := (83872986430259 / 100000000000000 : ℝ)) (b := (16851751907 / 10000000000000 : ℝ)) (q := (46290079659 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12229])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12229])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12229]

theorem cert12229_7 : CellCertificate 12229 (28135483754483 / 312500000000000 : ℝ) (343522686909549 / 200000000000000000 : ℝ) (173640514060081 / 5000000000000000 : ℝ)
    (cell12229 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · have h := gap_lower (n := 12229) (a := (41919003296529 / 50000000000000 : ℝ)) (b := (16851751907 / 10000000000000 : ℝ)) (q := (2314508006353 / 100000000000000 : ℝ))
      (E := (cell12229 ⟨7, by decide⟩).energy) (xi := (173640514060081 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12229 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12229]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12229])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12229) (a := (41919003296529 / 50000000000000 : ℝ)) (b := (16851751907 / 10000000000000 : ℝ)) (q := (2314508006353 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12229])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12229])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12229]

theorem cert12229_8 : CellCertificate 12229 (28135483754483 / 312500000000000 : ℝ) (343522686909549 / 200000000000000000 : ℝ) (173640514060081 / 5000000000000000 : ℝ)
    (cell12229 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · have h := gap_lower (n := 12229) (a := (16760610338221 / 20000000000000 : ℝ)) (b := (16851751907 / 10000000000000 : ℝ)) (q := (578627993323 / 25000000000000 : ℝ))
      (E := (cell12229 ⟨8, by decide⟩).energy) (xi := (173640514060081 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12229 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12229]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12229])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12229) (a := (16760610338221 / 20000000000000 : ℝ)) (b := (16851751907 / 10000000000000 : ℝ)) (q := (578627993323 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12229])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12229])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12229]

theorem cert12229_9 : CellCertificate 12229 (28135483754483 / 312500000000000 : ℝ) (343522686909549 / 200000000000000000 : ℝ) (173640514060081 / 5000000000000000 : ℝ)
    (cell12229 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · have h := gap_lower (n := 12229) (a := (83768121688567 / 100000000000000 : ℝ)) (b := (16851751907 / 10000000000000 : ℝ)) (q := (578628987461 / 25000000000000 : ℝ))
      (E := (cell12229 ⟨9, by decide⟩).energy) (xi := (173640514060081 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12229 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12229]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12229])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12229) (a := (83768121688567 / 100000000000000 : ℝ)) (b := (16851751907 / 10000000000000 : ℝ)) (q := (578628987461 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12229])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12229])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12229]

theorem cert12229_10 : CellCertificate 12229 (28135483754483 / 312500000000000 : ℝ) (343522686909549 / 200000000000000000 : ℝ) (173640514060081 / 5000000000000000 : ℝ)
    (cell12229 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · have h := gap_lower (n := 12229) (a := (83733216549797 / 100000000000000 : ℝ)) (b := (16851751907 / 10000000000000 : ℝ)) (q := (462903988787 / 20000000000000 : ℝ))
      (E := (cell12229 ⟨10, by decide⟩).energy) (xi := (173640514060081 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12229 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12229]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12229])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12229) (a := (83733216549797 / 100000000000000 : ℝ)) (b := (16851751907 / 10000000000000 : ℝ)) (q := (462903988787 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12229])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12229])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12229]

theorem cert12229_11 : CellCertificate 12229 (28135483754483 / 312500000000000 : ℝ) (343522686909549 / 200000000000000000 : ℝ) (173640514060081 / 5000000000000000 : ℝ)
    (cell12229 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · have h := gap_lower (n := 12229) (a := (41849168119669 / 50000000000000 : ℝ)) (b := (16851751907 / 10000000000000 : ℝ)) (q := (72328873851 / 3125000000000 : ℝ))
      (E := (cell12229 ⟨11, by decide⟩).energy) (xi := (173640514060081 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12229 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12229]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12229])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12229) (a := (41849168119669 / 50000000000000 : ℝ)) (b := (16851751907 / 10000000000000 : ℝ)) (q := (72328873851 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12229])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12229])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12229]

theorem cert12229_12 : CellCertificate 12229 (28135483754483 / 312500000000000 : ℝ) (343522686909549 / 200000000000000000 : ℝ) (173640514060081 / 5000000000000000 : ℝ)
    (cell12229 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · have h := gap_lower (n := 12229) (a := (83663480721917 / 100000000000000 : ℝ)) (b := (16851751907 / 10000000000000 : ℝ)) (q := (2314527957113 / 100000000000000 : ℝ))
      (E := (cell12229 ⟨12, by decide⟩).energy) (xi := (173640514060081 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12229 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12229]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12229])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12229) (a := (83663480721917 / 100000000000000 : ℝ)) (b := (16851751907 / 10000000000000 : ℝ)) (q := (2314527957113 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12229])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12229])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12229]

theorem cert12229_13 : CellCertificate 12229 (28135483754483 / 312500000000000 : ℝ) (343522686909549 / 200000000000000000 : ℝ) (173640514060081 / 5000000000000000 : ℝ)
    (cell12229 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · have h := gap_lower (n := 12229) (a := (41814324981223 / 50000000000000 : ℝ)) (b := (16851751907 / 10000000000000 : ℝ)) (q := (92581277307 / 4000000000000 : ℝ))
      (E := (cell12229 ⟨13, by decide⟩).energy) (xi := (173640514060081 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12229 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12229]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12229])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12229) (a := (41814324981223 / 50000000000000 : ℝ)) (b := (16851751907 / 10000000000000 : ℝ)) (q := (92581277307 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12229])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12229])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12229]

theorem cert12229_14 : CellCertificate 12229 (28135483754483 / 312500000000000 : ℝ) (343522686909549 / 200000000000000000 : ℝ) (173640514060081 / 5000000000000000 : ℝ)
    (cell12229 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · have h := gap_lower (n := 12229) (a := (4179692196301 / 5000000000000 : ℝ)) (b := (16851751907 / 10000000000000 : ℝ)) (q := (2314535954851 / 100000000000000 : ℝ))
      (E := (cell12229 ⟨14, by decide⟩).energy) (xi := (173640514060081 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12229 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12229]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12229])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12229) (a := (4179692196301 / 5000000000000 : ℝ)) (b := (16851751907 / 10000000000000 : ℝ)) (q := (2314535954851 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12229])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12229])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12229]

theorem cert12229_15 : CellCertificate 12229 (28135483754483 / 312500000000000 : ℝ) (343522686909549 / 200000000000000000 : ℝ) (173640514060081 / 5000000000000000 : ℝ)
    (cell12229 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · have h := gap_lower (n := 12229) (a := (20889765644479 / 25000000000000 : ℝ)) (b := (16851751907 / 10000000000000 : ℝ)) (q := (2314539914087 / 100000000000000 : ℝ))
      (E := (cell12229 ⟨15, by decide⟩).energy) (xi := (173640514060081 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12229 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12229]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12229])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12229) (a := (20889765644479 / 25000000000000 : ℝ)) (b := (16851751907 / 10000000000000 : ℝ)) (q := (2314539914087 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12229])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12229])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12229]

theorem cert12229_16 : CellCertificate 12229 (28135483754483 / 312500000000000 : ℝ) (343522686909549 / 200000000000000000 : ℝ) (173640514060081 / 5000000000000000 : ℝ)
    (cell12229 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · have h := gap_lower (n := 12229) (a := (83524305883593 / 100000000000000 : ℝ)) (b := (16851751907 / 10000000000000 : ℝ)) (q := (578635983233 / 25000000000000 : ℝ))
      (E := (cell12229 ⟨16, by decide⟩).energy) (xi := (173640514060081 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12229 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12229]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12229])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12229) (a := (83524305883593 / 100000000000000 : ℝ)) (b := (16851751907 / 10000000000000 : ℝ)) (q := (578635983233 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12229])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12229])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12229]

theorem cert12229_17 : CellCertificate 12229 (28135483754483 / 312500000000000 : ℝ) (343522686909549 / 200000000000000000 : ℝ) (173640514060081 / 5000000000000000 : ℝ)
    (cell12229 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · have h := gap_lower (n := 12229) (a := (8348957380869 / 10000000000000 : ℝ)) (b := (16851751907 / 10000000000000 : ℝ)) (q := (2314547901241 / 100000000000000 : ℝ))
      (E := (cell12229 ⟨17, by decide⟩).energy) (xi := (173640514060081 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12229 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12229]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12229])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12229) (a := (8348957380869 / 10000000000000 : ℝ)) (b := (16851751907 / 10000000000000 : ℝ)) (q := (2314547901241 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12229])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12229])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12229]

theorem cert12229_18 : CellCertificate 12229 (28135483754483 / 312500000000000 : ℝ) (343522686909549 / 200000000000000000 : ℝ) (173640514060081 / 5000000000000000 : ℝ)
    (cell12229 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · have h := gap_lower (n := 12229) (a := (41727433159511 / 50000000000000 : ℝ)) (b := (16851751907 / 10000000000000 : ℝ)) (q := (462910376597 / 20000000000000 : ℝ))
      (E := (cell12229 ⟨18, by decide⟩).energy) (xi := (173640514060081 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12229 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12229]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12229])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12229) (a := (41727433159511 / 50000000000000 : ℝ)) (b := (16851751907 / 10000000000000 : ℝ)) (q := (462910376597 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12229])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12229])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12229]

theorem cert12229_19 : CellCertificate 12229 (28135483754483 / 312500000000000 : ℝ) (343522686909549 / 200000000000000000 : ℝ) (173640514060081 / 5000000000000000 : ℝ)
    (cell12229 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · have h := gap_lower (n := 12229) (a := (16684036676117 / 20000000000000 : ℝ)) (b := (16851751907 / 10000000000000 : ℝ)) (q := (92582235351 / 4000000000000 : ℝ))
      (E := (cell12229 ⟨19, by decide⟩).energy) (xi := (173640514060081 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12229 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12229]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12229])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12229) (a := (16684036676117 / 20000000000000 : ℝ)) (b := (16851751907 / 10000000000000 : ℝ)) (q := (92582235351 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12229])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12229])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12229]

theorem cert12230_0 : CellCertificate 12230 (900305438860391 / 10000000000000000 : ℝ) (34349458879233 / 20000000000000000 : ℝ) (347251867056221 / 10000000000000000 : ℝ)
    (cell12230 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · have h := gap_lower (n := 12230) (a := (21020843701741 / 25000000000000 : ℝ)) (b := (84251777189 / 50000000000000 : ℝ)) (q := (2314330958461 / 100000000000000 : ℝ))
      (E := (cell12230 ⟨0, by decide⟩).energy) (xi := (347251867056221 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12230 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12230]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12230])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12230) (a := (21020843701741 / 25000000000000 : ℝ)) (b := (84251777189 / 50000000000000 : ℝ)) (q := (2314330958461 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12230])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12230])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12230]

theorem cert12230_1 : CellCertificate 12230 (900305438860391 / 10000000000000000 : ℝ) (34349458879233 / 20000000000000000 : ℝ) (347251867056221 / 10000000000000000 : ℝ)
    (cell12230 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · have h := gap_lower (n := 12230) (a := (42024122467189 / 50000000000000 : ℝ)) (b := (84251777189 / 50000000000000 : ℝ)) (q := (2892918723 / 125000000000 : ℝ))
      (E := (cell12230 ⟨1, by decide⟩).energy) (xi := (347251867056221 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12230 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12230]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12230])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12230) (a := (42024122467189 / 50000000000000 : ℝ)) (b := (84251777189 / 50000000000000 : ℝ)) (q := (2892918723 / 125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12230])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12230])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12230]

theorem cert12230_2 : CellCertificate 12230 (900305438860391 / 10000000000000000 : ℝ) (34349458879233 / 20000000000000000 : ℝ) (347251867056221 / 10000000000000000 : ℝ)
    (cell12230 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · have h := gap_lower (n := 12230) (a := (4200657010779 / 5000000000000 : ℝ)) (b := (84251777189 / 50000000000000 : ℝ)) (q := (578584736501 / 25000000000000 : ℝ))
      (E := (cell12230 ⟨2, by decide⟩).energy) (xi := (347251867056221 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12230 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12230]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12230])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12230) (a := (4200657010779 / 5000000000000 : ℝ)) (b := (84251777189 / 50000000000000 : ℝ)) (q := (578584736501 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12230])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12230])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12230]

theorem cert12230_3 : CellCertificate 12230 (900305438860391 / 10000000000000000 : ℝ) (34349458879233 / 20000000000000000 : ℝ) (347251867056221 / 10000000000000000 : ℝ)
    (cell12230 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · have h := gap_lower (n := 12230) (a := (5248628788349 / 6250000000000 : ℝ)) (b := (84251777189 / 50000000000000 : ℝ)) (q := (2314342928829 / 100000000000000 : ℝ))
      (E := (cell12230 ⟨3, by decide⟩).energy) (xi := (347251867056221 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12230 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12230]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12230])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12230) (a := (5248628788349 / 6250000000000 : ℝ)) (b := (84251777189 / 50000000000000 : ℝ)) (q := (2314342928829 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12230])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12230])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12230]

theorem cert12230_4 : CellCertificate 12230 (900305438860391 / 10000000000000000 : ℝ) (34349458879233 / 20000000000000000 : ℝ) (347251867056221 / 10000000000000000 : ℝ)
    (cell12230 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · have h := gap_lower (n := 12230) (a := (41971503045799 / 50000000000000 : ℝ)) (b := (84251777189 / 50000000000000 : ℝ)) (q := (1157173468207 / 50000000000000 : ℝ))
      (E := (cell12230 ⟨4, by decide⟩).energy) (xi := (347251867056221 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12230 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12230]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12230])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12230) (a := (41971503045799 / 50000000000000 : ℝ)) (b := (84251777189 / 50000000000000 : ℝ)) (q := (1157173468207 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12230])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12230])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12230]

theorem cert12230_5 : CellCertificate 12230 (900305438860391 / 10000000000000000 : ℝ) (34349458879233 / 20000000000000000 : ℝ) (347251867056221 / 10000000000000000 : ℝ)
    (cell12230 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · have h := gap_lower (n := 12230) (a := (41953988306511 / 50000000000000 : ℝ)) (b := (84251777189 / 50000000000000 : ℝ)) (q := (2314350920163 / 100000000000000 : ℝ))
      (E := (cell12230 ⟨5, by decide⟩).energy) (xi := (347251867056221 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12230 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12230]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12230])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12230) (a := (41953988306511 / 50000000000000 : ℝ)) (b := (84251777189 / 50000000000000 : ℝ)) (q := (2314350920163 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12230])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12230])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12230]

theorem cert12230_6 : CellCertificate 12230 (900305438860391 / 10000000000000000 : ℝ) (34349458879233 / 20000000000000000 : ℝ) (347251867056221 / 10000000000000000 : ℝ)
    (cell12230 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · have h := gap_lower (n := 12230) (a := (83872972141453 / 100000000000000 : ℝ)) (b := (84251777189 / 50000000000000 : ℝ)) (q := (1157177473461 / 50000000000000 : ℝ))
      (E := (cell12230 ⟨6, by decide⟩).energy) (xi := (347251867056221 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12230 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12230]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12230])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12230) (a := (83872972141453 / 100000000000000 : ℝ)) (b := (84251777189 / 50000000000000 : ℝ)) (q := (1157177473461 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12230])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12230])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12230]

theorem cert12230_7 : CellCertificate 12230 (900305438860391 / 10000000000000000 : ℝ) (34349458879233 / 20000000000000000 : ℝ) (347251867056221 / 10000000000000000 : ℝ)
    (cell12230 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · have h := gap_lower (n := 12230) (a := (41918996320339 / 50000000000000 : ℝ)) (b := (84251777189 / 50000000000000 : ℝ)) (q := (462871781921 / 20000000000000 : ℝ))
      (E := (cell12230 ⟨7, by decide⟩).energy) (xi := (347251867056221 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12230 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12230]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12230])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12230) (a := (41918996320339 / 50000000000000 : ℝ)) (b := (84251777189 / 50000000000000 : ℝ)) (q := (462871781921 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12230])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12230])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12230]

theorem cert12230_8 : CellCertificate 12230 (900305438860391 / 10000000000000000 : ℝ) (34349458879233 / 20000000000000000 : ℝ) (347251867056221 / 10000000000000000 : ℝ)
    (cell12230 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · have h := gap_lower (n := 12230) (a := (20950759518669 / 25000000000000 : ℝ)) (b := (84251777189 / 50000000000000 : ℝ)) (q := (2314362932467 / 100000000000000 : ℝ))
      (E := (cell12230 ⟨8, by decide⟩).energy) (xi := (347251867056221 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12230 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12230]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12230])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12230) (a := (20950759518669 / 25000000000000 : ℝ)) (b := (84251777189 / 50000000000000 : ℝ)) (q := (2314362932467 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12230])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12230])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12230]

theorem cert12230_9 : CellCertificate 12230 (900305438860391 / 10000000000000000 : ℝ) (34349458879233 / 20000000000000000 : ℝ) (347251867056221 / 10000000000000000 : ℝ)
    (cell12230 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · have h := gap_lower (n := 12230) (a := (83768108407613 / 100000000000000 : ℝ)) (b := (84251777189 / 50000000000000 : ℝ)) (q := (289295863477 / 12500000000000 : ℝ))
      (E := (cell12230 ⟨9, by decide⟩).energy) (xi := (347251867056221 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12230 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12230]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12230])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12230) (a := (83768108407613 / 100000000000000 : ℝ)) (b := (84251777189 / 50000000000000 : ℝ)) (q := (289295863477 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12230])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12230])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12230]

theorem cert12230_10 : CellCertificate 12230 (900305438860391 / 10000000000000000 : ℝ) (34349458879233 / 20000000000000000 : ℝ) (347251867056221 / 10000000000000000 : ℝ)
    (cell12230 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · have h := gap_lower (n := 12230) (a := (41866601801923 / 50000000000000 : ℝ)) (b := (84251777189 / 50000000000000 : ℝ)) (q := (2314370901497 / 100000000000000 : ℝ))
      (E := (cell12230 ⟨10, by decide⟩).energy) (xi := (347251867056221 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12230 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12230]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12230])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12230) (a := (41866601801923 / 50000000000000 : ℝ)) (b := (84251777189 / 50000000000000 : ℝ)) (q := (2314370901497 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12230])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12230])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12230]

theorem cert12230_11 : CellCertificate 12230 (900305438860391 / 10000000000000000 : ℝ) (34349458879233 / 20000000000000000 : ℝ) (347251867056221 / 10000000000000000 : ℝ)
    (cell12230 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · have h := gap_lower (n := 12230) (a := (83698323627917 / 100000000000000 : ℝ)) (b := (84251777189 / 50000000000000 : ℝ)) (q := (1157187431581 / 50000000000000 : ℝ))
      (E := (cell12230 ⟨11, by decide⟩).energy) (xi := (347251867056221 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12230 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12230]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12230])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12230) (a := (83698323627917 / 100000000000000 : ℝ)) (b := (84251777189 / 50000000000000 : ℝ)) (q := (1157187431581 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12230])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12230])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12230]

theorem cert12230_12 : CellCertificate 12230 (900305438860391 / 10000000000000000 : ℝ) (34349458879233 / 20000000000000000 : ℝ) (347251867056221 / 10000000000000000 : ℝ)
    (cell12230 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · have h := gap_lower (n := 12230) (a := (41831734222277 / 50000000000000 : ℝ)) (b := (84251777189 / 50000000000000 : ℝ)) (q := (2314378858199 / 100000000000000 : ℝ))
      (E := (cell12230 ⟨12, by decide⟩).energy) (xi := (347251867056221 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12230 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12230]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12230])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12230) (a := (41831734222277 / 50000000000000 : ℝ)) (b := (84251777189 / 50000000000000 : ℝ)) (q := (2314378858199 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12230])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12230])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12230]

theorem cert12230_13 : CellCertificate 12230 (900305438860391 / 10000000000000000 : ℝ) (34349458879233 / 20000000000000000 : ℝ) (347251867056221 / 10000000000000000 : ℝ)
    (cell12230 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · have h := gap_lower (n := 12230) (a := (83628638018671 / 100000000000000 : ℝ)) (b := (84251777189 / 50000000000000 : ℝ)) (q := (578595708927 / 25000000000000 : ℝ))
      (E := (cell12230 ⟨13, by decide⟩).energy) (xi := (347251867056221 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12230 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12230]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12230])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12230) (a := (83628638018671 / 100000000000000 : ℝ)) (b := (84251777189 / 50000000000000 : ℝ)) (q := (578595708927 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12230])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12230])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12230]

theorem cert12230_14 : CellCertificate 12230 (900305438860391 / 10000000000000000 : ℝ) (34349458879233 / 20000000000000000 : ℝ) (347251867056221 / 10000000000000000 : ℝ)
    (cell12230 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · have h := gap_lower (n := 12230) (a := (83593832315363 / 100000000000000 : ℝ)) (b := (84251777189 / 50000000000000 : ℝ)) (q := (2314386860623 / 100000000000000 : ℝ))
      (E := (cell12230 ⟨14, by decide⟩).energy) (xi := (347251867056221 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12230 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12230]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12230])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12230) (a := (83593832315363 / 100000000000000 : ℝ)) (b := (84251777189 / 50000000000000 : ℝ)) (q := (2314386860623 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12230])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12230])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12230]

theorem cert12230_15 : CellCertificate 12230 (900305438860391 / 10000000000000000 : ℝ) (34349458879233 / 20000000000000000 : ℝ) (347251867056221 / 10000000000000000 : ℝ)
    (cell12230 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · have h := gap_lower (n := 12230) (a := (83559051299909 / 100000000000000 : ℝ)) (b := (84251777189 / 50000000000000 : ℝ)) (q := (578597705847 / 25000000000000 : ℝ))
      (E := (cell12230 ⟨15, by decide⟩).energy) (xi := (347251867056221 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12230 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12230]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12230])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12230) (a := (83559051299909 / 100000000000000 : ℝ)) (b := (84251777189 / 50000000000000 : ℝ)) (q := (578597705847 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12230])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12230])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12230]

theorem cert12230_16 : CellCertificate 12230 (900305438860391 / 10000000000000000 : ℝ) (34349458879233 / 20000000000000000 : ℝ) (347251867056221 / 10000000000000000 : ℝ)
    (cell12230 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · have h := gap_lower (n := 12230) (a := (10440536867221 / 12500000000000 : ℝ)) (b := (84251777189 / 50000000000000 : ℝ)) (q := (46287896931 / 2000000000000 : ℝ))
      (E := (cell12230 ⟨16, by decide⟩).energy) (xi := (347251867056221 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12230 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12230]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12230])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12230) (a := (10440536867221 / 12500000000000 : ℝ)) (b := (84251777189 / 50000000000000 : ℝ)) (q := (46287896931 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12230])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12230])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12230]

theorem cert12230_17 : CellCertificate 12230 (900305438860391 / 10000000000000000 : ℝ) (34349458879233 / 20000000000000000 : ℝ) (347251867056221 / 10000000000000000 : ℝ)
    (cell12230 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · have h := gap_lower (n := 12230) (a := (4174478159729 / 5000000000000 : ℝ)) (b := (84251777189 / 50000000000000 : ℝ)) (q := (2314398819967 / 100000000000000 : ℝ))
      (E := (cell12230 ⟨17, by decide⟩).energy) (xi := (347251867056221 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12230 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12230]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12230])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12230) (a := (4174478159729 / 5000000000000 : ℝ)) (b := (84251777189 / 50000000000000 : ℝ)) (q := (2314398819967 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12230])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12230])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12230]

theorem cert12230_18 : CellCertificate 12230 (900305438860391 / 10000000000000000 : ℝ) (34349458879233 / 20000000000000000 : ℝ) (347251867056221 / 10000000000000000 : ℝ)
    (cell12230 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · have h := gap_lower (n := 12230) (a := (41727428018081 / 50000000000000 : ℝ)) (b := (84251777189 / 50000000000000 : ℝ)) (q := (578600701901 / 25000000000000 : ℝ))
      (E := (cell12230 ⟨18, by decide⟩).energy) (xi := (347251867056221 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12230 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12230]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12230])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12230) (a := (41727428018081 / 50000000000000 : ℝ)) (b := (84251777189 / 50000000000000 : ℝ)) (q := (578600701901 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12230])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12230])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12230]

theorem cert12230_19 : CellCertificate 12230 (900305438860391 / 10000000000000000 : ℝ) (34349458879233 / 20000000000000000 : ℝ) (347251867056221 / 10000000000000000 : ℝ)
    (cell12230 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · have h := gap_lower (n := 12230) (a := (83420173428509 / 100000000000000 : ℝ)) (b := (84251777189 / 50000000000000 : ℝ)) (q := (578601703769 / 25000000000000 : ℝ))
      (E := (cell12230 ⟨19, by decide⟩).energy) (xi := (347251867056221 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12230 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12230]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12230])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12230) (a := (83420173428509 / 100000000000000 : ℝ)) (b := (84251777189 / 50000000000000 : ℝ)) (q := (578601703769 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12230])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12230])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12230]

theorem cert12231_0 : CellCertificate 12231 (225068850577927 / 2500000000000000 : ℝ) (214666559544533 / 125000000000000000 : ℝ) (17361135550939 / 500000000000000 : ℝ)
    (cell12231 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · have h := gap_lower (n := 12231) (a := (84083358492227 / 100000000000000 : ℝ)) (b := (168489592031 / 100000000000000 : ℝ)) (q := (1157091004191 / 50000000000000 : ℝ))
      (E := (cell12231 ⟨0, by decide⟩).energy) (xi := (17361135550939 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12231 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12231]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12231])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12231) (a := (84083358492227 / 100000000000000 : ℝ)) (b := (168489592031 / 100000000000000 : ℝ)) (q := (1157091004191 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12231])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12231])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12231]

theorem cert12231_1 : CellCertificate 12231 (225068850577927 / 2500000000000000 : ℝ) (214666559544533 / 125000000000000000 : ℝ) (17361135550939 / 500000000000000 : ℝ)
    (cell12231 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · have h := gap_lower (n := 12231) (a := (84048228958899 / 100000000000000 : ℝ)) (b := (168489592031 / 100000000000000 : ℝ)) (q := (1157092981503 / 50000000000000 : ℝ))
      (E := (cell12231 ⟨1, by decide⟩).energy) (xi := (17361135550939 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12231 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12231]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12231])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12231) (a := (84048228958899 / 100000000000000 : ℝ)) (b := (168489592031 / 100000000000000 : ℝ)) (q := (1157092981503 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12231])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12231])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12231]

theorem cert12231_2 : CellCertificate 12231 (225068850577927 / 2500000000000000 : ℝ) (214666559544533 / 125000000000000000 : ℝ) (17361135550939 / 500000000000000 : ℝ)
    (cell12231 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · have h := gap_lower (n := 12231) (a := (84013124578879 / 100000000000000 : ℝ)) (b := (168489592031 / 100000000000000 : ℝ)) (q := (2314189981661 / 100000000000000 : ℝ))
      (E := (cell12231 ⟨2, by decide⟩).energy) (xi := (17361135550939 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12231 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12231]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12231])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12231) (a := (84013124578879 / 100000000000000 : ℝ)) (b := (168489592031 / 100000000000000 : ℝ)) (q := (2314189981661 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12231])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12231])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12231]

theorem cert12231_3 : CellCertificate 12231 (225068850577927 / 2500000000000000 : ℝ) (214666559544533 / 125000000000000000 : ℝ) (17361135550939 / 500000000000000 : ℝ)
    (cell12231 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · have h := gap_lower (n := 12231) (a := (83978045315179 / 100000000000000 : ℝ)) (b := (168489592031 / 100000000000000 : ℝ)) (q := (1157096979279 / 50000000000000 : ℝ))
      (E := (cell12231 ⟨3, by decide⟩).energy) (xi := (17361135550939 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12231 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12231]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12231])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12231) (a := (83978045315179 / 100000000000000 : ℝ)) (b := (168489592031 / 100000000000000 : ℝ)) (q := (1157096979279 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12231])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12231])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12231]

theorem cert12231_4 : CellCertificate 12231 (225068850577927 / 2500000000000000 : ℝ) (214666559544533 / 125000000000000000 : ℝ) (17361135550939 / 500000000000000 : ℝ)
    (cell12231 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · have h := gap_lower (n := 12231) (a := (83942991131009 / 100000000000000 : ℝ)) (b := (168489592031 / 100000000000000 : ℝ)) (q := (2314197961017 / 100000000000000 : ℝ))
      (E := (cell12231 ⟨4, by decide⟩).energy) (xi := (17361135550939 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12231 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12231]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12231])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12231) (a := (83942991131009 / 100000000000000 : ℝ)) (b := (168489592031 / 100000000000000 : ℝ)) (q := (2314197961017 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12231])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12231])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12231]

theorem cert12231_5 : CellCertificate 12231 (225068850577927 / 2500000000000000 : ℝ) (214666559544533 / 125000000000000000 : ℝ) (17361135550939 / 500000000000000 : ℝ)
    (cell12231 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · have h := gap_lower (n := 12231) (a := (83907961989771 / 100000000000000 : ℝ)) (b := (168489592031 / 100000000000000 : ℝ)) (q := (2314201940439 / 100000000000000 : ℝ))
      (E := (cell12231 ⟨5, by decide⟩).energy) (xi := (17361135550939 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12231 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12231]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12231])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12231) (a := (83907961989771 / 100000000000000 : ℝ)) (b := (168489592031 / 100000000000000 : ℝ)) (q := (2314201940439 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12231])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12231])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12231]

theorem cert12231_6 : CellCertificate 12231 (225068850577927 / 2500000000000000 : ℝ) (214666559544533 / 125000000000000000 : ℝ) (17361135550939 / 500000000000000 : ℝ)
    (cell12231 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · have h := gap_lower (n := 12231) (a := (83872957855063 / 100000000000000 : ℝ)) (b := (168489592031 / 100000000000000 : ℝ)) (q := (231420596367 / 10000000000000 : ℝ))
      (E := (cell12231 ⟨6, by decide⟩).energy) (xi := (17361135550939 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12231 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12231]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12231])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12231) (a := (83872957855063 / 100000000000000 : ℝ)) (b := (168489592031 / 100000000000000 : ℝ)) (q := (231420596367 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12231])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12231])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12231]

theorem cert12231_7 : CellCertificate 12231 (225068850577927 / 2500000000000000 : ℝ) (214666559544533 / 125000000000000000 : ℝ) (17361135550939 / 500000000000000 : ℝ)
    (cell12231 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · have h := gap_lower (n := 12231) (a := (5239873668167 / 6250000000000 : ℝ)) (b := (168489592031 / 100000000000000 : ℝ)) (q := (1157104961811 / 50000000000000 : ℝ))
      (E := (cell12231 ⟨7, by decide⟩).energy) (xi := (17361135550939 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12231 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12231]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12231])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12231) (a := (5239873668167 / 6250000000000 : ℝ)) (b := (168489592031 / 100000000000000 : ℝ)) (q := (1157104961811 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12231])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12231])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12231]

theorem cert12231_8 : CellCertificate 12231 (225068850577927 / 2500000000000000 : ℝ) (214666559544533 / 125000000000000000 : ℝ) (17361135550939 / 500000000000000 : ℝ)
    (cell12231 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · have h := gap_lower (n := 12231) (a := (83803024460577 / 100000000000000 : ℝ)) (b := (168489592031 / 100000000000000 : ℝ)) (q := (289276743069 / 12500000000000 : ℝ))
      (E := (cell12231 ⟨8, by decide⟩).energy) (xi := (17361135550939 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12231 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12231]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12231])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12231) (a := (83803024460577 / 100000000000000 : ℝ)) (b := (168489592031 / 100000000000000 : ℝ)) (q := (289276743069 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12231])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12231])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12231]

theorem cert12231_9 : CellCertificate 12231 (225068850577927 / 2500000000000000 : ℝ) (214666559544533 / 125000000000000000 : ℝ) (17361135550939 / 500000000000000 : ℝ)
    (cell12231 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · have h := gap_lower (n := 12231) (a := (20942023782237 / 25000000000000 : ℝ)) (b := (168489592031 / 100000000000000 : ℝ)) (q := (578554479691 / 25000000000000 : ℝ))
      (E := (cell12231 ⟨9, by decide⟩).energy) (xi := (17361135550939 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12231 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12231]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12231])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12231) (a := (20942023782237 / 25000000000000 : ℝ)) (b := (168489592031 / 100000000000000 : ℝ)) (q := (578554479691 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12231])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12231])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12231]

theorem cert12231_10 : CellCertificate 12231 (225068850577927 / 2500000000000000 : ℝ) (214666559544533 / 125000000000000000 : ℝ) (17361135550939 / 500000000000000 : ℝ)
    (cell12231 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · have h := gap_lower (n := 12231) (a := (83733190660141 / 100000000000000 : ℝ)) (b := (168489592031 / 100000000000000 : ℝ)) (q := (2314221912103 / 100000000000000 : ℝ))
      (E := (cell12231 ⟨10, by decide⟩).energy) (xi := (17361135550939 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12231 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12231]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12231])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12231) (a := (83733190660141 / 100000000000000 : ℝ)) (b := (168489592031 / 100000000000000 : ℝ)) (q := (2314221912103 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12231])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12231])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12231]

theorem cert12231_11 : CellCertificate 12231 (225068850577927 / 2500000000000000 : ℝ) (214666559544533 / 125000000000000000 : ℝ) (17361135550939 / 500000000000000 : ℝ)
    (cell12231 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · have h := gap_lower (n := 12231) (a := (836983110187 / 1000000000000 : ℝ)) (b := (168489592031 / 100000000000000 : ℝ)) (q := (2314225874221 / 100000000000000 : ℝ))
      (E := (cell12231 ⟨11, by decide⟩).energy) (xi := (17361135550939 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12231 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12231]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12231])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12231) (a := (836983110187 / 1000000000000 : ℝ)) (b := (168489592031 / 100000000000000 : ℝ)) (q := (2314225874221 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12231])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12231])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12231]

theorem cert12231_12 : CellCertificate 12231 (225068850577927 / 2500000000000000 : ℝ) (214666559544533 / 125000000000000000 : ℝ) (17361135550939 / 500000000000000 : ℝ)
    (cell12231 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · have h := gap_lower (n := 12231) (a := (83663456169353 / 100000000000000 : ℝ)) (b := (168489592031 / 100000000000000 : ℝ)) (q := (2314229870503 / 100000000000000 : ℝ))
      (E := (cell12231 ⟨12, by decide⟩).energy) (xi := (17361135550939 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12231 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12231]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12231])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12231) (a := (83663456169353 / 100000000000000 : ℝ)) (b := (168489592031 / 100000000000000 : ℝ)) (q := (2314229870503 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12231])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12231])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12231]

theorem cert12231_13 : CellCertificate 12231 (225068850577927 / 2500000000000000 : ℝ) (214666559544533 / 125000000000000000 : ℝ) (17361135550939 / 500000000000000 : ℝ)
    (cell12231 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · have h := gap_lower (n := 12231) (a := (16725725215403 / 20000000000000 : ℝ)) (b := (168489592031 / 100000000000000 : ℝ)) (q := (46284677001 / 2000000000000 : ℝ))
      (E := (cell12231 ⟨13, by decide⟩).energy) (xi := (17361135550939 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12231 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12231]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12231])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12231) (a := (16725725215403 / 20000000000000 : ℝ)) (b := (168489592031 / 100000000000000 : ℝ)) (q := (46284677001 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12231])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12231])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12231]

theorem cert12231_14 : CellCertificate 12231 (225068850577927 / 2500000000000000 : ℝ) (214666559544533 / 125000000000000000 : ℝ) (17361135550939 / 500000000000000 : ℝ)
    (cell12231 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · have h := gap_lower (n := 12231) (a := (83593820706783 / 100000000000000 : ℝ)) (b := (168489592031 / 100000000000000 : ℝ)) (q := (1157118938897 / 50000000000000 : ℝ))
      (E := (cell12231 ⟨14, by decide⟩).energy) (xi := (17361135550939 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12231 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12231]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12231])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12231) (a := (83593820706783 / 100000000000000 : ℝ)) (b := (168489592031 / 100000000000000 : ℝ)) (q := (1157118938897 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12231])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12231])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12231]

theorem cert12231_15 : CellCertificate 12231 (225068850577927 / 2500000000000000 : ℝ) (214666559544533 / 125000000000000000 : ℝ) (17361135550939 / 500000000000000 : ℝ)
    (cell12231 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · have h := gap_lower (n := 12231) (a := (83559040023937 / 100000000000000 : ℝ)) (b := (168489592031 / 100000000000000 : ℝ)) (q := (1157120922089 / 50000000000000 : ℝ))
      (E := (cell12231 ⟨15, by decide⟩).energy) (xi := (17361135550939 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12231 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12231]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12231])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12231) (a := (83559040023937 / 100000000000000 : ℝ)) (b := (168489592031 / 100000000000000 : ℝ)) (q := (1157120922089 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12231])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12231])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12231]

theorem cert12231_16 : CellCertificate 12231 (225068850577927 / 2500000000000000 : ℝ) (214666559544533 / 125000000000000000 : ℝ) (17361135550939 / 500000000000000 : ℝ)
    (cell12231 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · have h := gap_lower (n := 12231) (a := (5220267749621 / 6250000000000 : ℝ)) (b := (168489592031 / 100000000000000 : ℝ)) (q := (2314245871749 / 100000000000000 : ℝ))
      (E := (cell12231 ⟨16, by decide⟩).energy) (xi := (17361135550939 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12231 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12231]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12231])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12231) (a := (5220267749621 / 6250000000000 : ℝ)) (b := (168489592031 / 100000000000000 : ℝ)) (q := (2314245871749 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12231])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12231])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12231]

theorem cert12231_17 : CellCertificate 12231 (225068850577927 / 2500000000000000 : ℝ) (214666559544533 / 125000000000000000 : ℝ) (17361135550939 / 500000000000000 : ℝ)
    (cell12231 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · have h := gap_lower (n := 12231) (a := (83489552582421 / 100000000000000 : ℝ)) (b := (168489592031 / 100000000000000 : ℝ)) (q := (1157124925181 / 50000000000000 : ℝ))
      (E := (cell12231 ⟨17, by decide⟩).energy) (xi := (17361135550939 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12231 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12231]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12231])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12231) (a := (83489552582421 / 100000000000000 : ℝ)) (b := (168489592031 / 100000000000000 : ℝ)) (q := (1157124925181 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12231])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12231])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12231]

theorem cert12231_18 : CellCertificate 12231 (225068850577927 / 2500000000000000 : ℝ) (214666559544533 / 125000000000000000 : ℝ) (17361135550939 / 500000000000000 : ℝ)
    (cell12231 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · have h := gap_lower (n := 12231) (a := (83454845755211 / 100000000000000 : ℝ)) (b := (168489592031 / 100000000000000 : ℝ)) (q := (144640865249 / 6250000000000 : ℝ))
      (E := (cell12231 ⟨18, by decide⟩).energy) (xi := (17361135550939 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12231 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12231]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12231])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12231) (a := (83454845755211 / 100000000000000 : ℝ)) (b := (168489592031 / 100000000000000 : ℝ)) (q := (144640865249 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12231])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12231])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12231]

theorem cert12231_19 : CellCertificate 12231 (225068850577927 / 2500000000000000 : ℝ) (214666559544533 / 125000000000000000 : ℝ) (17361135550939 / 500000000000000 : ℝ)
    (cell12231 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · have h := gap_lower (n := 12231) (a := (41710081739151 / 50000000000000 : ℝ)) (b := (168489592031 / 100000000000000 : ℝ)) (q := (2314257800021 / 100000000000000 : ℝ))
      (E := (cell12231 ⟨19, by decide⟩).energy) (xi := (17361135550939 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12231 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12231]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12231])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12231) (a := (41710081739151 / 50000000000000 : ℝ)) (b := (168489592031 / 100000000000000 : ℝ)) (q := (2314257800021 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12231])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12231])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12231]

theorem cert12232_0 : CellCertificate 12232 (450122685248117 / 5000000000000000 : ℝ) (13415562747859 / 7812500000000000 : ℝ) (347193560006361 / 10000000000000000 : ℝ)
    (cell12232 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · have h := gap_lower (n := 12232) (a := (84083342180161 / 100000000000000 : ℝ)) (b := (16847563203 / 10000000000000 : ℝ)) (q := (92561324427 / 4000000000000 : ℝ))
      (E := (cell12232 ⟨0, by decide⟩).energy) (xi := (347193560006361 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12232 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12232]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12232])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12232) (a := (84083342180161 / 100000000000000 : ℝ)) (b := (16847563203 / 10000000000000 : ℝ)) (q := (92561324427 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12232])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12232])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12232]

theorem cert12232_1 : CellCertificate 12232 (450122685248117 / 5000000000000000 : ℝ) (13415562747859 / 7812500000000000 : ℝ) (347193560006361 / 10000000000000000 : ℝ)
    (cell12232 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · have h := gap_lower (n := 12232) (a := (84048212986049 / 100000000000000 : ℝ)) (b := (16847563203 / 10000000000000 : ℝ)) (q := (72313659863 / 3125000000000 : ℝ))
      (E := (cell12232 ⟨1, by decide⟩).energy) (xi := (347193560006361 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12232 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12232]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12232])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12232) (a := (84048212986049 / 100000000000000 : ℝ)) (b := (16847563203 / 10000000000000 : ℝ)) (q := (72313659863 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12232])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12232])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12232]

theorem cert12232_2 : CellCertificate 12232 (450122685248117 / 5000000000000000 : ℝ) (13415562747859 / 7812500000000000 : ℝ) (347193560006361 / 10000000000000000 : ℝ)
    (cell12232 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · have h := gap_lower (n := 12232) (a := (84013108944763 / 100000000000000 : ℝ)) (b := (16847563203 / 10000000000000 : ℝ)) (q := (92561642793 / 4000000000000 : ℝ))
      (E := (cell12232 ⟨2, by decide⟩).energy) (xi := (347193560006361 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12232 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12232]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12232])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12232) (a := (84013108944763 / 100000000000000 : ℝ)) (b := (16847563203 / 10000000000000 : ℝ)) (q := (92561642793 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12232])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12232])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12232]

theorem cert12232_3 : CellCertificate 12232 (450122685248117 / 5000000000000000 : ℝ) (13415562747859 / 7812500000000000 : ℝ) (347193560006361 / 10000000000000000 : ℝ)
    (cell12232 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · have h := gap_lower (n := 12232) (a := (83978030019317 / 100000000000000 : ℝ)) (b := (16847563203 / 10000000000000 : ℝ)) (q := (2314045040861 / 100000000000000 : ℝ))
      (E := (cell12232 ⟨3, by decide⟩).energy) (xi := (347193560006361 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12232 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12232]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12232])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12232) (a := (83978030019317 / 100000000000000 : ℝ)) (b := (16847563203 / 10000000000000 : ℝ)) (q := (2314045040861 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12232])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12232])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12232]

theorem cert12232_4 : CellCertificate 12232 (450122685248117 / 5000000000000000 : ℝ) (13415562747859 / 7812500000000000 : ℝ) (347193560006361 / 10000000000000000 : ℝ)
    (cell12232 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · have h := gap_lower (n := 12232) (a := (83942976172921 / 100000000000000 : ℝ)) (b := (16847563203 / 10000000000000 : ℝ)) (q := (115702451913 / 5000000000000 : ℝ))
      (E := (cell12232 ⟨4, by decide⟩).energy) (xi := (347193560006361 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12232 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12232]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12232])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12232) (a := (83942976172921 / 100000000000000 : ℝ)) (b := (16847563203 / 10000000000000 : ℝ)) (q := (115702451913 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12232])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12232])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12232]

theorem cert12232_5 : CellCertificate 12232 (450122685248117 / 5000000000000000 : ℝ) (13415562747859 / 7812500000000000 : ℝ) (347193560006361 / 10000000000000000 : ℝ)
    (cell12232 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · have h := gap_lower (n := 12232) (a := (41953973684489 / 50000000000000 : ℝ)) (b := (16847563203 / 10000000000000 : ℝ)) (q := (2314053071299 / 100000000000000 : ℝ))
      (E := (cell12232 ⟨5, by decide⟩).energy) (xi := (347193560006361 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12232 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12232]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12232])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12232) (a := (41953973684489 / 50000000000000 : ℝ)) (b := (16847563203 / 10000000000000 : ℝ)) (q := (2314053071299 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12232])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12232])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12232]

theorem cert12232_6 : CellCertificate 12232 (450122685248117 / 5000000000000000 : ℝ) (13415562747859 / 7812500000000000 : ℝ) (347193560006361 / 10000000000000000 : ℝ)
    (cell12232 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · have h := gap_lower (n := 12232) (a := (83872943571087 / 100000000000000 : ℝ)) (b := (16847563203 / 10000000000000 : ℝ)) (q := (2314057033193 / 100000000000000 : ℝ))
      (E := (cell12232 ⟨6, by decide⟩).energy) (xi := (347193560006361 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12232 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12232]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12232])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12232) (a := (83872943571087 / 100000000000000 : ℝ)) (b := (16847563203 / 10000000000000 : ℝ)) (q := (2314057033193 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12232])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12232])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12232]

theorem cert12232_7 : CellCertificate 12232 (450122685248117 / 5000000000000000 : ℝ) (13415562747859 / 7812500000000000 : ℝ) (347193560006361 / 10000000000000000 : ℝ)
    (cell12232 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · have h := gap_lower (n := 12232) (a := (83837964743037 / 100000000000000 : ℝ)) (b := (16847563203 / 10000000000000 : ℝ)) (q := (2314061048407 / 100000000000000 : ℝ))
      (E := (cell12232 ⟨7, by decide⟩).energy) (xi := (347193560006361 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12232 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12232]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12232])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12232) (a := (83837964743037 / 100000000000000 : ℝ)) (b := (16847563203 / 10000000000000 : ℝ)) (q := (2314061048407 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12232])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12232])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12232]

theorem cert12232_8 : CellCertificate 12232 (450122685248117 / 5000000000000000 : ℝ) (13415562747859 / 7812500000000000 : ℝ) (347193560006361 / 10000000000000000 : ℝ)
    (cell12232 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · have h := gap_lower (n := 12232) (a := (83803010848809 / 100000000000000 : ℝ)) (b := (16847563203 / 10000000000000 : ℝ)) (q := (1157032504773 / 50000000000000 : ℝ))
      (E := (cell12232 ⟨8, by decide⟩).energy) (xi := (347193560006361 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12232 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12232]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12232])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12232) (a := (83803010848809 / 100000000000000 : ℝ)) (b := (16847563203 / 10000000000000 : ℝ)) (q := (1157032504773 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12232])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12232])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12232]

theorem cert12232_9 : CellCertificate 12232 (450122685248117 / 5000000000000000 : ℝ) (13415562747859 / 7812500000000000 : ℝ) (347193560006361 / 10000000000000000 : ℝ)
    (cell12232 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · have h := gap_lower (n := 12232) (a := (83768081852571 / 100000000000000 : ℝ)) (b := (16847563203 / 10000000000000 : ℝ)) (q := (2314069040659 / 100000000000000 : ℝ))
      (E := (cell12232 ⟨9, by decide⟩).energy) (xi := (347193560006361 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12232 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12232]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12232])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12232) (a := (83768081852571 / 100000000000000 : ℝ)) (b := (16847563203 / 10000000000000 : ℝ)) (q := (2314069040659 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12232])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12232])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12232]

theorem cert12232_10 : CellCertificate 12232 (450122685248117 / 5000000000000000 : ℝ) (13415562747859 / 7812500000000000 : ℝ) (347193560006361 / 10000000000000000 : ℝ)
    (cell12232 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · have h := gap_lower (n := 12232) (a := (83733177718681 / 100000000000000 : ℝ)) (b := (16847563203 / 10000000000000 : ℝ)) (q := (578518258437 / 25000000000000 : ℝ))
      (E := (cell12232 ⟨10, by decide⟩).energy) (xi := (347193560006361 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12232 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12232]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12232])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12232) (a := (83733177718681 / 100000000000000 : ℝ)) (b := (16847563203 / 10000000000000 : ℝ)) (q := (578518258437 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12232])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12232])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12232]

theorem cert12232_11 : CellCertificate 12232 (450122685248117 / 5000000000000000 : ℝ) (13415562747859 / 7812500000000000 : ℝ) (347193560006361 / 10000000000000000 : ℝ)
    (cell12232 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · have h := gap_lower (n := 12232) (a := (16739659682337 / 20000000000000 : ℝ)) (b := (16847563203 / 10000000000000 : ℝ)) (q := (289259624551 / 12500000000000 : ℝ))
      (E := (cell12232 ⟨11, by decide⟩).energy) (xi := (347193560006361 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12232 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12232]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12232])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12232) (a := (16739659682337 / 20000000000000 : ℝ)) (b := (16847563203 / 10000000000000 : ℝ)) (q := (289259624551 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12232])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12232])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12232]

theorem cert12232_12 : CellCertificate 12232 (450122685248117 / 5000000000000000 : ℝ) (13415562747859 / 7812500000000000 : ℝ) (347193560006361 / 10000000000000000 : ℝ)
    (cell12232 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · have h := gap_lower (n := 12232) (a := (10457930487039 / 12500000000000 : ℝ)) (b := (16847563203 / 10000000000000 : ℝ)) (q := (1157040497013 / 50000000000000 : ℝ))
      (E := (cell12232 ⟨12, by decide⟩).energy) (xi := (347193560006361 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12232 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12232]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12232])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12232) (a := (10457930487039 / 12500000000000 : ℝ)) (b := (16847563203 / 10000000000000 : ℝ)) (q := (1157040497013 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12232])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12232])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12232]

theorem cert12232_13 : CellCertificate 12232 (450122685248117 / 5000000000000000 : ℝ) (13415562747859 / 7812500000000000 : ℝ) (347193560006361 / 10000000000000000 : ℝ)
    (cell12232 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · have h := gap_lower (n := 12232) (a := (41814307068739 / 50000000000000 : ℝ)) (b := (16847563203 / 10000000000000 : ℝ)) (q := (2314084975701 / 100000000000000 : ℝ))
      (E := (cell12232 ⟨13, by decide⟩).energy) (xi := (347193560006361 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12232 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12232]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12232])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12232) (a := (41814307068739 / 50000000000000 : ℝ)) (b := (16847563203 / 10000000000000 : ℝ)) (q := (2314084975701 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12232])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12232])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12232]

theorem cert12232_14 : CellCertificate 12232 (450122685248117 / 5000000000000000 : ℝ) (13415562747859 / 7812500000000000 : ℝ) (347193560006361 / 10000000000000000 : ℝ)
    (cell12232 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · have h := gap_lower (n := 12232) (a := (2089845227507 / 2500000000000 : ℝ)) (b := (16847563203 / 10000000000000 : ℝ)) (q := (578522237069 / 25000000000000 : ℝ))
      (E := (cell12232 ⟨14, by decide⟩).energy) (xi := (347193560006361 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12232 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12232]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12232])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12232) (a := (2089845227507 / 2500000000000 : ℝ)) (b := (16847563203 / 10000000000000 : ℝ)) (q := (578522237069 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12232])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12232])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12232]

theorem cert12232_15 : CellCertificate 12232 (450122685248117 / 5000000000000000 : ℝ) (13415562747859 / 7812500000000000 : ℝ) (347193560006361 / 10000000000000000 : ℝ)
    (cell12232 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · have h := gap_lower (n := 12232) (a := (83559028749999 / 100000000000000 : ℝ)) (b := (16847563203 / 10000000000000 : ℝ)) (q := (1157046488229 / 50000000000000 : ℝ))
      (E := (cell12232 ⟨15, by decide⟩).energy) (xi := (347193560006361 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12232 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12232]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12232])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12232) (a := (83559028749999 / 100000000000000 : ℝ)) (b := (16847563203 / 10000000000000 : ℝ)) (q := (1157046488229 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12232])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12232])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12232]

theorem cert12232_16 : CellCertificate 12232 (450122685248117 / 5000000000000000 : ℝ) (13415562747859 / 7812500000000000 : ℝ) (347193560006361 / 10000000000000000 : ℝ)
    (cell12232 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · have h := gap_lower (n := 12232) (a := (83524273052097 / 100000000000000 : ℝ)) (b := (16847563203 / 10000000000000 : ℝ)) (q := (289262118799 / 12500000000000 : ℝ))
      (E := (cell12232 ⟨16, by decide⟩).energy) (xi := (347193560006361 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12232 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12232]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12232])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12232) (a := (83524273052097 / 100000000000000 : ℝ)) (b := (16847563203 / 10000000000000 : ℝ)) (q := (289262118799 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12232])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12232])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12232]

theorem cert12232_17 : CellCertificate 12232 (450122685248117 / 5000000000000000 : ℝ) (13415562747859 / 7812500000000000 : ℝ) (347193560006361 / 10000000000000000 : ℝ)
    (cell12232 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · have h := gap_lower (n := 12232) (a := (83489541972213 / 100000000000000 : ℝ)) (b := (16847563203 / 10000000000000 : ℝ)) (q := (2314100934269 / 100000000000000 : ℝ))
      (E := (cell12232 ⟨17, by decide⟩).energy) (xi := (347193560006361 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12232 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12232]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12232])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12232) (a := (83489541972213 / 100000000000000 : ℝ)) (b := (16847563203 / 10000000000000 : ℝ)) (q := (2314100934269 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12232])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12232])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12232]

theorem cert12232_18 : CellCertificate 12232 (450122685248117 / 5000000000000000 : ℝ) (13415562747859 / 7812500000000000 : ℝ) (347193560006361 / 10000000000000000 : ℝ)
    (cell12232 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · have h := gap_lower (n := 12232) (a := (83454835476169 / 100000000000000 : ℝ)) (b := (16847563203 / 10000000000000 : ℝ)) (q := (2314104933941 / 100000000000000 : ℝ))
      (E := (cell12232 ⟨18, by decide⟩).energy) (xi := (347193560006361 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12232 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12232]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12232])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12232) (a := (83454835476169 / 100000000000000 : ℝ)) (b := (16847563203 / 10000000000000 : ℝ)) (q := (2314104933941 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12232])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12232])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12232]

theorem cert12232_19 : CellCertificate 12232 (450122685248117 / 5000000000000000 : ℝ) (13415562747859 / 7812500000000000 : ℝ) (347193560006361 / 10000000000000000 : ℝ)
    (cell12232 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · have h := gap_lower (n := 12232) (a := (83420153529961 / 100000000000000 : ℝ)) (b := (16847563203 / 10000000000000 : ℝ)) (q := (2314108955021 / 100000000000000 : ℝ))
      (E := (cell12232 ⟨19, by decide⟩).energy) (xi := (347193560006361 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12232 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12232]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12232])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12232) (a := (83420153529961 / 100000000000000 : ℝ)) (b := (16847563203 / 10000000000000 : ℝ)) (q := (2314108955021 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12232])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12232])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12232]

theorem cert12233_0 : CellCertificate 12233 (900215343412797 / 10000000000000000 : ℝ) (68682064402603 / 40000000000000000 : ℝ) (86791103504371 / 2500000000000000 : ℝ)
    (cell12233 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · have h := gap_lower (n := 12233) (a := (16816665174153 / 20000000000000 : ℝ)) (b := (84230837187 / 50000000000000 : ℝ)) (q := (1156942132671 / 50000000000000 : ℝ))
      (E := (cell12233 ⟨0, by decide⟩).energy) (xi := (86791103504371 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12233 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12233]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12233])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12233) (a := (16816665174153 / 20000000000000 : ℝ)) (b := (84230837187 / 50000000000000 : ℝ)) (q := (1156942132671 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12233])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12233])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12233]

theorem cert12233_1 : CellCertificate 12233 (900215343412797 / 10000000000000000 : ℝ) (68682064402603 / 40000000000000000 : ℝ) (86791103504371 / 2500000000000000 : ℝ)
    (cell12233 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · have h := gap_lower (n := 12233) (a := (84048197015827 / 100000000000000 : ℝ)) (b := (84230837187 / 50000000000000 : ℝ)) (q := (2313888262883 / 100000000000000 : ℝ))
      (E := (cell12233 ⟨1, by decide⟩).energy) (xi := (86791103504371 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12233 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12233]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12233])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12233) (a := (84048197015827 / 100000000000000 : ℝ)) (b := (84230837187 / 50000000000000 : ℝ)) (q := (2313888262883 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12233])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12233])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12233]

theorem cert12233_2 : CellCertificate 12233 (900215343412797 / 10000000000000000 : ℝ) (68682064402603 / 40000000000000000 : ℝ) (86791103504371 / 2500000000000000 : ℝ)
    (cell12233 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · have h := gap_lower (n := 12233) (a := (5250818332077 / 6250000000000 : ℝ)) (b := (84230837187 / 50000000000000 : ℝ)) (q := (144618266769 / 6250000000000 : ℝ))
      (E := (cell12233 ⟨2, by decide⟩).energy) (xi := (86791103504371 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12233 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12233]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12233])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12233) (a := (5250818332077 / 6250000000000 : ℝ)) (b := (84230837187 / 50000000000000 : ℝ)) (q := (144618266769 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12233])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12233])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12233]

theorem cert12233_3 : CellCertificate 12233 (900215343412797 / 10000000000000000 : ℝ) (68682064402603 / 40000000000000000 : ℝ) (86791103504371 / 2500000000000000 : ℝ)
    (cell12233 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · have h := gap_lower (n := 12233) (a := (83978014725997 / 100000000000000 : ℝ)) (b := (84230837187 / 50000000000000 : ℝ)) (q := (11569481457 / 500000000000 : ℝ))
      (E := (cell12233 ⟨3, by decide⟩).energy) (xi := (86791103504371 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12233 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12233]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12233])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12233) (a := (83978014725997 / 100000000000000 : ℝ)) (b := (84230837187 / 50000000000000 : ℝ)) (q := (11569481457 / 500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12233])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12233])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12233]

theorem cert12233_4 : CellCertificate 12233 (900215343412797 / 10000000000000000 : ℝ) (68682064402603 / 40000000000000000 : ℝ) (86791103504371 / 2500000000000000 : ℝ)
    (cell12233 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · have h := gap_lower (n := 12233) (a := (83942961217331 / 100000000000000 : ℝ)) (b := (84230837187 / 50000000000000 : ℝ)) (q := (2313900226001 / 100000000000000 : ℝ))
      (E := (cell12233 ⟨4, by decide⟩).energy) (xi := (86791103504371 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12233 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12233]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12233])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12233) (a := (83942961217331 / 100000000000000 : ℝ)) (b := (84230837187 / 50000000000000 : ℝ)) (q := (2313900226001 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12233])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12233])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12233]

theorem cert12233_5 : CellCertificate 12233 (900215343412797 / 10000000000000000 : ℝ) (68682064402603 / 40000000000000000 : ℝ) (86791103504371 / 2500000000000000 : ℝ)
    (cell12233 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · have h := gap_lower (n := 12233) (a := (83907932750641 / 100000000000000 : ℝ)) (b := (84230837187 / 50000000000000 : ℝ)) (q := (2313904254871 / 100000000000000 : ℝ))
      (E := (cell12233 ⟨5, by decide⟩).energy) (xi := (86791103504371 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12233 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12233]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12233])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12233) (a := (83907932750641 / 100000000000000 : ℝ)) (b := (84230837187 / 50000000000000 : ℝ)) (q := (2313904254871 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12233])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12233])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12233]

theorem cert12233_6 : CellCertificate 12233 (900215343412797 / 10000000000000000 : ℝ) (68682064402603 / 40000000000000000 : ℝ) (86791103504371 / 2500000000000000 : ℝ)
    (cell12233 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · have h := gap_lower (n := 12233) (a := (41936464644763 / 50000000000000 : ℝ)) (b := (84230837187 / 50000000000000 : ℝ)) (q := (1156954106697 / 50000000000000 : ℝ))
      (E := (cell12233 ⟨6, by decide⟩).energy) (xi := (86791103504371 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12233 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12233]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12233])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12233) (a := (41936464644763 / 50000000000000 : ℝ)) (b := (84230837187 / 50000000000000 : ℝ)) (q := (1156954106697 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12233])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12233])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12233]

theorem cert12233_7 : CellCertificate 12233 (900215343412797 / 10000000000000000 : ℝ) (68682064402603 / 40000000000000000 : ℝ) (86791103504371 / 2500000000000000 : ℝ)
    (cell12233 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · have h := gap_lower (n := 12233) (a := (41918975398887 / 50000000000000 : ℝ)) (b := (84230837187 / 50000000000000 : ℝ)) (q := (578478056509 / 25000000000000 : ℝ))
      (E := (cell12233 ⟨7, by decide⟩).energy) (xi := (86791103504371 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12233 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12233]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12233])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12233) (a := (41918975398887 / 50000000000000 : ℝ)) (b := (84230837187 / 50000000000000 : ℝ)) (q := (578478056509 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12233])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12233])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12233]

theorem cert12233_8 : CellCertificate 12233 (900215343412797 / 10000000000000000 : ℝ) (68682064402603 / 40000000000000000 : ℝ) (86791103504371 / 2500000000000000 : ℝ)
    (cell12233 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · have h := gap_lower (n := 12233) (a := (83802997239369 / 100000000000000 : ℝ)) (b := (84230837187 / 50000000000000 : ℝ)) (q := (578479060837 / 25000000000000 : ℝ))
      (E := (cell12233 ⟨8, by decide⟩).energy) (xi := (86791103504371 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12233 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12233]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12233])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12233) (a := (83802997239369 / 100000000000000 : ℝ)) (b := (84230837187 / 50000000000000 : ℝ)) (q := (578479060837 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12233])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12233])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12233]

theorem cert12233_9 : CellCertificate 12233 (900215343412797 / 10000000000000000 : ℝ) (68682064402603 / 40000000000000000 : ℝ) (86791103504371 / 2500000000000000 : ℝ)
    (cell12233 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · have h := gap_lower (n := 12233) (a := (1047100857231 / 1250000000000 : ℝ)) (b := (84230837187 / 50000000000000 : ℝ)) (q := (1156960107767 / 50000000000000 : ℝ))
      (E := (cell12233 ⟨9, by decide⟩).energy) (xi := (86791103504371 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12233 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12233]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12233])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12233) (a := (1047100857231 / 1250000000000 : ℝ)) (b := (84230837187 / 50000000000000 : ℝ)) (q := (1156960107767 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12233])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12233])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12233]

theorem cert12233_10 : CellCertificate 12233 (900215343412797 / 10000000000000000 : ℝ) (68682064402603 / 40000000000000000 : ℝ) (86791103504371 / 2500000000000000 : ℝ)
    (cell12233 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · have h := gap_lower (n := 12233) (a := (41866582389733 / 50000000000000 : ℝ)) (b := (84230837187 / 50000000000000 : ℝ)) (q := (2313924208439 / 100000000000000 : ℝ))
      (E := (cell12233 ⟨10, by decide⟩).energy) (xi := (86791103504371 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12233 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12233]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12233])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12233) (a := (41866582389733 / 50000000000000 : ℝ)) (b := (84230837187 / 50000000000000 : ℝ)) (q := (2313924208439 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12233])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12233])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12233]

theorem cert12233_11 : CellCertificate 12233 (900215343412797 / 10000000000000000 : ℝ) (68682064402603 / 40000000000000000 : ℝ) (86791103504371 / 2500000000000000 : ℝ)
    (cell12233 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · have h := gap_lower (n := 12233) (a := (83698285806873 / 100000000000000 : ℝ)) (b := (84230837187 / 50000000000000 : ℝ)) (q := (578482042927 / 25000000000000 : ℝ))
      (E := (cell12233 ⟨11, by decide⟩).energy) (xi := (86791103504371 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12233 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12233]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12233])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12233) (a := (83698285806873 / 100000000000000 : ℝ)) (b := (84230837187 / 50000000000000 : ℝ)) (q := (578482042927 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12233])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12233])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12233]

theorem cert12233_12 : CellCertificate 12233 (900215343412797 / 10000000000000000 : ℝ) (68682064402603 / 40000000000000000 : ℝ) (86791103504371 / 2500000000000000 : ℝ)
    (cell12233 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · have h := gap_lower (n := 12233) (a := (10457928953179 / 12500000000000 : ℝ)) (b := (84230837187 / 50000000000000 : ℝ)) (q := (2313932170729 / 100000000000000 : ℝ))
      (E := (cell12233 ⟨12, by decide⟩).energy) (xi := (86791103504371 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12233 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12233]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12233])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12233) (a := (10457928953179 / 12500000000000 : ℝ)) (b := (84230837187 / 50000000000000 : ℝ)) (q := (2313932170729 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12233])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12233])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12233]

theorem cert12233_13 : CellCertificate 12233 (900215343412797 / 10000000000000000 : ℝ) (68682064402603 / 40000000000000000 : ℝ) (86791103504371 / 2500000000000000 : ℝ)
    (cell12233 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · have h := gap_lower (n := 12233) (a := (83628602200059 / 100000000000000 : ℝ)) (b := (84230837187 / 50000000000000 : ℝ)) (q := (2313936154599 / 100000000000000 : ℝ))
      (E := (cell12233 ⟨13, by decide⟩).energy) (xi := (86791103504371 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12233 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12233]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12233])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12233) (a := (83628602200059 / 100000000000000 : ℝ)) (b := (84230837187 / 50000000000000 : ℝ)) (q := (2313936154599 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12233])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12233])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12233]

theorem cert12233_14 : CellCertificate 12233 (900215343412797 / 10000000000000000 : ℝ) (68682064402603 / 40000000000000000 : ℝ) (86791103504371 / 2500000000000000 : ℝ)
    (cell12233 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · have h := gap_lower (n := 12233) (a := (83593797495853 / 100000000000000 : ℝ)) (b := (84230837187 / 50000000000000 : ℝ)) (q := (289242523531 / 12500000000000 : ℝ))
      (E := (cell12233 ⟨14, by decide⟩).energy) (xi := (86791103504371 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12233 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12233]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12233])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12233) (a := (83593797495853 / 100000000000000 : ℝ)) (b := (84230837187 / 50000000000000 : ℝ)) (q := (289242523531 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12233])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12233])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12233]

theorem cert12233_15 : CellCertificate 12233 (900215343412797 / 10000000000000000 : ℝ) (68682064402603 / 40000000000000000 : ℝ) (86791103504371 / 2500000000000000 : ℝ)
    (cell12233 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · have h := gap_lower (n := 12233) (a := (5222438592381 / 6250000000000 : ℝ)) (b := (84230837187 / 50000000000000 : ℝ)) (q := (2313944162117 / 100000000000000 : ℝ))
      (E := (cell12233 ⟨15, by decide⟩).energy) (xi := (86791103504371 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12233 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12233]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12233])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12233) (a := (5222438592381 / 6250000000000 : ℝ)) (b := (84230837187 / 50000000000000 : ℝ)) (q := (2313944162117 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12233])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12233])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12233]

theorem cert12233_16 : CellCertificate 12233 (900215343412797 / 10000000000000000 : ℝ) (68682064402603 / 40000000000000000 : ℝ) (86791103504371 / 2500000000000000 : ℝ)
    (cell12233 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · have h := gap_lower (n := 12233) (a := (83524262112249 / 100000000000000 : ℝ)) (b := (84230837187 / 50000000000000 : ℝ)) (q := (2313948140617 / 100000000000000 : ℝ))
      (E := (cell12233 ⟨16, by decide⟩).energy) (xi := (86791103504371 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12233 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12233]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12233])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12233) (a := (83524262112249 / 100000000000000 : ℝ)) (b := (84230837187 / 50000000000000 : ℝ)) (q := (2313948140617 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12233])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12233])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12233]

theorem cert12233_17 : CellCertificate 12233 (900215343412797 / 10000000000000000 : ℝ) (68682064402603 / 40000000000000000 : ℝ) (86791103504371 / 2500000000000000 : ℝ)
    (cell12233 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · have h := gap_lower (n := 12233) (a := (20872382840989 / 25000000000000 : ℝ)) (b := (84230837187 / 50000000000000 : ℝ)) (q := (1156976064923 / 50000000000000 : ℝ))
      (E := (cell12233 ⟨17, by decide⟩).energy) (xi := (86791103504371 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12233 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12233]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12233])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12233) (a := (20872382840989 / 25000000000000 : ℝ)) (b := (84230837187 / 50000000000000 : ℝ)) (q := (1156976064923 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12233])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12233])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12233]

theorem cert12233_18 : CellCertificate 12233 (900215343412797 / 10000000000000000 : ℝ) (68682064402603 / 40000000000000000 : ℝ) (86791103504371 / 2500000000000000 : ℝ)
    (cell12233 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · have h := gap_lower (n := 12233) (a := (20863706299759 / 25000000000000 : ℝ)) (b := (84230837187 / 50000000000000 : ℝ)) (q := (115697806783 / 5000000000000 : ℝ))
      (E := (cell12233 ⟨18, by decide⟩).energy) (xi := (86791103504371 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12233 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12233]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12233])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12233) (a := (20863706299759 / 25000000000000 : ℝ)) (b := (84230837187 / 50000000000000 : ℝ)) (q := (115697806783 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12233])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12233])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12233]

theorem cert12233_19 : CellCertificate 12233 (900215343412797 / 10000000000000000 : ℝ) (68682064402603 / 40000000000000000 : ℝ) (86791103504371 / 2500000000000000 : ℝ)
    (cell12233 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · have h := gap_lower (n := 12233) (a := (325859935873 / 390625000000 : ℝ)) (b := (84230837187 / 50000000000000 : ℝ)) (q := (2313960105461 / 100000000000000 : ℝ))
      (E := (cell12233 ⟨19, by decide⟩).energy) (xi := (86791103504371 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12233 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12233]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12233])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12233) (a := (325859935873 / 390625000000 : ℝ)) (b := (84230837187 / 50000000000000 : ℝ)) (q := (2313960105461 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12233])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12233])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12233]

theorem cert12234_0 : CellCertificate 12234 (900185321060227 / 10000000000000000 : ℝ) (1716911211367999 / 1000000000000000000 : ℝ) (347135273050673 / 10000000000000000 : ℝ)
    (cell12234 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · have h := gap_lower (n := 12234) (a := (84083309564039 / 100000000000000 : ℝ)) (b := (168447719061 / 100000000000000 : ℝ)) (q := (36152118561 / 1562500000000 : ℝ))
      (E := (cell12234 ⟨0, by decide⟩).energy) (xi := (347135273050673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12234 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12234]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12234])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12234) (a := (84083309564039 / 100000000000000 : ℝ)) (b := (168447719061 / 100000000000000 : ℝ)) (q := (36152118561 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12234])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12234])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12234]

theorem cert12234_1 : CellCertificate 12234 (900185321060227 / 10000000000000000 : ℝ) (1716911211367999 / 1000000000000000000 : ℝ) (347135273050673 / 10000000000000000 : ℝ)
    (cell12234 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · have h := gap_lower (n := 12234) (a := (84048181048231 / 100000000000000 : ℝ)) (b := (168447719061 / 100000000000000 : ℝ)) (q := (1156869789081 / 50000000000000 : ℝ))
      (E := (cell12234 ⟨1, by decide⟩).energy) (xi := (347135273050673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12234 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12234]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12234])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12234) (a := (84048181048231 / 100000000000000 : ℝ)) (b := (168447719061 / 100000000000000 : ℝ)) (q := (1156869789081 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12234])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12234])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12234]

theorem cert12234_2 : CellCertificate 12234 (900185321060227 / 10000000000000000 : ℝ) (1716911211367999 / 1000000000000000000 : ℝ) (347135273050673 / 10000000000000000 : ℝ)
    (cell12234 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · have h := gap_lower (n := 12234) (a := (16802615536857 / 20000000000000 : ℝ)) (b := (168447719061 / 100000000000000 : ℝ)) (q := (2313743577101 / 100000000000000 : ℝ))
      (E := (cell12234 ⟨2, by decide⟩).energy) (xi := (347135273050673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12234 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12234]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12234])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12234) (a := (16802615536857 / 20000000000000 : ℝ)) (b := (168447719061 / 100000000000000 : ℝ)) (q := (2313743577101 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12234])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12234])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12234]

theorem cert12234_3 : CellCertificate 12234 (900185321060227 / 10000000000000000 : ℝ) (1716911211367999 / 1000000000000000000 : ℝ) (347135273050673 / 10000000000000000 : ℝ)
    (cell12234 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · have h := gap_lower (n := 12234) (a := (41988999717609 / 50000000000000 : ℝ)) (b := (168447719061 / 100000000000000 : ℝ)) (q := (144609221043 / 6250000000000 : ℝ))
      (E := (cell12234 ⟨3, by decide⟩).energy) (xi := (347135273050673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12234 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12234]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12234])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12234) (a := (41988999717609 / 50000000000000 : ℝ)) (b := (168447719061 / 100000000000000 : ℝ)) (q := (144609221043 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12234])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12234])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12234]

theorem cert12234_4 : CellCertificate 12234 (900185321060227 / 10000000000000000 : ℝ) (1716911211367999 / 1000000000000000000 : ℝ) (347135273050673 / 10000000000000000 : ℝ)
    (cell12234 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · have h := gap_lower (n := 12234) (a := (83942946264241 / 100000000000000 : ℝ)) (b := (168447719061 / 100000000000000 : ℝ)) (q := (2313751524241 / 100000000000000 : ℝ))
      (E := (cell12234 ⟨4, by decide⟩).energy) (xi := (347135273050673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12234 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12234]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12234])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12234) (a := (83942946264241 / 100000000000000 : ℝ)) (b := (168447719061 / 100000000000000 : ℝ)) (q := (2313751524241 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12234])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12234])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12234]

theorem cert12234_5 : CellCertificate 12234 (900185321060227 / 10000000000000000 : ℝ) (1716911211367999 / 1000000000000000000 : ℝ) (347135273050673 / 10000000000000000 : ℝ)
    (cell12234 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · have h := gap_lower (n := 12234) (a := (83907918134761 / 100000000000000 : ℝ)) (b := (168447719061 / 100000000000000 : ℝ)) (q := (289219443629 / 12500000000000 : ℝ))
      (E := (cell12234 ⟨5, by decide⟩).energy) (xi := (347135273050673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12234 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12234]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12234])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12234) (a := (83907918134761 / 100000000000000 : ℝ)) (b := (168447719061 / 100000000000000 : ℝ)) (q := (289219443629 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12234])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12234])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12234]

theorem cert12234_6 : CellCertificate 12234 (900185321060227 / 10000000000000000 : ℝ) (1716911211367999 / 1000000000000000000 : ℝ) (347135273050673 / 10000000000000000 : ℝ)
    (cell12234 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · have h := gap_lower (n := 12234) (a := (41936457505189 / 50000000000000 : ℝ)) (b := (168447719061 / 100000000000000 : ℝ)) (q := (578439876069 / 25000000000000 : ℝ))
      (E := (cell12234 ⟨6, by decide⟩).energy) (xi := (347135273050673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12234 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12234]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12234])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12234) (a := (41936457505189 / 50000000000000 : ℝ)) (b := (168447719061 / 100000000000000 : ℝ)) (q := (578439876069 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12234])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12234])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12234]

theorem cert12234_7 : CellCertificate 12234 (900185321060227 / 10000000000000000 : ℝ) (1716911211367999 / 1000000000000000000 : ℝ) (347135273050673 / 10000000000000000 : ℝ)
    (cell12234 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · have h := gap_lower (n := 12234) (a := (83837936854883 / 100000000000000 : ℝ)) (b := (168447719061 / 100000000000000 : ℝ)) (q := (578440878609 / 25000000000000 : ℝ))
      (E := (cell12234 ⟨7, by decide⟩).energy) (xi := (347135273050673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12234 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12234]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12234])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12234) (a := (83837936854883 / 100000000000000 : ℝ)) (b := (168447719061 / 100000000000000 : ℝ)) (q := (578440878609 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12234])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12234])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12234]

theorem cert12234_8 : CellCertificate 12234 (900185321060227 / 10000000000000000 : ℝ) (1716911211367999 / 1000000000000000000 : ℝ) (347135273050673 / 10000000000000000 : ℝ)
    (cell12234 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · have h := gap_lower (n := 12234) (a := (41901491816129 / 50000000000000 : ℝ)) (b := (168447719061 / 100000000000000 : ℝ)) (q := (462753506013 / 20000000000000 : ℝ))
      (E := (cell12234 ⟨8, by decide⟩).energy) (xi := (347135273050673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12234 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12234]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12234])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12234) (a := (41901491816129 / 50000000000000 : ℝ)) (b := (168447719061 / 100000000000000 : ℝ)) (q := (462753506013 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12234])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12234])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12234]

theorem cert12234_9 : CellCertificate 12234 (900185321060227 / 10000000000000000 : ℝ) (1716911211367999 / 1000000000000000000 : ℝ) (347135273050673 / 10000000000000000 : ℝ)
    (cell12234 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · have h := gap_lower (n := 12234) (a := (20942013826669 / 25000000000000 : ℝ)) (b := (168447719061 / 100000000000000 : ℝ)) (q := (1156885750681 / 50000000000000 : ℝ))
      (E := (cell12234 ⟨9, by decide⟩).energy) (xi := (347135273050673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12234 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12234]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12234])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12234) (a := (20942013826669 / 25000000000000 : ℝ)) (b := (168447719061 / 100000000000000 : ℝ)) (q := (1156885750681 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12234])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12234])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12234]

theorem cert12234_10 : CellCertificate 12234 (900185321060227 / 10000000000000000 : ℝ) (1716911211367999 / 1000000000000000000 : ℝ) (347135273050673 / 10000000000000000 : ℝ)
    (cell12234 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · have h := gap_lower (n := 12234) (a := (16746630368499 / 20000000000000 : ℝ)) (b := (168447719061 / 100000000000000 : ℝ)) (q := (578443873543 / 25000000000000 : ℝ))
      (E := (cell12234 ⟨10, by decide⟩).energy) (xi := (347135273050673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12234 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12234]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12234])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12234) (a := (16746630368499 / 20000000000000 : ℝ)) (b := (168447719061 / 100000000000000 : ℝ)) (q := (578443873543 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12234])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12234])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12234]

theorem cert12234_11 : CellCertificate 12234 (900185321060227 / 10000000000000000 : ℝ) (1716911211367999 / 1000000000000000000 : ℝ) (347135273050673 / 10000000000000000 : ℝ)
    (cell12234 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · have h := gap_lower (n := 12234) (a := (83698273204263 / 100000000000000 : ℝ)) (b := (168447719061 / 100000000000000 : ℝ)) (q := (1156889729071 / 50000000000000 : ℝ))
      (E := (cell12234 ⟨11, by decide⟩).energy) (xi := (347135273050673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12234 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12234]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12234])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12234) (a := (83698273204263 / 100000000000000 : ℝ)) (b := (168447719061 / 100000000000000 : ℝ)) (q := (1156889729071 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12234])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12234])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12234]

theorem cert12234_12 : CellCertificate 12234 (900185321060227 / 10000000000000000 : ℝ) (1716911211367999 / 1000000000000000000 : ℝ) (347135273050673 / 10000000000000000 : ℝ)
    (cell12234 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · have h := gap_lower (n := 12234) (a := (83663419356711 / 100000000000000 : ℝ)) (b := (168447719061 / 100000000000000 : ℝ)) (q := (2313783458657 / 100000000000000 : ℝ))
      (E := (cell12234 ⟨12, by decide⟩).energy) (xi := (347135273050673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12234 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12234]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12234])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12234) (a := (83663419356711 / 100000000000000 : ℝ)) (b := (168447719061 / 100000000000000 : ℝ)) (q := (2313783458657 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12234])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12234])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12234]

theorem cert12234_13 : CellCertificate 12234 (900185321060227 / 10000000000000000 : ℝ) (1716911211367999 / 1000000000000000000 : ℝ) (347135273050673 / 10000000000000000 : ℝ)
    (cell12234 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · have h := gap_lower (n := 12234) (a := (83628590264757 / 100000000000000 : ℝ)) (b := (168447719061 / 100000000000000 : ℝ)) (q := (578446861203 / 25000000000000 : ℝ))
      (E := (cell12234 ⟨13, by decide⟩).energy) (xi := (347135273050673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12234 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12234]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12234])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12234) (a := (83628590264757 / 100000000000000 : ℝ)) (b := (168447719061 / 100000000000000 : ℝ)) (q := (578446861203 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12234])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12234])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12234]

theorem cert12234_14 : CellCertificate 12234 (900185321060227 / 10000000000000000 : ℝ) (1716911211367999 / 1000000000000000000 : ℝ) (347135273050673 / 10000000000000000 : ℝ)
    (cell12234 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · have h := gap_lower (n := 12234) (a := (83593785893501 / 100000000000000 : ℝ)) (b := (168447719061 / 100000000000000 : ℝ)) (q := (2313791423449 / 100000000000000 : ℝ))
      (E := (cell12234 ⟨14, by decide⟩).energy) (xi := (347135273050673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12234 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12234]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12234])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12234) (a := (83593785893501 / 100000000000000 : ℝ)) (b := (168447719061 / 100000000000000 : ℝ)) (q := (2313791423449 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12234])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12234])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12234]

theorem cert12234_15 : CellCertificate 12234 (900185321060227 / 10000000000000000 : ℝ) (1716911211367999 / 1000000000000000000 : ℝ) (347135273050673 / 10000000000000000 : ℝ)
    (cell12234 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · have h := gap_lower (n := 12234) (a := (41779503104113 / 50000000000000 : ℝ)) (b := (168447719061 / 100000000000000 : ℝ)) (q := (2313795459271 / 100000000000000 : ℝ))
      (E := (cell12234 ⟨15, by decide⟩).energy) (xi := (347135273050673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12234 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12234]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12234])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12234) (a := (41779503104113 / 50000000000000 : ℝ)) (b := (168447719061 / 100000000000000 : ℝ)) (q := (2313795459271 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12234])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12234])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12234]

theorem cert12234_16 : CellCertificate 12234 (900185321060227 / 10000000000000000 : ℝ) (1716911211367999 / 1000000000000000000 : ℝ) (347135273050673 / 10000000000000000 : ℝ)
    (cell12234 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · have h := gap_lower (n := 12234) (a := (41762125587197 / 50000000000000 : ℝ)) (b := (168447719061 / 100000000000000 : ℝ)) (q := (1156899721213 / 50000000000000 : ℝ))
      (E := (cell12234 ⟨16, by decide⟩).energy) (xi := (347135273050673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12234 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12234]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12234])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12234) (a := (41762125587197 / 50000000000000 : ℝ)) (b := (168447719061 / 100000000000000 : ℝ)) (q := (1156899721213 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12234])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12234])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12234]

theorem cert12234_17 : CellCertificate 12234 (900185321060227 / 10000000000000000 : ℝ) (1716911211367999 / 1000000000000000000 : ℝ) (347135273050673 / 10000000000000000 : ℝ)
    (cell12234 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · have h := gap_lower (n := 12234) (a := (5218095047353 / 6250000000000 : ℝ)) (b := (168447719061 / 100000000000000 : ℝ)) (q := (23138034371 / 1000000000000 : ℝ))
      (E := (cell12234 ⟨17, by decide⟩).energy) (xi := (347135273050673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12234 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12234]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12234])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12234) (a := (5218095047353 / 6250000000000 : ℝ)) (b := (168447719061 / 100000000000000 : ℝ)) (q := (23138034371 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12234])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12234])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12234]

theorem cert12234_18 : CellCertificate 12234 (900185321060227 / 10000000000000000 : ℝ) (1716911211367999 / 1000000000000000000 : ℝ) (347135273050673 / 10000000000000000 : ℝ)
    (cell12234 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · have h := gap_lower (n := 12234) (a := (8345481492381 / 10000000000000 : ℝ)) (b := (168447719061 / 100000000000000 : ℝ)) (q := (1156903695481 / 50000000000000 : ℝ))
      (E := (cell12234 ⟨18, by decide⟩).energy) (xi := (347135273050673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12234 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12234]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12234])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12234) (a := (8345481492381 / 10000000000000 : ℝ)) (b := (168447719061 / 100000000000000 : ℝ)) (q := (1156903695481 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12234])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12234])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12234]

theorem cert12234_19 : CellCertificate 12234 (900185321060227 / 10000000000000000 : ℝ) (1716911211367999 / 1000000000000000000 : ℝ) (347135273050673 / 10000000000000000 : ℝ)
    (cell12234 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · have h := gap_lower (n := 12234) (a := (521375835243 / 625000000000 : ℝ)) (b := (168447719061 / 100000000000000 : ℝ)) (q := (1156905712981 / 50000000000000 : ℝ))
      (E := (cell12234 ⟨19, by decide⟩).energy) (xi := (347135273050673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12234 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12234]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12234])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12234) (a := (521375835243 / 625000000000 : ℝ)) (b := (168447719061 / 100000000000000 : ℝ)) (q := (1156905712981 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12234])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12234])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12234]

theorem cert12235_0 : CellCertificate 12235 (112519412929669 / 1250000000000000 : ℝ) (1716770835629093 / 1000000000000000000 : ℝ) (6942122742089 / 200000000000000 : ℝ)
    (cell12235 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · have h := gap_lower (n := 12235) (a := (84083293259983 / 100000000000000 : ℝ)) (b := (42108441523 / 25000000000000 : ℝ)) (q := (2313586962843 / 100000000000000 : ℝ))
      (E := (cell12235 ⟨0, by decide⟩).energy) (xi := (6942122742089 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12235 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12235]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12235])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12235) (a := (84083293259983 / 100000000000000 : ℝ)) (b := (42108441523 / 25000000000000 : ℝ)) (q := (2313586962843 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12235])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12235])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12235]

theorem cert12235_1 : CellCertificate 12235 (112519412929669 / 1250000000000000 : ℝ) (1716770835629093 / 1000000000000000000 : ℝ) (6942122742089 / 200000000000000 : ℝ)
    (cell12235 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · have h := gap_lower (n := 12235) (a := (42024082541631 / 50000000000000 : ℝ)) (b := (42108441523 / 25000000000000 : ℝ)) (q := (578397736471 / 25000000000000 : ℝ))
      (E := (cell12235 ⟨1, by decide⟩).energy) (xi := (6942122742089 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12235 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12235]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12235])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12235) (a := (42024082541631 / 50000000000000 : ℝ)) (b := (42108441523 / 25000000000000 : ℝ)) (q := (578397736471 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12235])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12235])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12235]

theorem cert12235_2 : CellCertificate 12235 (112519412929669 / 1250000000000000 : ℝ) (1716770835629093 / 1000000000000000000 : ℝ) (6942122742089 / 200000000000000 : ℝ)
    (cell12235 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · have h := gap_lower (n := 12235) (a := (42006531028961 / 50000000000000 : ℝ)) (b := (42108441523 / 25000000000000 : ℝ)) (q := (231359493841 / 10000000000000 : ℝ))
      (E := (cell12235 ⟨2, by decide⟩).energy) (xi := (6942122742089 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12235 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12235]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12235])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12235) (a := (42006531028961 / 50000000000000 : ℝ)) (b := (42108441523 / 25000000000000 : ℝ)) (q := (231359493841 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12235])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12235])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12235]

theorem cert12235_3 : CellCertificate 12235 (112519412929669 / 1250000000000000 : ℝ) (1716770835629093 / 1000000000000000000 : ℝ) (6942122742089 / 200000000000000 : ℝ)
    (cell12235 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · have h := gap_lower (n := 12235) (a := (4198899207349 / 5000000000000 : ℝ)) (b := (42108441523 / 25000000000000 : ℝ)) (q := (462719790043 / 20000000000000 : ℝ))
      (E := (cell12235 ⟨3, by decide⟩).energy) (xi := (6942122742089 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12235 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12235]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12235])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12235) (a := (4198899207349 / 5000000000000 : ℝ)) (b := (42108441523 / 25000000000000 : ℝ)) (q := (462719790043 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12235])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12235])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12235]

theorem cert12235_4 : CellCertificate 12235 (112519412929669 / 1250000000000000 : ℝ) (1716770835629093 / 1000000000000000000 : ℝ) (6942122742089 / 200000000000000 : ℝ)
    (cell12235 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · have h := gap_lower (n := 12235) (a := (83942931313649 / 100000000000000 : ℝ)) (b := (42108441523 / 25000000000000 : ℝ)) (q := (115680146649 / 5000000000000 : ℝ))
      (E := (cell12235 ⟨4, by decide⟩).energy) (xi := (6942122742089 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12235 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12235]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12235])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12235) (a := (83942931313649 / 100000000000000 : ℝ)) (b := (42108441523 / 25000000000000 : ℝ)) (q := (115680146649 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12235])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12235])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12235]

theorem cert12235_5 : CellCertificate 12235 (112519412929669 / 1250000000000000 : ℝ) (1716770835629093 / 1000000000000000000 : ℝ) (6942122742089 / 200000000000000 : ℝ)
    (cell12235 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · have h := gap_lower (n := 12235) (a := (10488487940167 / 12500000000000 : ℝ)) (b := (42108441523 / 25000000000000 : ℝ)) (q := (578401723977 / 25000000000000 : ℝ))
      (E := (cell12235 ⟨5, by decide⟩).energy) (xi := (6942122742089 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12235 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12235]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12235])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12235) (a := (10488487940167 / 12500000000000 : ℝ)) (b := (42108441523 / 25000000000000 : ℝ)) (q := (578401723977 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12235])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12235])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12235]

theorem cert12235_6 : CellCertificate 12235 (112519412929669 / 1250000000000000 : ℝ) (1716770835629093 / 1000000000000000000 : ℝ) (6942122742089 / 200000000000000 : ℝ)
    (cell12235 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · have h := gap_lower (n := 12235) (a := (83872900733643 / 100000000000000 : ℝ)) (b := (42108441523 / 25000000000000 : ℝ)) (q := (28920136323 / 1250000000000 : ℝ))
      (E := (cell12235 ⟨6, by decide⟩).energy) (xi := (6942122742089 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12235 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12235]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12235])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12235) (a := (83872900733643 / 100000000000000 : ℝ)) (b := (42108441523 / 25000000000000 : ℝ)) (q := (28920136323 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12235])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12235])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12235]

theorem cert12235_7 : CellCertificate 12235 (112519412929669 / 1250000000000000 : ℝ) (1716770835629093 / 1000000000000000000 : ℝ) (6942122742089 / 200000000000000 : ℝ)
    (cell12235 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · have h := gap_lower (n := 12235) (a := (83837922914361 / 100000000000000 : ℝ)) (b := (42108441523 / 25000000000000 : ℝ)) (q := (231361491361 / 10000000000000 : ℝ))
      (E := (cell12235 ⟨7, by decide⟩).energy) (xi := (6942122742089 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12235 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12235]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12235])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12235) (a := (83837922914361 / 100000000000000 : ℝ)) (b := (42108441523 / 25000000000000 : ℝ)) (q := (231361491361 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12235])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12235])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12235]

theorem cert12235_8 : CellCertificate 12235 (112519412929669 / 1250000000000000 : ℝ) (1716770835629093 / 1000000000000000000 : ℝ) (6942122742089 / 200000000000000 : ℝ)
    (cell12235 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · have h := gap_lower (n := 12235) (a := (3352118801099 / 4000000000000 : ℝ)) (b := (42108441523 / 25000000000000 : ℝ)) (q := (2313618869697 / 100000000000000 : ℝ))
      (E := (cell12235 ⟨8, by decide⟩).energy) (xi := (6942122742089 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12235 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12235]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12235])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12235) (a := (3352118801099 / 4000000000000 : ℝ)) (b := (42108441523 / 25000000000000 : ℝ)) (q := (2313618869697 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12235])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12235])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12235]

theorem cert12235_9 : CellCertificate 12235 (112519412929669 / 1250000000000000 : ℝ) (1716770835629093 / 1000000000000000000 : ℝ) (6942122742089 / 200000000000000 : ℝ)
    (cell12235 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · have h := gap_lower (n := 12235) (a := (83768042037157 / 100000000000000 : ℝ)) (b := (42108441523 / 25000000000000 : ℝ)) (q := (2313622898143 / 100000000000000 : ℝ))
      (E := (cell12235 ⟨9, by decide⟩).energy) (xi := (6942122742089 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12235 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12235]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12235])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12235) (a := (83768042037157 / 100000000000000 : ℝ)) (b := (42108441523 / 25000000000000 : ℝ)) (q := (2313622898143 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12235])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12235])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12235]

theorem cert12235_10 : CellCertificate 12235 (112519412929669 / 1250000000000000 : ℝ) (1716770835629093 / 1000000000000000000 : ℝ) (6942122742089 / 200000000000000 : ℝ)
    (cell12235 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · have h := gap_lower (n := 12235) (a := (83733138907767 / 100000000000000 : ℝ)) (b := (42108441523 / 25000000000000 : ℝ)) (q := (578406708239 / 25000000000000 : ℝ))
      (E := (cell12235 ⟨10, by decide⟩).energy) (xi := (6942122742089 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12235 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12235]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12235])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12235) (a := (83733138907767 / 100000000000000 : ℝ)) (b := (42108441523 / 25000000000000 : ℝ)) (q := (578406708239 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12235])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12235])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12235]

theorem cert12235_11 : CellCertificate 12235 (112519412929669 / 1250000000000000 : ℝ) (1716770835629093 / 1000000000000000000 : ℝ) (6942122742089 / 200000000000000 : ℝ)
    (cell12235 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · have h := gap_lower (n := 12235) (a := (83698260603853 / 100000000000000 : ℝ)) (b := (42108441523 / 25000000000000 : ℝ)) (q := (2313630855711 / 100000000000000 : ℝ))
      (E := (cell12235 ⟨11, by decide⟩).energy) (xi := (6942122742089 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12235 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12235]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12235])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12235) (a := (83698260603853 / 100000000000000 : ℝ)) (b := (42108441523 / 25000000000000 : ℝ)) (q := (2313630855711 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12235])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12235])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12235]

theorem cert12235_12 : CellCertificate 12235 (112519412929669 / 1250000000000000 : ℝ) (1716770835629093 / 1000000000000000000 : ℝ) (6942122742089 / 200000000000000 : ℝ)
    (cell12235 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · have h := gap_lower (n := 12235) (a := (83663407090149 / 100000000000000 : ℝ)) (b := (42108441523 / 25000000000000 : ℝ)) (q := (2313634857809 / 100000000000000 : ℝ))
      (E := (cell12235 ⟨12, by decide⟩).energy) (xi := (6942122742089 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12235 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12235]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12235])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12235) (a := (83663407090149 / 100000000000000 : ℝ)) (b := (42108441523 / 25000000000000 : ℝ)) (q := (2313634857809 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12235])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12235])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12235]

theorem cert12235_13 : CellCertificate 12235 (112519412929669 / 1250000000000000 : ℝ) (1716770835629093 / 1000000000000000000 : ℝ) (6942122742089 / 200000000000000 : ℝ)
    (cell12235 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · have h := gap_lower (n := 12235) (a := (83628578331573 / 100000000000000 : ℝ)) (b := (42108441523 / 25000000000000 : ℝ)) (q := (1156819423169 / 50000000000000 : ℝ))
      (E := (cell12235 ⟨13, by decide⟩).energy) (xi := (6942122742089 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12235 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12235]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12235])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12235) (a := (83628578331573 / 100000000000000 : ℝ)) (b := (42108441523 / 25000000000000 : ℝ)) (q := (1156819423169 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12235])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12235])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12235]

theorem cert12235_14 : CellCertificate 12235 (112519412929669 / 1250000000000000 : ℝ) (1716770835629093 / 1000000000000000000 : ℝ) (6942122742089 / 200000000000000 : ℝ)
    (cell12235 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · have h := gap_lower (n := 12235) (a := (3343750971729 / 4000000000000 : ℝ)) (b := (42108441523 / 25000000000000 : ℝ)) (q := (2313642828141 / 100000000000000 : ℝ))
      (E := (cell12235 ⟨14, by decide⟩).energy) (xi := (6942122742089 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12235 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12235]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12235])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12235) (a := (3343750971729 / 4000000000000 : ℝ)) (b := (42108441523 / 25000000000000 : ℝ)) (q := (2313642828141 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12235])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12235])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12235]

theorem cert12235_15 : CellCertificate 12235 (112519412929669 / 1250000000000000 : ℝ) (1716770835629093 / 1000000000000000000 : ℝ) (6942122742089 / 200000000000000 : ℝ)
    (cell12235 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · have h := gap_lower (n := 12235) (a := (83558994940389 / 100000000000000 : ℝ)) (b := (42108441523 / 25000000000000 : ℝ)) (q := (2313646809809 / 100000000000000 : ℝ))
      (E := (cell12235 ⟨15, by decide⟩).energy) (xi := (6942122742089 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12235 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12235]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12235])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12235) (a := (83558994940389 / 100000000000000 : ℝ)) (b := (42108441523 / 25000000000000 : ℝ)) (q := (2313646809809 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12235])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12235])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12235]

theorem cert12235_16 : CellCertificate 12235 (112519412929669 / 1250000000000000 : ℝ) (1716770835629093 / 1000000000000000000 : ℝ) (6942122742089 / 200000000000000 : ℝ)
    (cell12235 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · have h := gap_lower (n := 12235) (a := (83524240238529 / 100000000000000 : ℝ)) (b := (42108441523 / 25000000000000 : ℝ)) (q := (1156825398843 / 50000000000000 : ℝ))
      (E := (cell12235 ⟨16, by decide⟩).energy) (xi := (6942122742089 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12235 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12235]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12235])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12235) (a := (83524240238529 / 100000000000000 : ℝ)) (b := (42108441523 / 25000000000000 : ℝ)) (q := (1156825398843 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12235])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12235])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12235]

theorem cert12235_17 : CellCertificate 12235 (112519412929669 / 1250000000000000 : ℝ) (1716770835629093 / 1000000000000000000 : ℝ) (6942122742089 / 200000000000000 : ℝ)
    (cell12235 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · have h := gap_lower (n := 12235) (a := (83489510153289 / 100000000000000 : ℝ)) (b := (42108441523 / 25000000000000 : ℝ)) (q := (2313654797869 / 100000000000000 : ℝ))
      (E := (cell12235 ⟨17, by decide⟩).energy) (xi := (6942122742089 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12235 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12235]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12235])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12235) (a := (83489510153289 / 100000000000000 : ℝ)) (b := (42108441523 / 25000000000000 : ℝ)) (q := (2313654797869 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12235])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12235])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12235]

theorem cert12235_18 : CellCertificate 12235 (112519412929669 / 1250000000000000 : ℝ) (1716770835629093 / 1000000000000000000 : ℝ) (6942122742089 / 200000000000000 : ℝ)
    (cell12235 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · have h := gap_lower (n := 12235) (a := (83454804650493 / 100000000000000 : ℝ)) (b := (42108441523 / 25000000000000 : ℝ)) (q := (231365881621 / 10000000000000 : ℝ))
      (E := (cell12235 ⟨18, by decide⟩).energy) (xi := (6942122742089 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12235 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12235]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12235])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12235) (a := (83454804650493 / 100000000000000 : ℝ)) (b := (42108441523 / 25000000000000 : ℝ)) (q := (231365881621 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12235])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12235])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12235]

theorem cert12235_19 : CellCertificate 12235 (112519412929669 / 1250000000000000 : ℝ) (1716770835629093 / 1000000000000000000 : ℝ) (6942122742089 / 200000000000000 : ℝ)
    (cell12235 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · have h := gap_lower (n := 12235) (a := (83420123696139 / 100000000000000 : ℝ)) (b := (42108441523 / 25000000000000 : ℝ)) (q := (2313662800111 / 100000000000000 : ℝ))
      (E := (cell12235 ⟨19, by decide⟩).energy) (xi := (6942122742089 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12235 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12235]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12235])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12235) (a := (83420123696139 / 100000000000000 : ℝ)) (b := (42108441523 / 25000000000000 : ℝ)) (q := (2313662800111 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12235])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12235])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12235]

theorem cert12236_0 : CellCertificate 12236 (450062645271501 / 5000000000000000 : ℝ) (68665219313709 / 40000000000000000 : ℝ) (17353850308867 / 500000000000000 : ℝ)
    (cell12236 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · have h := gap_lower (n := 12236) (a := (16816655391719 / 20000000000000 : ℝ)) (b := (84209907733 / 50000000000000 : ℝ)) (q := (28917979877 / 1250000000000 : ℝ))
      (E := (cell12236 ⟨0, by decide⟩).energy) (xi := (17353850308867 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12236 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12236]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12236])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12236) (a := (16816655391719 / 20000000000000 : ℝ)) (b := (84209907733 / 50000000000000 : ℝ)) (q := (28917979877 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12236])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12236])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12236]

theorem cert12236_1 : CellCertificate 12236 (450062645271501 / 5000000000000000 : ℝ) (68665219313709 / 40000000000000000 : ℝ) (17353850308867 / 500000000000000 : ℝ)
    (cell12236 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · have h := gap_lower (n := 12236) (a := (42024074560459 / 50000000000000 : ℝ)) (b := (84209907733 / 50000000000000 : ℝ)) (q := (2313442423837 / 100000000000000 : ℝ))
      (E := (cell12236 ⟨1, by decide⟩).energy) (xi := (17353850308867 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12236 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12236]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12236])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12236) (a := (42024074560459 / 50000000000000 : ℝ)) (b := (84209907733 / 50000000000000 : ℝ)) (q := (2313442423837 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12236])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12236])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12236]

theorem cert12236_2 : CellCertificate 12236 (450062645271501 / 5000000000000000 : ℝ) (68665219313709 / 40000000000000000 : ℝ) (17353850308867 / 500000000000000 : ℝ)
    (cell12236 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · have h := gap_lower (n := 12236) (a := (84013046434141 / 100000000000000 : ℝ)) (b := (84209907733 / 50000000000000 : ℝ)) (q := (57836160251 / 2500000000000 : ℝ))
      (E := (cell12236 ⟨2, by decide⟩).energy) (xi := (17353850308867 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12236 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12236]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12236])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12236) (a := (84013046434141 / 100000000000000 : ℝ)) (b := (84209907733 / 50000000000000 : ℝ)) (q := (57836160251 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12236])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12236])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12236]

theorem cert12236_3 : CellCertificate 12236 (450062645271501 / 5000000000000000 : ℝ) (68665219313709 / 40000000000000000 : ℝ) (17353850308867 / 500000000000000 : ℝ)
    (cell12236 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · have h := gap_lower (n := 12236) (a := (41988984430641 / 50000000000000 : ℝ)) (b := (84209907733 / 50000000000000 : ℝ)) (q := (578362604081 / 25000000000000 : ℝ))
      (E := (cell12236 ⟨3, by decide⟩).energy) (xi := (17353850308867 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12236 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12236]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12236])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12236) (a := (41988984430641 / 50000000000000 : ℝ)) (b := (84209907733 / 50000000000000 : ℝ)) (q := (578362604081 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12236])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12236])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12236]

theorem cert12236_4 : CellCertificate 12236 (450062645271501 / 5000000000000000 : ℝ) (68665219313709 / 40000000000000000 : ℝ) (17353850308867 / 500000000000000 : ℝ)
    (cell12236 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · have h := gap_lower (n := 12236) (a := (41971458182777 / 50000000000000 : ℝ)) (b := (84209907733 / 50000000000000 : ℝ)) (q := (2313454394369 / 100000000000000 : ℝ))
      (E := (cell12236 ⟨4, by decide⟩).energy) (xi := (17353850308867 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12236 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12236]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12236])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12236) (a := (41971458182777 / 50000000000000 : ℝ)) (b := (84209907733 / 50000000000000 : ℝ)) (q := (2313454394369 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12236])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12236])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12236]

theorem cert12236_5 : CellCertificate 12236 (450062645271501 / 5000000000000000 : ℝ) (68665219313709 / 40000000000000000 : ℝ) (17353850308867 / 500000000000000 : ℝ)
    (cell12236 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · have h := gap_lower (n := 12236) (a := (41953944455183 / 50000000000000 : ℝ)) (b := (84209907733 / 50000000000000 : ℝ)) (q := (2313458353377 / 100000000000000 : ℝ))
      (E := (cell12236 ⟨5, by decide⟩).energy) (xi := (17353850308867 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12236 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12236]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12236])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12236) (a := (41953944455183 / 50000000000000 : ℝ)) (b := (84209907733 / 50000000000000 : ℝ)) (q := (2313458353377 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12236])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12236])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12236]

theorem cert12236_6 : CellCertificate 12236 (450062645271501 / 5000000000000000 : ℝ) (68665219313709 / 40000000000000000 : ℝ) (17353850308867 / 500000000000000 : ℝ)
    (cell12236 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · have h := gap_lower (n := 12236) (a := (2096822161483 / 2500000000000 : ℝ)) (b := (84209907733 / 50000000000000 : ℝ)) (q := (578365590047 / 25000000000000 : ℝ))
      (E := (cell12236 ⟨6, by decide⟩).energy) (xi := (17353850308867 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12236 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12236]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12236])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12236) (a := (2096822161483 / 2500000000000 : ℝ)) (b := (84209907733 / 50000000000000 : ℝ)) (q := (578365590047 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12236])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12236])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12236]

theorem cert12236_7 : CellCertificate 12236 (450062645271501 / 5000000000000000 : ℝ) (68665219313709 / 40000000000000000 : ℝ) (17353850308867 / 500000000000000 : ℝ)
    (cell12236 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · have h := gap_lower (n := 12236) (a := (8383790897621 / 10000000000000 : ℝ)) (b := (84209907733 / 50000000000000 : ℝ)) (q := (1156733182817 / 50000000000000 : ℝ))
      (E := (cell12236 ⟨7, by decide⟩).energy) (xi := (17353850308867 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12236 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12236]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12236])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12236) (a := (8383790897621 / 10000000000000 : ℝ)) (b := (84209907733 / 50000000000000 : ℝ)) (q := (1156733182817 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12236])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12236])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12236]

theorem cert12236_8 : CellCertificate 12236 (450062645271501 / 5000000000000000 : ℝ) (68665219313709 / 40000000000000000 : ℝ) (17353850308867 / 500000000000000 : ℝ)
    (cell12236 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · have h := gap_lower (n := 12236) (a := (4190147821251 / 5000000000000 : ℝ)) (b := (84209907733 / 50000000000000 : ℝ)) (q := (2313470320193 / 100000000000000 : ℝ))
      (E := (cell12236 ⟨8, by decide⟩).energy) (xi := (17353850308867 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12236 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12236]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12236])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12236) (a := (4190147821251 / 5000000000000 : ℝ)) (b := (84209907733 / 50000000000000 : ℝ)) (q := (2313470320193 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12236])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12236])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12236]

theorem cert12236_9 : CellCertificate 12236 (450062645271501 / 5000000000000000 : ℝ) (68665219313709 / 40000000000000000 : ℝ) (17353850308867 / 500000000000000 : ℝ)
    (cell12236 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · have h := gap_lower (n := 12236) (a := (83768028769923 / 100000000000000 : ℝ)) (b := (84209907733 / 50000000000000 : ℝ)) (q := (2313474347909 / 100000000000000 : ℝ))
      (E := (cell12236 ⟨9, by decide⟩).energy) (xi := (17353850308867 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12236 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12236]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12236])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12236) (a := (83768028769923 / 100000000000000 : ℝ)) (b := (84209907733 / 50000000000000 : ℝ)) (q := (2313474347909 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12236])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12236])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12236]

theorem cert12236_10 : CellCertificate 12236 (450062645271501 / 5000000000000000 : ℝ) (68665219313709 / 40000000000000000 : ℝ) (17353850308867 / 500000000000000 : ℝ)
    (cell12236 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · have h := gap_lower (n := 12236) (a := (41866562987641 / 50000000000000 : ℝ)) (b := (84209907733 / 50000000000000 : ℝ)) (q := (115673917039 / 5000000000000 : ℝ))
      (E := (cell12236 ⟨10, by decide⟩).energy) (xi := (17353850308867 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12236 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12236]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12236])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12236) (a := (41866562987641 / 50000000000000 : ℝ)) (b := (84209907733 / 50000000000000 : ℝ)) (q := (115673917039 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12236])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12236])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12236]

theorem cert12236_11 : CellCertificate 12236 (450062645271501 / 5000000000000000 : ℝ) (68665219313709 / 40000000000000000 : ℝ) (17353850308867 / 500000000000000 : ℝ)
    (cell12236 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · have h := gap_lower (n := 12236) (a := (16739649601129 / 20000000000000 : ℝ)) (b := (84209907733 / 50000000000000 : ℝ)) (q := (1156741153199 / 50000000000000 : ℝ))
      (E := (cell12236 ⟨11, by decide⟩).energy) (xi := (17353850308867 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12236 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12236]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12236])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12236) (a := (16739649601129 / 20000000000000 : ℝ)) (b := (84209907733 / 50000000000000 : ℝ)) (q := (1156741153199 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12236])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12236])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12236]

theorem cert12236_12 : CellCertificate 12236 (450062645271501 / 5000000000000000 : ℝ) (68665219313709 / 40000000000000000 : ℝ) (17353850308867 / 500000000000000 : ℝ)
    (cell12236 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · have h := gap_lower (n := 12236) (a := (41831697412873 / 50000000000000 : ℝ)) (b := (84209907733 / 50000000000000 : ℝ)) (q := (462697262029 / 20000000000000 : ℝ))
      (E := (cell12236 ⟨12, by decide⟩).energy) (xi := (17353850308867 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12236 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12236]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12236])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12236) (a := (41831697412873 / 50000000000000 : ℝ)) (b := (84209907733 / 50000000000000 : ℝ)) (q := (462697262029 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12236])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12236])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12236]

theorem cert12236_13 : CellCertificate 12236 (450062645271501 / 5000000000000000 : ℝ) (68665219313709 / 40000000000000000 : ℝ) (17353850308867 / 500000000000000 : ℝ)
    (cell12236 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · have h := gap_lower (n := 12236) (a := (16725713280101 / 20000000000000 : ℝ)) (b := (84209907733 / 50000000000000 : ℝ)) (q := (2313490301117 / 100000000000000 : ℝ))
      (E := (cell12236 ⟨13, by decide⟩).energy) (xi := (17353850308867 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12236 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12236]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12236])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12236) (a := (16725713280101 / 20000000000000 : ℝ)) (b := (84209907733 / 50000000000000 : ℝ)) (q := (2313490301117 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12236])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12236])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12236]

theorem cert12236_14 : CellCertificate 12236 (450062645271501 / 5000000000000000 : ℝ) (68665219313709 / 40000000000000000 : ℝ) (17353850308867 / 500000000000000 : ℝ)
    (cell12236 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · have h := gap_lower (n := 12236) (a := (83593762695023 / 100000000000000 : ℝ)) (b := (84209907733 / 50000000000000 : ℝ)) (q := (2313494286153 / 100000000000000 : ℝ))
      (E := (cell12236 ⟨14, by decide⟩).energy) (xi := (17353850308867 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12236 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12236]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12236])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12236) (a := (83593762695023 / 100000000000000 : ℝ)) (b := (84209907733 / 50000000000000 : ℝ)) (q := (2313494286153 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12236])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12236])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12236]

theorem cert12236_15 : CellCertificate 12236 (450062645271501 / 5000000000000000 : ℝ) (68665219313709 / 40000000000000000 : ℝ) (17353850308867 / 500000000000000 : ℝ)
    (cell12236 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · have h := gap_lower (n := 12236) (a := (10444872959323 / 12500000000000 : ℝ)) (b := (84209907733 / 50000000000000 : ℝ)) (q := (578374567961 / 25000000000000 : ℝ))
      (E := (cell12236 ⟨15, by decide⟩).energy) (xi := (17353850308867 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12236 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12236]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12236])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12236) (a := (10444872959323 / 12500000000000 : ℝ)) (b := (84209907733 / 50000000000000 : ℝ)) (q := (578374567961 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12236])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12236])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12236]

theorem cert12236_16 : CellCertificate 12236 (450062645271501 / 5000000000000000 : ℝ) (68665219313709 / 40000000000000000 : ℝ) (17353850308867 / 500000000000000 : ℝ)
    (cell12236 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · have h := gap_lower (n := 12236) (a := (16704845860931 / 20000000000000 : ℝ)) (b := (84209907733 / 50000000000000 : ℝ)) (q := (578375566133 / 25000000000000 : ℝ))
      (E := (cell12236 ⟨16, by decide⟩).energy) (xi := (17353850308867 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12236 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12236]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12236])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12236) (a := (16704845860931 / 20000000000000 : ℝ)) (b := (84209907733 / 50000000000000 : ℝ)) (q := (578375566133 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12236])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12236])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12236]

theorem cert12236_17 : CellCertificate 12236 (450062645271501 / 5000000000000000 : ℝ) (68665219313709 / 40000000000000000 : ℝ) (17353850308867 / 500000000000000 : ℝ)
    (cell12236 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · have h := gap_lower (n := 12236) (a := (521809372193 / 625000000000 : ℝ)) (b := (84209907733 / 50000000000000 : ℝ)) (q := (462701254063 / 20000000000000 : ℝ))
      (E := (cell12236 ⟨17, by decide⟩).energy) (xi := (17353850308867 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12236 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12236]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12236])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12236) (a := (521809372193 / 625000000000 : ℝ)) (b := (84209907733 / 50000000000000 : ℝ)) (q := (462701254063 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12236])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12236])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12236]

theorem cert12236_18 : CellCertificate 12236 (450062645271501 / 5000000000000000 : ℝ) (68665219313709 / 40000000000000000 : ℝ) (17353850308867 / 500000000000000 : ℝ)
    (cell12236 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · have h := gap_lower (n := 12236) (a := (41727397189541 / 50000000000000 : ℝ)) (b := (84209907733 / 50000000000000 : ℝ)) (q := (2313510236861 / 100000000000000 : ℝ))
      (E := (cell12236 ⟨18, by decide⟩).energy) (xi := (17353850308867 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12236 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12236]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12236])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12236) (a := (41727397189541 / 50000000000000 : ℝ)) (b := (84209907733 / 50000000000000 : ℝ)) (q := (2313510236861 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12236])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12236])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12236]

theorem cert12236_19 : CellCertificate 12236 (450062645271501 / 5000000000000000 : ℝ) (68665219313709 / 40000000000000000 : ℝ) (17353850308867 / 500000000000000 : ℝ)
    (cell12236 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · have h := gap_lower (n := 12236) (a := (83420113755263 / 100000000000000 : ℝ)) (b := (84209907733 / 50000000000000 : ℝ)) (q := (2313514227911 / 100000000000000 : ℝ))
      (E := (cell12236 ⟨19, by decide⟩).energy) (xi := (17353850308867 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12236 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12236]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12236])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12236) (a := (83420113755263 / 100000000000000 : ℝ)) (b := (84209907733 / 50000000000000 : ℝ)) (q := (2313514227911 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12236])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12236])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12236]

theorem cert12237_0 : CellCertificate 12237 (112511910297001 / 1250000000000000 : ℝ) (858245076501633 / 500000000000000000 : ℝ) (86761970066967 / 2500000000000000 : ℝ)
    (cell12237 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · have h := gap_lower (n := 12237) (a := (42041630329937 / 50000000000000 : ℝ)) (b := (84202933591 / 50000000000000 : ℝ)) (q := (115664499269 / 5000000000000 : ℝ))
      (E := (cell12237 ⟨0, by decide⟩).energy) (xi := (86761970066967 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12237 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12237]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12237])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12237) (a := (42041630329937 / 50000000000000 : ℝ)) (b := (84202933591 / 50000000000000 : ℝ)) (q := (115664499269 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12237])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12237])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12237]

theorem cert12237_1 : CellCertificate 12237 (112511910297001 / 1250000000000000 : ℝ) (858245076501633 / 500000000000000000 : ℝ) (86761970066967 / 2500000000000000 : ℝ)
    (cell12237 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · have h := gap_lower (n := 12237) (a := (210120332903 / 250000000000 : ℝ)) (b := (84202933591 / 50000000000000 : ℝ)) (q := (2313293954237 / 100000000000000 : ℝ))
      (E := (cell12237 ⟨1, by decide⟩).energy) (xi := (86761970066967 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12237 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12237]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12237])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12237) (a := (210120332903 / 250000000000 : ℝ)) (b := (84202933591 / 50000000000000 : ℝ)) (q := (2313293954237 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12237])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12237])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12237]

theorem cert12237_2 : CellCertificate 12237 (112511910297001 / 1250000000000000 : ℝ) (858245076501633 / 500000000000000000 : ℝ) (86761970066967 / 2500000000000000 : ℝ)
    (cell12237 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · have h := gap_lower (n := 12237) (a := (84013030812943 / 100000000000000 : ℝ)) (b := (84202933591 / 50000000000000 : ℝ)) (q := (462659586837 / 20000000000000 : ℝ))
      (E := (cell12237 ⟨2, by decide⟩).energy) (xi := (86761970066967 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12237 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12237]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12237])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12237) (a := (84013030812943 / 100000000000000 : ℝ)) (b := (84202933591 / 50000000000000 : ℝ)) (q := (462659586837 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12237])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12237])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12237]

theorem cert12237_3 : CellCertificate 12237 (112511910297001 / 1250000000000000 : ℝ) (858245076501633 / 500000000000000000 : ℝ) (86761970066967 / 2500000000000000 : ℝ)
    (cell12237 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · have h := gap_lower (n := 12237) (a := (83977953578123 / 100000000000000 : ℝ)) (b := (84202933591 / 50000000000000 : ℝ)) (q := (2313301935017 / 100000000000000 : ℝ))
      (E := (cell12237 ⟨3, by decide⟩).energy) (xi := (86761970066967 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12237 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12237]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12237])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12237) (a := (83977953578123 / 100000000000000 : ℝ)) (b := (84202933591 / 50000000000000 : ℝ)) (q := (2313301935017 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12237])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12237])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12237]

theorem cert12237_4 : CellCertificate 12237 (112511910297001 / 1250000000000000 : ℝ) (858245076501633 / 500000000000000000 : ℝ) (86761970066967 / 2500000000000000 : ℝ)
    (cell12237 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · have h := gap_lower (n := 12237) (a := (20985725354989 / 25000000000000 : ℝ)) (b := (84202933591 / 50000000000000 : ℝ)) (q := (2313305908409 / 100000000000000 : ℝ))
      (E := (cell12237 ⟨4, by decide⟩).energy) (xi := (86761970066967 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12237 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12237]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12237])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12237) (a := (20985725354989 / 25000000000000 : ℝ)) (b := (84202933591 / 50000000000000 : ℝ)) (q := (2313305908409 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12237])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12237])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12237]

theorem cert12237_5 : CellCertificate 12237 (112511910297001 / 1250000000000000 : ℝ) (858245076501633 / 500000000000000000 : ℝ) (86761970066967 / 2500000000000000 : ℝ)
    (cell12237 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · have h := gap_lower (n := 12237) (a := (1678157486037 / 2000000000000 : ℝ)) (b := (84202933591 / 50000000000000 : ℝ)) (q := (2313309921441 / 100000000000000 : ℝ))
      (E := (cell12237 ⟨5, by decide⟩).energy) (xi := (86761970066967 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12237 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12237]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12237])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12237) (a := (1678157486037 / 2000000000000 : ℝ)) (b := (84202933591 / 50000000000000 : ℝ)) (q := (2313309921441 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12237])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12237])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12237]

theorem cert12237_6 : CellCertificate 12237 (112511910297001 / 1250000000000000 : ℝ) (858245076501633 / 500000000000000000 : ℝ) (86761970066967 / 2500000000000000 : ℝ)
    (cell12237 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · have h := gap_lower (n := 12237) (a := (83872872187409 / 100000000000000 : ℝ)) (b := (84202933591 / 50000000000000 : ℝ)) (q := (1156656962611 / 50000000000000 : ℝ))
      (E := (cell12237 ⟨6, by decide⟩).energy) (xi := (86761970066967 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12237 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12237]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12237])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12237) (a := (83872872187409 / 100000000000000 : ℝ)) (b := (84202933591 / 50000000000000 : ℝ)) (q := (1156656962611 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12237])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12237])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12237]

theorem cert12237_7 : CellCertificate 12237 (112511910297001 / 1250000000000000 : ℝ) (858245076501633 / 500000000000000000 : ℝ) (86761970066967 / 2500000000000000 : ℝ)
    (cell12237 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · have h := gap_lower (n := 12237) (a := (20959473760107 / 25000000000000 : ℝ)) (b := (84202933591 / 50000000000000 : ℝ)) (q := (1156658964217 / 50000000000000 : ℝ))
      (E := (cell12237 ⟨7, by decide⟩).energy) (xi := (86761970066967 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12237 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12237]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12237])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12237) (a := (20959473760107 / 25000000000000 : ℝ)) (b := (84202933591 / 50000000000000 : ℝ)) (q := (1156658964217 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12237])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12237])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12237]

theorem cert12237_8 : CellCertificate 12237 (112511910297001 / 1250000000000000 : ℝ) (858245076501633 / 500000000000000000 : ℝ) (86761970066967 / 2500000000000000 : ℝ)
    (cell12237 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · have h := gap_lower (n := 12237) (a := (20950735706223 / 25000000000000 : ℝ)) (b := (84202933591 / 50000000000000 : ℝ)) (q := (578330470389 / 25000000000000 : ℝ))
      (E := (cell12237 ⟨8, by decide⟩).energy) (xi := (86761970066967 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12237 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12237]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12237])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12237) (a := (20950735706223 / 25000000000000 : ℝ)) (b := (84202933591 / 50000000000000 : ℝ)) (q := (578330470389 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12237])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12237])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12237]

theorem cert12237_9 : CellCertificate 12237 (112511910297001 / 1250000000000000 : ℝ) (858245076501633 / 500000000000000000 : ℝ) (86761970066967 / 2500000000000000 : ℝ)
    (cell12237 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · have h := gap_lower (n := 12237) (a := (41884007752487 / 50000000000000 : ℝ)) (b := (84202933591 / 50000000000000 : ℝ)) (q := (2313325908633 / 100000000000000 : ℝ))
      (E := (cell12237 ⟨9, by decide⟩).energy) (xi := (86761970066967 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12237 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12237]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12237])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12237) (a := (41884007752487 / 50000000000000 : ℝ)) (b := (84202933591 / 50000000000000 : ℝ)) (q := (2313325908633 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12237])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12237])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12237]

theorem cert12237_10 : CellCertificate 12237 (112511910297001 / 1250000000000000 : ℝ) (858245076501633 / 500000000000000000 : ℝ) (86761970066967 / 2500000000000000 : ℝ)
    (cell12237 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · have h := gap_lower (n := 12237) (a := (1046663913063 / 1250000000000 : ℝ)) (b := (84202933591 / 50000000000000 : ℝ)) (q := (289166237707 / 12500000000000 : ℝ))
      (E := (cell12237 ⟨10, by decide⟩).energy) (xi := (86761970066967 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12237 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12237]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12237])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12237) (a := (1046663913063 / 1250000000000 : ℝ)) (b := (84202933591 / 50000000000000 : ℝ)) (q := (289166237707 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12237])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12237])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12237]

theorem cert12237_11 : CellCertificate 12237 (112511910297001 / 1250000000000000 : ℝ) (858245076501633 / 500000000000000000 : ℝ) (86761970066967 / 2500000000000000 : ℝ)
    (cell12237 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · have h := gap_lower (n := 12237) (a := (83698235409637 / 100000000000000 : ℝ)) (b := (84202933591 / 50000000000000 : ℝ)) (q := (1156666934111 / 50000000000000 : ℝ))
      (E := (cell12237 ⟨11, by decide⟩).energy) (xi := (86761970066967 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12237 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12237]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12237])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12237) (a := (83698235409637 / 100000000000000 : ℝ)) (b := (84202933591 / 50000000000000 : ℝ)) (q := (1156666934111 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12237])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12237])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12237]

theorem cert12237_12 : CellCertificate 12237 (112511910297001 / 1250000000000000 : ℝ) (858245076501633 / 500000000000000000 : ℝ) (86761970066967 / 2500000000000000 : ℝ)
    (cell12237 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · have h := gap_lower (n := 12237) (a := (83663382563501 / 100000000000000 : ℝ)) (b := (84202933591 / 50000000000000 : ℝ)) (q := (2313337873711 / 100000000000000 : ℝ))
      (E := (cell12237 ⟨12, by decide⟩).energy) (xi := (86761970066967 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12237 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12237]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12237])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12237) (a := (83663382563501 / 100000000000000 : ℝ)) (b := (84202933591 / 50000000000000 : ℝ)) (q := (2313337873711 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12237])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12237])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12237]

theorem cert12237_13 : CellCertificate 12237 (112511910297001 / 1250000000000000 : ℝ) (858245076501633 / 500000000000000000 : ℝ) (86761970066967 / 2500000000000000 : ℝ)
    (cell12237 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · have h := gap_lower (n := 12237) (a := (83628554471553 / 100000000000000 : ℝ)) (b := (84202933591 / 50000000000000 : ℝ)) (q := (1156670933607 / 50000000000000 : ℝ))
      (E := (cell12237 ⟨13, by decide⟩).energy) (xi := (86761970066967 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12237 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12237]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12237])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12237) (a := (83628554471553 / 100000000000000 : ℝ)) (b := (84202933591 / 50000000000000 : ℝ)) (q := (1156670933607 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12237])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12237])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12237]

theorem cert12237_14 : CellCertificate 12237 (112511910297001 / 1250000000000000 : ℝ) (858245076501633 / 500000000000000000 : ℝ) (86761970066967 / 2500000000000000 : ℝ)
    (cell12237 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · have h := gap_lower (n := 12237) (a := (41796875549447 / 50000000000000 : ℝ)) (b := (84202933591 / 50000000000000 : ℝ)) (q := (1156672927787 / 50000000000000 : ℝ))
      (E := (cell12237 ⟨14, by decide⟩).energy) (xi := (86761970066967 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12237 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12237]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12237])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12237) (a := (41796875549447 / 50000000000000 : ℝ)) (b := (84202933591 / 50000000000000 : ℝ)) (q := (1156672927787 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12237])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12237])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12237]

theorem cert12237_15 : CellCertificate 12237 (112511910297001 / 1250000000000000 : ℝ) (858245076501633 / 500000000000000000 : ℝ) (86761970066967 / 2500000000000000 : ℝ)
    (cell12237 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · have h := gap_lower (n := 12237) (a := (20889743102703 / 25000000000000 : ℝ)) (b := (84202933591 / 50000000000000 : ℝ)) (q := (2313349845377 / 100000000000000 : ℝ))
      (E := (cell12237 ⟨15, by decide⟩).energy) (xi := (86761970066967 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12237 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12237]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12237])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12237) (a := (20889743102703 / 25000000000000 : ℝ)) (b := (84202933591 / 50000000000000 : ℝ)) (q := (2313349845377 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12237])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12237])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12237]

theorem cert12237_16 : CellCertificate 12237 (112511910297001 / 1250000000000000 : ℝ) (858245076501633 / 500000000000000000 : ℝ) (86761970066967 / 2500000000000000 : ℝ)
    (cell12237 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · have h := gap_lower (n := 12237) (a := (83524218372771 / 100000000000000 : ℝ)) (b := (84202933591 / 50000000000000 : ℝ)) (q := (289169230371 / 12500000000000 : ℝ))
      (E := (cell12237 ⟨16, by decide⟩).energy) (xi := (86761970066967 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12237 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12237]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12237])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12237) (a := (83524218372771 / 100000000000000 : ℝ)) (b := (84202933591 / 50000000000000 : ℝ)) (q := (289169230371 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12237])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12237])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12237]

theorem cert12237_17 : CellCertificate 12237 (112511910297001 / 1250000000000000 : ℝ) (858245076501633 / 500000000000000000 : ℝ) (86761970066967 / 2500000000000000 : ℝ)
    (cell12237 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · have h := gap_lower (n := 12237) (a := (41744744475209 / 50000000000000 : ℝ)) (b := (84202933591 / 50000000000000 : ℝ)) (q := (1156678898141 / 50000000000000 : ℝ))
      (E := (cell12237 ⟨17, by decide⟩).energy) (xi := (86761970066967 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12237 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12237]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12237])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12237) (a := (41744744475209 / 50000000000000 : ℝ)) (b := (84202933591 / 50000000000000 : ℝ)) (q := (1156678898141 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12237])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12237])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12237]

theorem cert12237_18 : CellCertificate 12237 (112511910297001 / 1250000000000000 : ℝ) (858245076501633 / 500000000000000000 : ℝ) (86761970066967 / 2500000000000000 : ℝ)
    (cell12237 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · have h := gap_lower (n := 12237) (a := (41727392054789 / 50000000000000 : ℝ)) (b := (84202933591 / 50000000000000 : ℝ)) (q := (2313361827463 / 100000000000000 : ℝ))
      (E := (cell12237 ⟨18, by decide⟩).energy) (xi := (86761970066967 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12237 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12237]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12237])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12237) (a := (41727392054789 / 50000000000000 : ℝ)) (b := (84202933591 / 50000000000000 : ℝ)) (q := (2313361827463 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12237])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12237])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12237]

theorem cert12237_19 : CellCertificate 12237 (112511910297001 / 1250000000000000 : ℝ) (858245076501633 / 500000000000000000 : ℝ) (86761970066967 / 2500000000000000 : ℝ)
    (cell12237 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · have h := gap_lower (n := 12237) (a := (83420103816251 / 100000000000000 : ℝ)) (b := (84202933591 / 50000000000000 : ℝ)) (q := (1156682912889 / 50000000000000 : ℝ))
      (E := (cell12237 ⟨19, by decide⟩).energy) (xi := (86761970066967 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12237 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12237]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12237])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12237) (a := (83420103816251 / 100000000000000 : ℝ)) (b := (84202933591 / 50000000000000 : ℝ)) (q := (1156682912889 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12237])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12237])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12237]

theorem cert12238_0 : CellCertificate 12238 (1125081598669 / 12500000000000 : ℝ) (171634984610509 / 100000000000000000 : ℝ) (173509379687279 / 5000000000000000 : ℝ)
    (cell12238 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · have h := gap_lower (n := 12238) (a := (84083244363821 / 100000000000000 : ℝ)) (b := (168391921239 / 100000000000000 : ℝ)) (q := (1156570816491 / 50000000000000 : ℝ))
      (E := (cell12238 ⟨0, by decide⟩).energy) (xi := (173509379687279 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12238 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12238]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12238])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12238) (a := (84083244363821 / 100000000000000 : ℝ)) (b := (168391921239 / 100000000000000 : ℝ)) (q := (1156570816491 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12238])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12238])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12238]

theorem cert12238_1 : CellCertificate 12238 (1125081598669 / 12500000000000 : ℝ) (171634984610509 / 100000000000000000 : ℝ) (173509379687279 / 5000000000000000 : ℝ)
    (cell12238 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · have h := gap_lower (n := 12238) (a := (42024058602053 / 50000000000000 : ℝ)) (b := (168391921239 / 100000000000000 : ℝ)) (q := (289143199359 / 12500000000000 : ℝ))
      (E := (cell12238 ⟨1, by decide⟩).energy) (xi := (173509379687279 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12238 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12238]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12238])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12238) (a := (42024058602053 / 50000000000000 : ℝ)) (b := (168391921239 / 100000000000000 : ℝ)) (q := (289143199359 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12238])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12238])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12238]

theorem cert12238_2 : CellCertificate 12238 (1125081598669 / 12500000000000 : ℝ) (171634984610509 / 100000000000000000 : ℝ) (173509379687279 / 5000000000000000 : ℝ)
    (cell12238 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · have h := gap_lower (n := 12238) (a := (42006507597163 / 50000000000000 : ℝ)) (b := (168391921239 / 100000000000000 : ℝ)) (q := (2313149626463 / 100000000000000 : ℝ))
      (E := (cell12238 ⟨2, by decide⟩).energy) (xi := (173509379687279 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12238 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12238]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12238])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12238) (a := (42006507597163 / 50000000000000 : ℝ)) (b := (168391921239 / 100000000000000 : ℝ)) (q := (2313149626463 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12238])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12238])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12238]

theorem cert12238_3 : CellCertificate 12238 (1125081598669 / 12500000000000 : ℝ) (171634984610509 / 100000000000000000 : ℝ) (173509379687279 / 5000000000000000 : ℝ)
    (cell12238 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · have h := gap_lower (n := 12238) (a := (83977938297503 / 100000000000000 : ℝ)) (b := (168391921239 / 100000000000000 : ℝ)) (q := (18505228513 / 800000000000 : ℝ))
      (E := (cell12238 ⟨3, by decide⟩).energy) (xi := (173509379687279 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12238 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12238]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12238])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12238) (a := (83977938297503 / 100000000000000 : ℝ)) (b := (168391921239 / 100000000000000 : ℝ)) (q := (18505228513 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12238])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12238])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12238]

theorem cert12238_4 : CellCertificate 12238 (1125081598669 / 12500000000000 : ℝ) (171634984610509 / 100000000000000000 : ℝ) (173509379687279 / 5000000000000000 : ℝ)
    (cell12238 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · have h := gap_lower (n := 12238) (a := (41971443238427 / 50000000000000 : ℝ)) (b := (168391921239 / 100000000000000 : ℝ)) (q := (231315759081 / 10000000000000 : ℝ))
      (E := (cell12238 ⟨4, by decide⟩).energy) (xi := (173509379687279 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12238 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12238]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12238])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12238) (a := (41971443238427 / 50000000000000 : ℝ)) (b := (168391921239 / 100000000000000 : ℝ)) (q := (231315759081 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12238])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12238])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12238]

theorem cert12238_5 : CellCertificate 12238 (1125081598669 / 12500000000000 : ℝ) (171634984610509 / 100000000000000000 : ℝ) (173509379687279 / 5000000000000000 : ℝ)
    (cell12238 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · have h := gap_lower (n := 12238) (a := (20976964923947 / 25000000000000 : ℝ)) (b := (168391921239 / 100000000000000 : ℝ)) (q := (92526461689 / 4000000000000 : ℝ))
      (E := (cell12238 ⟨5, by decide⟩).energy) (xi := (173509379687279 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12238 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12238]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12238])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12238) (a := (20976964923947 / 25000000000000 : ℝ)) (b := (168391921239 / 100000000000000 : ℝ)) (q := (92526461689 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12238])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12238])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12238]

theorem cert12238_6 : CellCertificate 12238 (1125081598669 / 12500000000000 : ℝ) (171634984610509 / 100000000000000000 : ℝ) (173509379687279 / 5000000000000000 : ℝ)
    (cell12238 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · have h := gap_lower (n := 12238) (a := (8387285791791 / 10000000000000 : ℝ)) (b := (168391921239 / 100000000000000 : ℝ)) (q := (1156582771521 / 50000000000000 : ℝ))
      (E := (cell12238 ⟨6, by decide⟩).energy) (xi := (173509379687279 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12238 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12238]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12238])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12238) (a := (8387285791791 / 10000000000000 : ℝ)) (b := (168391921239 / 100000000000000 : ℝ)) (q := (1156582771521 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12238])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12238])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12238]

theorem cert12238_7 : CellCertificate 12238 (1125081598669 / 12500000000000 : ℝ) (171634984610509 / 100000000000000000 : ℝ) (173509379687279 / 5000000000000000 : ℝ)
    (cell12238 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · have h := gap_lower (n := 12238) (a := (16767576221403 / 20000000000000 : ℝ)) (b := (168391921239 / 100000000000000 : ℝ)) (q := (289146193011 / 12500000000000 : ℝ))
      (E := (cell12238 ⟨7, by decide⟩).energy) (xi := (173509379687279 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12238 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12238]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12238])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12238) (a := (16767576221403 / 20000000000000 : ℝ)) (b := (168391921239 / 100000000000000 : ℝ)) (q := (289146193011 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12238])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12238])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12238]

theorem cert12238_8 : CellCertificate 12238 (1125081598669 / 12500000000000 : ℝ) (171634984610509 / 100000000000000000 : ℝ) (173509379687279 / 5000000000000000 : ℝ)
    (cell12238 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · have h := gap_lower (n := 12238) (a := (8380292922709 / 10000000000000 : ℝ)) (b := (168391921239 / 100000000000000 : ℝ)) (q := (2313173553789 / 100000000000000 : ℝ))
      (E := (cell12238 ⟨8, by decide⟩).energy) (xi := (173509379687279 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12238 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12238]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12238])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12238) (a := (8380292922709 / 10000000000000 : ℝ)) (b := (168391921239 / 100000000000000 : ℝ)) (q := (2313173553789 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12238])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12238])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12238]

theorem cert12238_9 : CellCertificate 12238 (1125081598669 / 12500000000000 : ℝ) (171634984610509 / 100000000000000000 : ℝ) (173509379687279 / 5000000000000000 : ℝ)
    (cell12238 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · have h := gap_lower (n := 12238) (a := (8376800224231 / 10000000000000 : ℝ)) (b := (168391921239 / 100000000000000 : ℝ)) (q := (289147190293 / 12500000000000 : ℝ))
      (E := (cell12238 ⟨9, by decide⟩).energy) (xi := (173509379687279 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12238 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12238]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12238])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12238) (a := (8376800224231 / 10000000000000 : ℝ)) (b := (168391921239 / 100000000000000 : ℝ)) (q := (289147190293 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12238])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12238])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12238]

theorem cert12238_10 : CellCertificate 12238 (1125081598669 / 12500000000000 : ℝ) (171634984610509 / 100000000000000000 : ℝ) (173509379687279 / 5000000000000000 : ℝ)
    (cell12238 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · have h := gap_lower (n := 12238) (a := (83733100117039 / 100000000000000 : ℝ)) (b := (168391921239 / 100000000000000 : ℝ)) (q := (2313181515589 / 100000000000000 : ℝ))
      (E := (cell12238 ⟨10, by decide⟩).energy) (xi := (173509379687279 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12238 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12238]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12238])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12238) (a := (83733100117039 / 100000000000000 : ℝ)) (b := (168391921239 / 100000000000000 : ℝ)) (q := (2313181515589 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12238])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12238])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12238]

theorem cert12238_11 : CellCertificate 12238 (1125081598669 / 12500000000000 : ℝ) (171634984610509 / 100000000000000000 : ℝ) (173509379687279 / 5000000000000000 : ℝ)
    (cell12238 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · have h := gap_lower (n := 12238) (a := (20924555703957 / 25000000000000 : ℝ)) (b := (168391921239 / 100000000000000 : ℝ)) (q := (578296385297 / 25000000000000 : ℝ))
      (E := (cell12238 ⟨11, by decide⟩).energy) (xi := (173509379687279 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12238 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12238]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12238])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12238) (a := (20924555703957 / 25000000000000 : ℝ)) (b := (168391921239 / 100000000000000 : ℝ)) (q := (578296385297 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12238])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12238])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12238]

theorem cert12238_12 : CellCertificate 12238 (1125081598669 / 12500000000000 : ℝ) (171634984610509 / 100000000000000000 : ℝ) (173509379687279 / 5000000000000000 : ℝ)
    (cell12238 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · have h := gap_lower (n := 12238) (a := (83663370303413 / 100000000000000 : ℝ)) (b := (168391921239 / 100000000000000 : ℝ)) (q := (462637898093 / 20000000000000 : ℝ))
      (E := (cell12238 ⟨12, by decide⟩).energy) (xi := (173509379687279 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12238 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12238]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12238])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12238) (a := (83663370303413 / 100000000000000 : ℝ)) (b := (168391921239 / 100000000000000 : ℝ)) (q := (462637898093 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12238])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12238])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12238]

theorem cert12238_13 : CellCertificate 12238 (1125081598669 / 12500000000000 : ℝ) (171634984610509 / 100000000000000000 : ℝ) (173509379687279 / 5000000000000000 : ℝ)
    (cell12238 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · have h := gap_lower (n := 12238) (a := (20907135636179 / 25000000000000 : ℝ)) (b := (168391921239 / 100000000000000 : ℝ)) (q := (289149185821 / 12500000000000 : ℝ))
      (E := (cell12238 ⟨13, by decide⟩).energy) (xi := (173509379687279 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12238 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12238]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12238])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12238) (a := (20907135636179 / 25000000000000 : ℝ)) (b := (168391921239 / 100000000000000 : ℝ)) (q := (289149185821 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12238])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12238])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12238]

theorem cert12238_14 : CellCertificate 12238 (1125081598669 / 12500000000000 : ℝ) (171634984610509 / 100000000000000000 : ℝ) (173509379687279 / 5000000000000000 : ℝ)
    (cell12238 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · have h := gap_lower (n := 12238) (a := (2089843487621 / 2500000000000 : ℝ)) (b := (168391921239 / 100000000000000 : ℝ)) (q := (2313197478317 / 100000000000000 : ℝ))
      (E := (cell12238 ⟨14, by decide⟩).energy) (xi := (173509379687279 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12238 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12238]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12238])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12238) (a := (2089843487621 / 2500000000000 : ℝ)) (b := (168391921239 / 100000000000000 : ℝ)) (q := (2313197478317 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12238])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12238])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12238]

theorem cert12238_15 : CellCertificate 12238 (1125081598669 / 12500000000000 : ℝ) (171634984610509 / 100000000000000000 : ℝ) (173509379687279 / 5000000000000000 : ℝ)
    (cell12238 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · have h := gap_lower (n := 12238) (a := (83558961149071 / 100000000000000 : ℝ)) (b := (168391921239 / 100000000000000 : ℝ)) (q := (23132014723 / 1000000000000 : ℝ))
      (E := (cell12238 ⟨15, by decide⟩).energy) (xi := (173509379687279 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12238 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12238]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12238])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12238) (a := (83558961149071 / 100000000000000 : ℝ)) (b := (168391921239 / 100000000000000 : ℝ)) (q := (23132014723 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12238])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12238])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12238]

theorem cert12238_16 : CellCertificate 12238 (1125081598669 / 12500000000000 : ℝ) (171634984610509 / 100000000000000000 : ℝ) (173509379687279 / 5000000000000000 : ℝ)
    (cell12238 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · have h := gap_lower (n := 12238) (a := (83524207442877 / 100000000000000 : ℝ)) (b := (168391921239 / 100000000000000 : ℝ)) (q := (2313205474859 / 100000000000000 : ℝ))
      (E := (cell12238 ⟨16, by decide⟩).energy) (xi := (173509379687279 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12238 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12238]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12238])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12238) (a := (83524207442877 / 100000000000000 : ℝ)) (b := (168391921239 / 100000000000000 : ℝ)) (q := (2313205474859 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12238])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12238])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12238]

theorem cert12238_17 : CellCertificate 12238 (1125081598669 / 12500000000000 : ℝ) (171634984610509 / 100000000000000000 : ℝ) (173509379687279 / 5000000000000000 : ℝ)
    (cell12238 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · have h := gap_lower (n := 12238) (a := (16697895670381 / 20000000000000 : ℝ)) (b := (168391921239 / 100000000000000 : ℝ)) (q := (289151186511 / 12500000000000 : ℝ))
      (E := (cell12238 ⟨17, by decide⟩).energy) (xi := (173509379687279 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12238 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12238]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12238])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12238) (a := (16697895670381 / 20000000000000 : ℝ)) (b := (168391921239 / 100000000000000 : ℝ)) (q := (289151186511 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12238])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12238])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12238]

theorem cert12238_18 : CellCertificate 12238 (1125081598669 / 12500000000000 : ℝ) (171634984610509 / 100000000000000000 : ℝ) (173509379687279 / 5000000000000000 : ℝ)
    (cell12238 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · have h := gap_lower (n := 12238) (a := (83454773841979 / 100000000000000 : ℝ)) (b := (168391921239 / 100000000000000 : ℝ)) (q := (462642694331 / 20000000000000 : ℝ))
      (E := (cell12238 ⟨18, by decide⟩).energy) (xi := (173509379687279 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12238 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12238]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12238])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12238) (a := (83454773841979 / 100000000000000 : ℝ)) (b := (168391921239 / 100000000000000 : ℝ)) (q := (462642694331 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12238])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12238])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12238]

theorem cert12238_19 : CellCertificate 12238 (1125081598669 / 12500000000000 : ℝ) (171634984610509 / 100000000000000000 : ℝ) (173509379687279 / 5000000000000000 : ℝ)
    (cell12238 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · have h := gap_lower (n := 12238) (a := (1303438966861 / 1562500000000 : ℝ)) (b := (168391921239 / 100000000000000 : ℝ)) (q := (1156608738649 / 50000000000000 : ℝ))
      (E := (cell12238 ⟨19, by decide⟩).energy) (xi := (173509379687279 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12238 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12238]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12238])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12238) (a := (1303438966861 / 1562500000000 : ℝ)) (b := (168391921239 / 100000000000000 : ℝ)) (q := (1156608738649 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12238])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12238])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12238]

theorem cert12239_0 : CellCertificate 12239 (900035280219407 / 10000000000000000 : ℝ) (171620956214257 / 100000000000000000 : ℝ) (346989643495939 / 10000000000000000 : ℝ)
    (cell12239 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · have h := gap_lower (n := 12239) (a := (16816645614087 / 20000000000000 : ℝ)) (b := (168377977637 / 100000000000000 : ℝ)) (q := (289124166621 / 12500000000000 : ℝ))
      (E := (cell12239 ⟨0, by decide⟩).energy) (xi := (346989643495939 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12239 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12239]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12239])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12239) (a := (16816645614087 / 20000000000000 : ℝ)) (b := (168377977637 / 100000000000000 : ℝ)) (q := (289124166621 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12239])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12239])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12239]

theorem cert12239_1 : CellCertificate 12239 (900035280219407 / 10000000000000000 : ℝ) (171620956214257 / 100000000000000000 : ℝ) (346989643495939 / 10000000000000000 : ℝ)
    (cell12239 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · have h := gap_lower (n := 12239) (a := (16809620249927 / 20000000000000 : ℝ)) (b := (168377977637 / 100000000000000 : ℝ)) (q := (2312997345743 / 100000000000000 : ℝ))
      (E := (cell12239 ⟨1, by decide⟩).energy) (xi := (346989643495939 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12239 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12239]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12239])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12239) (a := (16809620249927 / 20000000000000 : ℝ)) (b := (168377977637 / 100000000000000 : ℝ)) (q := (2312997345743 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12239])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12239])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12239]

theorem cert12239_2 : CellCertificate 12239 (900035280219407 / 10000000000000000 : ℝ) (171620956214257 / 100000000000000000 : ℝ) (346989643495939 / 10000000000000000 : ℝ)
    (cell12239 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · have h := gap_lower (n := 12239) (a := (8401299957829 / 10000000000000 : ℝ)) (b := (168377977637 / 100000000000000 : ℝ)) (q := (2313001313453 / 100000000000000 : ℝ))
      (E := (cell12239 ⟨2, by decide⟩).energy) (xi := (346989643495939 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12239 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12239]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12239])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12239) (a := (8401299957829 / 10000000000000 : ℝ)) (b := (168377977637 / 100000000000000 : ℝ)) (q := (2313001313453 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12239])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12239])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12239]

theorem cert12239_3 : CellCertificate 12239 (900035280219407 / 10000000000000000 : ℝ) (171620956214257 / 100000000000000000 : ℝ) (346989643495939 / 10000000000000000 : ℝ)
    (cell12239 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · have h := gap_lower (n := 12239) (a := (41988961509711 / 50000000000000 : ℝ)) (b := (168377977637 / 100000000000000 : ℝ)) (q := (2313005303651 / 100000000000000 : ℝ))
      (E := (cell12239 ⟨3, by decide⟩).energy) (xi := (346989643495939 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12239 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12239]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12239])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12239) (a := (41988961509711 / 50000000000000 : ℝ)) (b := (168377977637 / 100000000000000 : ℝ)) (q := (2313005303651 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12239])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12239])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12239]

theorem cert12239_4 : CellCertificate 12239 (900035280219407 / 10000000000000000 : ℝ) (171620956214257 / 100000000000000000 : ℝ) (346989643495939 / 10000000000000000 : ℝ)
    (cell12239 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · have h := gap_lower (n := 12239) (a := (10492858942031 / 12500000000000 : ℝ)) (b := (168377977637 / 100000000000000 : ℝ)) (q := (289126165733 / 12500000000000 : ℝ))
      (E := (cell12239 ⟨4, by decide⟩).energy) (xi := (346989643495939 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12239 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12239]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12239])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12239) (a := (10492858942031 / 12500000000000 : ℝ)) (b := (168377977637 / 100000000000000 : ℝ)) (q := (289126165733 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12239])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12239])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12239]

theorem cert12239_5 : CellCertificate 12239 (900035280219407 / 10000000000000000 : ℝ) (171620956214257 / 100000000000000000 : ℝ) (346989643495939 / 10000000000000000 : ℝ)
    (cell12239 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · have h := gap_lower (n := 12239) (a := (83907845092179 / 100000000000000 : ℝ)) (b := (168377977637 / 100000000000000 : ℝ)) (q := (462602666297 / 20000000000000 : ℝ))
      (E := (cell12239 ⟨5, by decide⟩).energy) (xi := (346989643495939 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12239 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12239]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12239])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12239) (a := (83907845092179 / 100000000000000 : ℝ)) (b := (168377977637 / 100000000000000 : ℝ)) (q := (462602666297 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12239])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12239])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12239]

theorem cert12239_6 : CellCertificate 12239 (900035280219407 / 10000000000000000 : ℝ) (171620956214257 / 100000000000000000 : ℝ) (346989643495939 / 10000000000000000 : ℝ)
    (cell12239 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · have h := gap_lower (n := 12239) (a := (83872843650821 / 100000000000000 : ℝ)) (b := (168377977637 / 100000000000000 : ℝ)) (q := (2313017271551 / 100000000000000 : ℝ))
      (E := (cell12239 ⟨6, by decide⟩).energy) (xi := (346989643495939 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12239 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12239]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12239])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12239) (a := (83872843650821 / 100000000000000 : ℝ)) (b := (168377977637 / 100000000000000 : ℝ)) (q := (2313017271551 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12239])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12239])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12239]

theorem cert12239_7 : CellCertificate 12239 (900035280219407 / 10000000000000000 : ℝ) (171620956214257 / 100000000000000000 : ℝ) (346989643495939 / 10000000000000000 : ℝ)
    (cell12239 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · have h := gap_lower (n := 12239) (a := (8383786717597 / 10000000000000 : ℝ)) (b := (168377977637 / 100000000000000 : ℝ)) (q := (2313021270523 / 100000000000000 : ℝ))
      (E := (cell12239 ⟨7, by decide⟩).energy) (xi := (346989643495939 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12239 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12239]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12239])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12239) (a := (8383786717597 / 10000000000000 : ℝ)) (b := (168377977637 / 100000000000000 : ℝ)) (q := (2313021270523 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12239])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12239])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12239]

theorem cert12239_8 : CellCertificate 12239 (900035280219407 / 10000000000000000 : ℝ) (171620956214257 / 100000000000000000 : ℝ) (346989643495939 / 10000000000000000 : ℝ)
    (cell12239 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · have h := gap_lower (n := 12239) (a := (83802915631613 / 100000000000000 : ℝ)) (b := (168377977637 / 100000000000000 : ℝ)) (q := (1156512639473 / 50000000000000 : ℝ))
      (E := (cell12239 ⟨8, by decide⟩).energy) (xi := (346989643495939 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12239 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12239]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12239])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12239) (a := (83802915631613 / 100000000000000 : ℝ)) (b := (168377977637 / 100000000000000 : ℝ)) (q := (1156512639473 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12239])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12239])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12239]

theorem cert12239_9 : CellCertificate 12239 (900035280219407 / 10000000000000000 : ℝ) (171620956214257 / 100000000000000000 : ℝ) (346989643495939 / 10000000000000000 : ℝ)
    (cell12239 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · have h := gap_lower (n := 12239) (a := (10470998622741 / 12500000000000 : ℝ)) (b := (168377977637 / 100000000000000 : ℝ)) (q := (2313029247017 / 100000000000000 : ℝ))
      (E := (cell12239 ⟨9, by decide⟩).energy) (xi := (346989643495939 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12239 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12239]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12239])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12239) (a := (10470998622741 / 12500000000000 : ℝ)) (b := (168377977637 / 100000000000000 : ℝ)) (q := (2313029247017 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12239])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12239])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12239]

theorem cert12239_10 : CellCertificate 12239 (900035280219407 / 10000000000000000 : ℝ) (171620956214257 / 100000000000000000 : ℝ) (346989643495939 / 10000000000000000 : ℝ)
    (cell12239 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · have h := gap_lower (n := 12239) (a := (83733087191279 / 100000000000000 : ℝ)) (b := (168377977637 / 100000000000000 : ℝ)) (q := (1156516620287 / 50000000000000 : ℝ))
      (E := (cell12239 ⟨10, by decide⟩).energy) (xi := (346989643495939 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12239 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12239]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12239])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12239) (a := (83733087191279 / 100000000000000 : ℝ)) (b := (168377977637 / 100000000000000 : ℝ)) (q := (1156516620287 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12239])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12239])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12239]

theorem cert12239_11 : CellCertificate 12239 (900035280219407 / 10000000000000000 : ℝ) (171620956214257 / 100000000000000000 : ℝ) (346989643495939 / 10000000000000000 : ℝ)
    (cell12239 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · have h := gap_lower (n := 12239) (a := (41849105112109 / 50000000000000 : ℝ)) (b := (168377977637 / 100000000000000 : ℝ)) (q := (2313037267277 / 100000000000000 : ℝ))
      (E := (cell12239 ⟨11, by decide⟩).energy) (xi := (346989643495939 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12239 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12239]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12239])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12239) (a := (41849105112109 / 50000000000000 : ℝ)) (b := (168377977637 / 100000000000000 : ℝ)) (q := (2313037267277 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12239])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12239])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12239]

theorem cert12239_12 : CellCertificate 12239 (900035280219407 / 10000000000000000 : ℝ) (171620956214257 / 100000000000000000 : ℝ) (346989643495939 / 10000000000000000 : ℝ)
    (cell12239 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · have h := gap_lower (n := 12239) (a := (83663358045483 / 100000000000000 : ℝ)) (b := (168377977637 / 100000000000000 : ℝ)) (q := (2313041218451 / 100000000000000 : ℝ))
      (E := (cell12239 ⟨12, by decide⟩).energy) (xi := (346989643495939 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12239 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12239]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12239])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12239) (a := (83663358045483 / 100000000000000 : ℝ)) (b := (168377977637 / 100000000000000 : ℝ)) (q := (2313041218451 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12239])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12239])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12239]

theorem cert12239_13 : CellCertificate 12239 (900035280219407 / 10000000000000000 : ℝ) (171620956214257 / 100000000000000000 : ℝ) (346989643495939 / 10000000000000000 : ℝ)
    (cell12239 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · have h := gap_lower (n := 12239) (a := (41814265309997 / 50000000000000 : ℝ)) (b := (168377977637 / 100000000000000 : ℝ)) (q := (578261304311 / 25000000000000 : ℝ))
      (E := (cell12239 ⟨13, by decide⟩).energy) (xi := (346989643495939 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12239 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12239]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12239])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12239) (a := (41814265309997 / 50000000000000 : ℝ)) (b := (168377977637 / 100000000000000 : ℝ)) (q := (578261304311 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12239])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12239])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12239]

theorem cert12239_14 : CellCertificate 12239 (900035280219407 / 10000000000000000 : ℝ) (171620956214257 / 100000000000000000 : ℝ) (346989643495939 / 10000000000000000 : ℝ)
    (cell12239 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · have h := gap_lower (n := 12239) (a := (41796863956429 / 50000000000000 : ℝ)) (b := (168377977637 / 100000000000000 : ℝ)) (q := (2313049212473 / 100000000000000 : ℝ))
      (E := (cell12239 ⟨14, by decide⟩).energy) (xi := (346989643495939 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12239 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12239]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12239])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12239) (a := (41796863956429 / 50000000000000 : ℝ)) (b := (168377977637 / 100000000000000 : ℝ)) (q := (2313049212473 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12239])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12239])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12239]

theorem cert12239_15 : CellCertificate 12239 (900035280219407 / 10000000000000000 : ℝ) (171620956214257 / 100000000000000000 : ℝ) (346989643495939 / 10000000000000000 : ℝ)
    (cell12239 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · have h := gap_lower (n := 12239) (a := (83558949889361 / 100000000000000 : ℝ)) (b := (168377977637 / 100000000000000 : ℝ)) (q := (1156526605363 / 50000000000000 : ℝ))
      (E := (cell12239 ⟨15, by decide⟩).energy) (xi := (346989643495939 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12239 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12239]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12239])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12239) (a := (83558949889361 / 100000000000000 : ℝ)) (b := (168377977637 / 100000000000000 : ℝ)) (q := (1156526605363 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12239])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12239])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12239]

theorem cert12239_16 : CellCertificate 12239 (900035280219407 / 10000000000000000 : ℝ) (171620956214257 / 100000000000000000 : ℝ) (346989643495939 / 10000000000000000 : ℝ)
    (cell12239 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · have h := gap_lower (n := 12239) (a := (20881049128743 / 25000000000000 : ℝ)) (b := (168377977637 / 100000000000000 : ℝ)) (q := (2313057218343 / 100000000000000 : ℝ))
      (E := (cell12239 ⟨16, by decide⟩).energy) (xi := (346989643495939 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12239 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12239]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12239])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12239) (a := (20881049128743 / 25000000000000 : ℝ)) (b := (168377977637 / 100000000000000 : ℝ)) (q := (2313057218343 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12239])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12239])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12239]

theorem cert12239_17 : CellCertificate 12239 (900035280219407 / 10000000000000000 : ℝ) (171620956214257 / 100000000000000000 : ℝ) (346989643495939 / 10000000000000000 : ℝ)
    (cell12239 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · have h := gap_lower (n := 12239) (a := (41744733877669 / 50000000000000 : ℝ)) (b := (168377977637 / 100000000000000 : ℝ)) (q := (115653059163 / 5000000000000 : ℝ))
      (E := (cell12239 ⟨17, by decide⟩).energy) (xi := (346989643495939 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12239 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12239]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12239])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12239) (a := (41744733877669 / 50000000000000 : ℝ)) (b := (168377977637 / 100000000000000 : ℝ)) (q := (115653059163 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12239])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12239])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12239]

theorem cert12239_18 : CellCertificate 12239 (900035280219407 / 10000000000000000 : ℝ) (171620956214257 / 100000000000000000 : ℝ) (346989643495939 / 10000000000000000 : ℝ)
    (cell12239 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · have h := gap_lower (n := 12239) (a := (83454763576287 / 100000000000000 : ℝ)) (b := (168377977637 / 100000000000000 : ℝ)) (q := (462613033887 / 20000000000000 : ℝ))
      (E := (cell12239 ⟨18, by decide⟩).energy) (xi := (346989643495939 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12239 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12239]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12239])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12239) (a := (83454763576287 / 100000000000000 : ℝ)) (b := (168377977637 / 100000000000000 : ℝ)) (q := (462613033887 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12239])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12239])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12239]

theorem cert12239_19 : CellCertificate 12239 (900035280219407 / 10000000000000000 : ℝ) (171620956214257 / 100000000000000000 : ℝ) (346989643495939 / 10000000000000000 : ℝ)
    (cell12239 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · have h := gap_lower (n := 12239) (a := (83420083943821 / 100000000000000 : ℝ)) (b := (168377977637 / 100000000000000 : ℝ)) (q := (92522767299 / 4000000000000 : ℝ))
      (E := (cell12239 ⟨19, by decide⟩).energy) (xi := (346989643495939 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12239 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12239]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12239])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12239) (a := (83420083943821 / 100000000000000 : ℝ)) (b := (168377977637 / 100000000000000 : ℝ)) (q := (92522767299 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12239])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12239])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12239]

theorem cert12240_0 : CellCertificate 12240 (900005286227463 / 10000000000000000 : ℝ) (343213860222017 / 200000000000000000 : ℝ) (69392106526107 / 2000000000000000 : ℝ)
    (cell12240 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · have h := gap_lower (n := 12240) (a := (42041605889857 / 50000000000000 : ℝ)) (b := (1346912291 / 800000000000 : ℝ)) (q := (1156422600431 / 50000000000000 : ℝ))
      (E := (cell12240 ⟨0, by decide⟩).energy) (xi := (69392106526107 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12240 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12240]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12240])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12240) (a := (42041605889857 / 50000000000000 : ℝ)) (b := (1346912291 / 800000000000 : ℝ)) (q := (1156422600431 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12240])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12240])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12240]

theorem cert12240_1 : CellCertificate 12240 (900005286227463 / 10000000000000000 : ℝ) (343213860222017 / 200000000000000000 : ℝ) (69392106526107 / 2000000000000000 : ℝ)
    (cell12240 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · have h := gap_lower (n := 12240) (a := (21012021324447 / 25000000000000 : ℝ)) (b := (1346912291 / 800000000000 : ℝ)) (q := (2312849149067 / 100000000000000 : ℝ))
      (E := (cell12240 ⟨1, by decide⟩).energy) (xi := (69392106526107 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12240 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12240]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12240])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12240) (a := (21012021324447 / 25000000000000 : ℝ)) (b := (1346912291 / 800000000000 : ℝ)) (q := (2312849149067 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12240])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12240])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12240]

theorem cert12240_2 : CellCertificate 12240 (900005286227463 / 10000000000000000 : ℝ) (343213860222017 / 200000000000000000 : ℝ) (69392106526107 / 2000000000000000 : ℝ)
    (cell12240 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · have h := gap_lower (n := 12240) (a := (16802596792967 / 20000000000000 : ℝ)) (b := (1346912291 / 800000000000 : ℝ)) (q := (2312853168579 / 100000000000000 : ℝ))
      (E := (cell12240 ⟨2, by decide⟩).energy) (xi := (69392106526107 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12240 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12240]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12240])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12240) (a := (16802596792967 / 20000000000000 : ℝ)) (b := (1346912291 / 800000000000 : ℝ)) (q := (2312853168579 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12240])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12240])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12240]

theorem cert12240_3 : CellCertificate 12240 (900005286227463 / 10000000000000000 : ℝ) (343213860222017 / 200000000000000000 : ℝ) (69392106526107 / 2000000000000000 : ℝ)
    (cell12240 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · have h := gap_lower (n := 12240) (a := (41988953871939 / 50000000000000 : ℝ)) (b := (1346912291 / 800000000000 : ℝ)) (q := (578214288399 / 25000000000000 : ℝ))
      (E := (cell12240 ⟨3, by decide⟩).energy) (xi := (69392106526107 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12240 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12240]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12240])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12240) (a := (41988953871939 / 50000000000000 : ℝ)) (b := (1346912291 / 800000000000 : ℝ)) (q := (578214288399 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12240])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12240])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12240]

theorem cert12240_4 : CellCertificate 12240 (900005286227463 / 10000000000000000 : ℝ) (343213860222017 / 200000000000000000 : ℝ) (69392106526107 / 2000000000000000 : ℝ)
    (cell12240 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · have h := gap_lower (n := 12240) (a := (83942856598137 / 100000000000000 : ℝ)) (b := (1346912291 / 800000000000 : ℝ)) (q := (1156430556787 / 50000000000000 : ℝ))
      (E := (cell12240 ⟨4, by decide⟩).energy) (xi := (69392106526107 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12240 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12240]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12240])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12240) (a := (83942856598137 / 100000000000000 : ℝ)) (b := (1346912291 / 800000000000 : ℝ)) (q := (1156430556787 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12240])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12240])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12240]

theorem cert12240_5 : CellCertificate 12240 (900005286227463 / 10000000000000000 : ℝ) (343213860222017 / 200000000000000000 : ℝ) (69392106526107 / 2000000000000000 : ℝ)
    (cell12240 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · have h := gap_lower (n := 12240) (a := (41953915245511 / 50000000000000 : ℝ)) (b := (1346912291 / 800000000000 : ℝ)) (q := (289108139449 / 12500000000000 : ℝ))
      (E := (cell12240 ⟨5, by decide⟩).energy) (xi := (69392106526107 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12240 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12240]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12240])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12240) (a := (41953915245511 / 50000000000000 : ℝ)) (b := (1346912291 / 800000000000 : ℝ)) (q := (289108139449 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12240])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12240])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12240]

theorem cert12240_6 : CellCertificate 12240 (900005286227463 / 10000000000000000 : ℝ) (343213860222017 / 200000000000000000 : ℝ) (69392106526107 / 2000000000000000 : ℝ)
    (cell12240 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · have h := gap_lower (n := 12240) (a := (41936414693071 / 50000000000000 : ℝ)) (b := (1346912291 / 800000000000 : ℝ)) (q := (2312869110753 / 100000000000000 : ℝ))
      (E := (cell12240 ⟨6, by decide⟩).energy) (xi := (69392106526107 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12240 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12240]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12240])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12240) (a := (41936414693071 / 50000000000000 : ℝ)) (b := (1346912291 / 800000000000 : ℝ)) (q := (2312869110753 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12240])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12240])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12240]

theorem cert12240_7 : CellCertificate 12240 (900005286227463 / 10000000000000000 : ℝ) (343213860222017 / 200000000000000000 : ℝ) (69392106526107 / 2000000000000000 : ℝ)
    (cell12240 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · have h := gap_lower (n := 12240) (a := (20959463311823 / 25000000000000 : ℝ)) (b := (1346912291 / 800000000000 : ℝ)) (q := (115643655387 / 5000000000000 : ℝ))
      (E := (cell12240 ⟨7, by decide⟩).energy) (xi := (69392106526107 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12240 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12240]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12240])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12240) (a := (20959463311823 / 25000000000000 : ℝ)) (b := (1346912291 / 800000000000 : ℝ)) (q := (115643655387 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12240])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12240])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12240]

theorem cert12240_8 : CellCertificate 12240 (900005286227463 / 10000000000000000 : ℝ) (343213860222017 / 200000000000000000 : ℝ) (69392106526107 / 2000000000000000 : ℝ)
    (cell12240 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · have h := gap_lower (n := 12240) (a := (41901451019231 / 50000000000000 : ℝ)) (b := (1346912291 / 800000000000 : ℝ)) (q := (92515084599 / 4000000000000 : ℝ))
      (E := (cell12240 ⟨8, by decide⟩).energy) (xi := (69392106526107 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12240 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12240]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12240])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12240) (a := (41901451019231 / 50000000000000 : ℝ)) (b := (1346912291 / 800000000000 : ℝ)) (q := (92515084599 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12240])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12240])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12240]

theorem cert12240_9 : CellCertificate 12240 (900005286227463 / 10000000000000000 : ℝ) (343213860222017 / 200000000000000000 : ℝ) (69392106526107 / 2000000000000000 : ℝ)
    (cell12240 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · have h := gap_lower (n := 12240) (a := (8376797572383 / 10000000000000 : ℝ)) (b := (1346912291 / 800000000000 : ℝ)) (q := (578220270663 / 25000000000000 : ℝ))
      (E := (cell12240 ⟨9, by decide⟩).energy) (xi := (69392106526107 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12240 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12240]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12240])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12240) (a := (8376797572383 / 10000000000000 : ℝ)) (b := (1346912291 / 800000000000 : ℝ)) (q := (578220270663 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12240])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12240])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12240]

theorem cert12240_10 : CellCertificate 12240 (900005286227463 / 10000000000000000 : ℝ) (343213860222017 / 200000000000000000 : ℝ) (69392106526107 / 2000000000000000 : ℝ)
    (cell12240 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · have h := gap_lower (n := 12240) (a := (1046663428347 / 1250000000000 : ℝ)) (b := (1346912291 / 800000000000 : ℝ)) (q := (2312885076611 / 100000000000000 : ℝ))
      (E := (cell12240 ⟨10, by decide⟩).energy) (xi := (69392106526107 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12240 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12240]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12240])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12240) (a := (1046663428347 / 1250000000000 : ℝ)) (b := (1346912291 / 800000000000 : ℝ)) (q := (2312885076611 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12240])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12240])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12240]

theorem cert12240_11 : CellCertificate 12240 (900005286227463 / 10000000000000000 : ℝ) (343213860222017 / 200000000000000000 : ℝ) (69392106526107 / 2000000000000000 : ℝ)
    (cell12240 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · have h := gap_lower (n := 12240) (a := (83698197634807 / 100000000000000 : ℝ)) (b := (1346912291 / 800000000000 : ℝ)) (q := (231288910451 / 10000000000000 : ℝ))
      (E := (cell12240 ⟨11, by decide⟩).energy) (xi := (69392106526107 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12240 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12240]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12240])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12240) (a := (83698197634807 / 100000000000000 : ℝ)) (b := (1346912291 / 800000000000 : ℝ)) (q := (231288910451 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12240])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12240])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12240]

theorem cert12240_12 : CellCertificate 12240 (900005286227463 / 10000000000000000 : ℝ) (343213860222017 / 200000000000000000 : ℝ) (69392106526107 / 2000000000000000 : ℝ)
    (cell12240 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · have h := gap_lower (n := 12240) (a := (20915836447427 / 25000000000000 : ℝ)) (b := (1346912291 / 800000000000 : ℝ)) (q := (289111632209 / 12500000000000 : ℝ))
      (E := (cell12240 ⟨12, by decide⟩).energy) (xi := (69392106526107 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12240 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12240]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12240])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12240) (a := (20915836447427 / 25000000000000 : ℝ)) (b := (1346912291 / 800000000000 : ℝ)) (q := (289111632209 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12240])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12240])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12240]

theorem cert12240_13 : CellCertificate 12240 (900005286227463 / 10000000000000000 : ℝ) (343213860222017 / 200000000000000000 : ℝ) (69392106526107 / 2000000000000000 : ℝ)
    (cell12240 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · have h := gap_lower (n := 12240) (a := (41814259348693 / 50000000000000 : ℝ)) (b := (1346912291 / 800000000000 : ℝ)) (q := (462579411849 / 20000000000000 : ℝ))
      (E := (cell12240 ⟨13, by decide⟩).energy) (xi := (69392106526107 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12240 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12240]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12240])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12240) (a := (41814259348693 / 50000000000000 : ℝ)) (b := (1346912291 / 800000000000 : ℝ)) (q := (462579411849 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12240])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12240])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12240]

theorem cert12240_14 : CellCertificate 12240 (900005286227463 / 10000000000000000 : ℝ) (343213860222017 / 200000000000000000 : ℝ) (69392106526107 / 2000000000000000 : ℝ)
    (cell12240 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · have h := gap_lower (n := 12240) (a := (20898429080737 / 25000000000000 : ℝ)) (b := (1346912291 / 800000000000 : ℝ)) (q := (2312901058043 / 100000000000000 : ℝ))
      (E := (cell12240 ⟨14, by decide⟩).energy) (xi := (69392106526107 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12240 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12240]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12240])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12240) (a := (20898429080737 / 25000000000000 : ℝ)) (b := (1346912291 / 800000000000 : ℝ)) (q := (2312901058043 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12240])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12240])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12240]

theorem cert12240_15 : CellCertificate 12240 (900005286227463 / 10000000000000000 : ℝ) (343213860222017 / 200000000000000000 : ℝ) (69392106526107 / 2000000000000000 : ℝ)
    (cell12240 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · have h := gap_lower (n := 12240) (a := (83558938631681 / 100000000000000 : ℝ)) (b := (1346912291 / 800000000000 : ℝ)) (q := (144556566291 / 6250000000000 : ℝ))
      (E := (cell12240 ⟨15, by decide⟩).energy) (xi := (69392106526107 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12240 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12240]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12240])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12240) (a := (83558938631681 / 100000000000000 : ℝ)) (b := (1346912291 / 800000000000 : ℝ)) (q := (144556566291 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12240])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12240])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12240]

theorem cert12240_16 : CellCertificate 12240 (900005286227463 / 10000000000000000 : ℝ) (343213860222017 / 200000000000000000 : ℝ) (69392106526107 / 2000000000000000 : ℝ)
    (cell12240 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · have h := gap_lower (n := 12240) (a := (16704837117811 / 20000000000000 : ℝ)) (b := (1346912291 / 800000000000 : ℝ)) (q := (1156454507643 / 50000000000000 : ℝ))
      (E := (cell12240 ⟨16, by decide⟩).energy) (xi := (69392106526107 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12240 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12240]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12240])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12240) (a := (16704837117811 / 20000000000000 : ℝ)) (b := (1346912291 / 800000000000 : ℝ)) (q := (1156454507643 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12240])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12240])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12240]

theorem cert12240_17 : CellCertificate 12240 (900005286227463 / 10000000000000000 : ℝ) (343213860222017 / 200000000000000000 : ℝ) (69392106526107 / 2000000000000000 : ℝ)
    (cell12240 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · have h := gap_lower (n := 12240) (a := (83489457160719 / 100000000000000 : ℝ)) (b := (1346912291 / 800000000000 : ℝ)) (q := (1156456522137 / 50000000000000 : ℝ))
      (E := (cell12240 ⟨17, by decide⟩).energy) (xi := (69392106526107 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12240 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12240]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12240])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12240) (a := (83489457160719 / 100000000000000 : ℝ)) (b := (1346912291 / 800000000000 : ℝ)) (q := (1156456522137 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12240])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12240])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12240]

theorem cert12240_18 : CellCertificate 12240 (900005286227463 / 10000000000000000 : ℝ) (343213860222017 / 200000000000000000 : ℝ) (69392106526107 / 2000000000000000 : ℝ)
    (cell12240 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · have h := gap_lower (n := 12240) (a := (83454753312499 / 100000000000000 : ℝ)) (b := (1346912291 / 800000000000 : ℝ)) (q := (2312917037173 / 100000000000000 : ℝ))
      (E := (cell12240 ⟨18, by decide⟩).energy) (xi := (69392106526107 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12240 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12240]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12240])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12240) (a := (83454753312499 / 100000000000000 : ℝ)) (b := (1346912291 / 800000000000 : ℝ)) (q := (2312917037173 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12240])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12240])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12240]

theorem cert12240_19 : CellCertificate 12240 (900005286227463 / 10000000000000000 : ℝ) (343213860222017 / 200000000000000000 : ℝ) (69392106526107 / 2000000000000000 : ℝ)
    (cell12240 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · have h := gap_lower (n := 12240) (a := (83420074010401 / 100000000000000 : ℝ)) (b := (1346912291 / 800000000000 : ℝ)) (q := (578230249879 / 25000000000000 : ℝ))
      (E := (cell12240 ⟨19, by decide⟩).energy) (xi := (69392106526107 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12240 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12240]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12240])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12240) (a := (83420074010401 / 100000000000000 : ℝ)) (b := (1346912291 / 800000000000 : ℝ)) (q := (578230249879 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12240])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12240])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12240]

theorem cert12241_0 : CellCertificate 12241 (449987648479099 / 5000000000000000 : ℝ) (1715929063002011 / 1000000000000000000 : ℝ) (346931426776877 / 10000000000000000 : ℝ)
    (cell12241 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · have h := gap_lower (n := 12241) (a := (84083195491659 / 100000000000000 : ℝ)) (b := (168350097453 / 100000000000000 : ℝ)) (q := (1156348531691 / 50000000000000 : ℝ))
      (E := (cell12241 ⟨0, by decide⟩).energy) (xi := (346931426776877 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12241 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12241]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12241])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12241) (a := (84083195491659 / 100000000000000 : ℝ)) (b := (168350097453 / 100000000000000 : ℝ)) (q := (1156348531691 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12241])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12241])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12241]

theorem cert12241_1 : CellCertificate 12241 (449987648479099 / 5000000000000000 : ℝ) (1715929063002011 / 1000000000000000000 : ℝ) (346931426776877 / 10000000000000000 : ℝ)
    (cell12241 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · have h := gap_lower (n := 12241) (a := (84048069348563 / 100000000000000 : ℝ)) (b := (168350097453 / 100000000000000 : ℝ)) (q := (2312701062631 / 100000000000000 : ℝ))
      (E := (cell12241 ⟨1, by decide⟩).energy) (xi := (346931426776877 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12241 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12241]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12241])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12241) (a := (84048069348563 / 100000000000000 : ℝ)) (b := (168350097453 / 100000000000000 : ℝ)) (q := (2312701062631 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12241])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12241])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12241]

theorem cert12241_2 : CellCertificate 12241 (449987648479099 / 5000000000000000 : ℝ) (1715929063002011 / 1000000000000000000 : ℝ) (346931426776877 / 10000000000000000 : ℝ)
    (cell12241 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · have h := gap_lower (n := 12241) (a := (84012968353959 / 100000000000000 : ℝ)) (b := (168350097453 / 100000000000000 : ℝ)) (q := (578176269057 / 25000000000000 : ℝ))
      (E := (cell12241 ⟨2, by decide⟩).energy) (xi := (346931426776877 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12241 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12241]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12241])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12241) (a := (84012968353959 / 100000000000000 : ℝ)) (b := (168350097453 / 100000000000000 : ℝ)) (q := (578176269057 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12241])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12241])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12241]

theorem cert12241_3 : CellCertificate 12241 (449987648479099 / 5000000000000000 : ℝ) (1715929063002011 / 1000000000000000000 : ℝ) (346931426776877 / 10000000000000000 : ℝ)
    (cell12241 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · have h := gap_lower (n := 12241) (a := (10497236558859 / 12500000000000 : ℝ)) (b := (168350097453 / 100000000000000 : ℝ)) (q := (231270905613 / 10000000000000 : ℝ))
      (E := (cell12241 ⟨3, by decide⟩).energy) (xi := (346931426776877 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12241 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12241]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12241])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12241) (a := (10497236558859 / 12500000000000 : ℝ)) (b := (168350097453 / 100000000000000 : ℝ)) (q := (231270905613 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12241])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12241])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12241]

theorem cert12241_4 : CellCertificate 12241 (449987648479099 / 5000000000000000 : ℝ) (1715929063002011 / 1000000000000000000 : ℝ) (346931426776877 / 10000000000000000 : ℝ)
    (cell12241 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · have h := gap_lower (n := 12241) (a := (2098571041563 / 2500000000000 : ℝ)) (b := (168350097453 / 100000000000000 : ℝ)) (q := (2312713069651 / 100000000000000 : ℝ))
      (E := (cell12241 ⟨4, by decide⟩).energy) (xi := (346931426776877 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12241 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12241]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12241])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12241) (a := (2098571041563 / 2500000000000 : ℝ)) (b := (168350097453 / 100000000000000 : ℝ)) (q := (2312713069651 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12241])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12241])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12241]

theorem cert12241_5 : CellCertificate 12241 (449987648479099 / 5000000000000000 : ℝ) (1715929063002011 / 1000000000000000000 : ℝ) (346931426776877 / 10000000000000000 : ℝ)
    (cell12241 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · have h := gap_lower (n := 12241) (a := (41953907946159 / 50000000000000 : ℝ)) (b := (168350097453 / 100000000000000 : ℝ)) (q := (1156358534089 / 50000000000000 : ℝ))
      (E := (cell12241 ⟨5, by decide⟩).energy) (xi := (346931426776877 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12241 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12241]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12241])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12241) (a := (41953907946159 / 50000000000000 : ℝ)) (b := (168350097453 / 100000000000000 : ℝ)) (q := (1156358534089 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12241])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12241])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12241]

theorem cert12241_6 : CellCertificate 12241 (449987648479099 / 5000000000000000 : ℝ) (1715929063002011 / 1000000000000000000 : ℝ) (346931426776877 / 10000000000000000 : ℝ)
    (cell12241 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · have h := gap_lower (n := 12241) (a := (2621025472621 / 3125000000000 : ℝ)) (b := (168350097453 / 100000000000000 : ℝ)) (q := (289090132581 / 12500000000000 : ℝ))
      (E := (cell12241 ⟨6, by decide⟩).energy) (xi := (346931426776877 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12241 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12241]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12241])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12241) (a := (2621025472621 / 3125000000000 : ℝ)) (b := (168350097453 / 100000000000000 : ℝ)) (q := (289090132581 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12241])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12241])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12241]

theorem cert12241_7 : CellCertificate 12241 (449987648479099 / 5000000000000000 : ℝ) (1715929063002011 / 1000000000000000000 : ℝ) (346931426776877 / 10000000000000000 : ℝ)
    (cell12241 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · have h := gap_lower (n := 12241) (a := (83837839320981 / 100000000000000 : ℝ)) (b := (168350097453 / 100000000000000 : ℝ)) (q := (289090624727 / 12500000000000 : ℝ))
      (E := (cell12241 ⟨7, by decide⟩).energy) (xi := (346931426776877 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12241 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12241]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12241])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12241) (a := (83837839320981 / 100000000000000 : ℝ)) (b := (168350097453 / 100000000000000 : ℝ)) (q := (289090624727 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12241])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12241])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12241]

theorem cert12241_8 : CellCertificate 12241 (449987648479099 / 5000000000000000 : ℝ) (1715929063002011 / 1000000000000000000 : ℝ) (346931426776877 / 10000000000000000 : ℝ)
    (cell12241 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · have h := gap_lower (n := 12241) (a := (16760577689527 / 20000000000000 : ℝ)) (b := (168350097453 / 100000000000000 : ℝ)) (q := (231272900393 / 10000000000000 : ℝ))
      (E := (cell12241 ⟨8, by decide⟩).energy) (xi := (346931426776877 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12241 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12241]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12241])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12241) (a := (16760577689527 / 20000000000000 : ℝ)) (b := (168350097453 / 100000000000000 : ℝ)) (q := (231272900393 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12241])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12241])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12241]

theorem cert12241_9 : CellCertificate 12241 (449987648479099 / 5000000000000000 : ℝ) (1715929063002011 / 1000000000000000000 : ℝ) (346931426776877 / 10000000000000000 : ℝ)
    (cell12241 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · have h := gap_lower (n := 12241) (a := (83767962468013 / 100000000000000 : ℝ)) (b := (168350097453 / 100000000000000 : ℝ)) (q := (2312733029253 / 100000000000000 : ℝ))
      (E := (cell12241 ⟨9, by decide⟩).energy) (xi := (346931426776877 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12241 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12241]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12241])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12241) (a := (83767962468013 / 100000000000000 : ℝ)) (b := (168350097453 / 100000000000000 : ℝ)) (q := (2312733029253 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12241])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12241])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12241]

theorem cert12241_10 : CellCertificate 12241 (449987648479099 / 5000000000000000 : ℝ) (1715929063002011 / 1000000000000000000 : ℝ) (346931426776877 / 10000000000000000 : ℝ)
    (cell12241 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · have h := gap_lower (n := 12241) (a := (83733061346481 / 100000000000000 : ℝ)) (b := (168350097453 / 100000000000000 : ℝ)) (q := (289092127963 / 12500000000000 : ℝ))
      (E := (cell12241 ⟨10, by decide⟩).energy) (xi := (346931426776877 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12241 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12241]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12241])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12241) (a := (83733061346481 / 100000000000000 : ℝ)) (b := (168350097453 / 100000000000000 : ℝ)) (q := (289092127963 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12241])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12241])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12241]

theorem cert12241_11 : CellCertificate 12241 (449987648479099 / 5000000000000000 : ℝ) (1715929063002011 / 1000000000000000000 : ℝ) (346931426776877 / 10000000000000000 : ℝ)
    (cell12241 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · have h := gap_lower (n := 12241) (a := (41849092523797 / 50000000000000 : ℝ)) (b := (168350097453 / 100000000000000 : ℝ)) (q := (2312740994869 / 100000000000000 : ℝ))
      (E := (cell12241 ⟨11, by decide⟩).energy) (xi := (346931426776877 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12241 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12241]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12241])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12241) (a := (41849092523797 / 50000000000000 : ℝ)) (b := (168350097453 / 100000000000000 : ℝ)) (q := (2312740994869 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12241])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12241])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12241]

theorem cert12241_12 : CellCertificate 12241 (449987648479099 / 5000000000000000 : ℝ) (1715929063002011 / 1000000000000000000 : ℝ) (346931426776877 / 10000000000000000 : ℝ)
    (cell12241 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · have h := gap_lower (n := 12241) (a := (83663333536089 / 100000000000000 : ℝ)) (b := (168350097453 / 100000000000000 : ℝ)) (q := (2312745008129 / 100000000000000 : ℝ))
      (E := (cell12241 ⟨12, by decide⟩).energy) (xi := (346931426776877 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12241 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12241]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12241])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12241) (a := (83663333536089 / 100000000000000 : ℝ)) (b := (168350097453 / 100000000000000 : ℝ)) (q := (2312745008129 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12241])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12241])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12241]

theorem cert12241_13 : CellCertificate 12241 (449987648479099 / 5000000000000000 : ℝ) (1715929063002011 / 1000000000000000000 : ℝ) (346931426776877 / 10000000000000000 : ℝ)
    (cell12241 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · have h := gap_lower (n := 12241) (a := (83628506776893 / 100000000000000 : ℝ)) (b := (168350097453 / 100000000000000 : ℝ)) (q := (289093619313 / 12500000000000 : ℝ))
      (E := (cell12241 ⟨13, by decide⟩).energy) (xi := (346931426776877 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12241 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12241]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12241])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12241) (a := (83628506776893 / 100000000000000 : ℝ)) (b := (168350097453 / 100000000000000 : ℝ)) (q := (289093619313 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12241])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12241])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12241]

theorem cert12241_14 : CellCertificate 12241 (449987648479099 / 5000000000000000 : ℝ) (1715929063002011 / 1000000000000000000 : ℝ) (346931426776877 / 10000000000000000 : ℝ)
    (cell12241 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · have h := gap_lower (n := 12241) (a := (8359370473511 / 10000000000000 : ℝ)) (b := (168350097453 / 100000000000000 : ℝ)) (q := (115637647847 / 5000000000000 : ℝ))
      (E := (cell12241 ⟨14, by decide⟩).energy) (xi := (346931426776877 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12241 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12241]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12241])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12241) (a := (8359370473511 / 10000000000000 : ℝ)) (b := (168350097453 / 100000000000000 : ℝ)) (q := (115637647847 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12241])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12241])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12241]

theorem cert12241_15 : CellCertificate 12241 (449987648479099 / 5000000000000000 : ℝ) (1715929063002011 / 1000000000000000000 : ℝ) (346931426776877 / 10000000000000000 : ℝ)
    (cell12241 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · have h := gap_lower (n := 12241) (a := (2611216480501 / 3125000000000 : ℝ)) (b := (168350097453 / 100000000000000 : ℝ)) (q := (2312756963979 / 100000000000000 : ℝ))
      (E := (cell12241 ⟨15, by decide⟩).energy) (xi := (346931426776877 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12241 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12241]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12241])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12241) (a := (2611216480501 / 3125000000000 : ℝ)) (b := (168350097453 / 100000000000000 : ℝ)) (q := (2312756963979 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12241])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12241])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12241]

theorem cert12241_16 : CellCertificate 12241 (449987648479099 / 5000000000000000 : ℝ) (1715929063002011 / 1000000000000000000 : ℝ) (346931426776877 / 10000000000000000 : ℝ)
    (cell12241 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · have h := gap_lower (n := 12241) (a := (83524174665127 / 100000000000000 : ℝ)) (b := (168350097453 / 100000000000000 : ℝ)) (q := (144547557739 / 6250000000000 : ℝ))
      (E := (cell12241 ⟨16, by decide⟩).energy) (xi := (346931426776877 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12241 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12241]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12241])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12241) (a := (83524174665127 / 100000000000000 : ℝ)) (b := (168350097453 / 100000000000000 : ℝ)) (q := (144547557739 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12241])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12241])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12241]

theorem cert12241_17 : CellCertificate 12241 (449987648479099 / 5000000000000000 : ℝ) (1715929063002011 / 1000000000000000000 : ℝ) (346931426776877 / 10000000000000000 : ℝ)
    (cell12241 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · have h := gap_lower (n := 12241) (a := (16697889313609 / 20000000000000 : ℝ)) (b := (168350097453 / 100000000000000 : ℝ)) (q := (72273904963 / 3125000000000 : ℝ))
      (E := (cell12241 ⟨17, by decide⟩).energy) (xi := (346931426776877 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12241 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12241]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12241])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12241) (a := (16697889313609 / 20000000000000 : ℝ)) (b := (168350097453 / 100000000000000 : ℝ)) (q := (72273904963 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12241])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12241])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12241]

theorem cert12241_18 : CellCertificate 12241 (449987648479099 / 5000000000000000 : ℝ) (1715929063002011 / 1000000000000000000 : ℝ) (346931426776877 / 10000000000000000 : ℝ)
    (cell12241 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · have h := gap_lower (n := 12241) (a := (10431842881327 / 12500000000000 : ℝ)) (b := (168350097453 / 100000000000000 : ℝ)) (q := (289096119813 / 12500000000000 : ℝ))
      (E := (cell12241 ⟨18, by decide⟩).energy) (xi := (346931426776877 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12241 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12241]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12241])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12241) (a := (10431842881327 / 12500000000000 : ℝ)) (b := (168350097453 / 100000000000000 : ℝ)) (q := (289096119813 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12241])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12241])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12241]

theorem cert12241_19 : CellCertificate 12241 (449987648479099 / 5000000000000000 : ℝ) (1715929063002011 / 1000000000000000000 : ℝ) (346931426776877 / 10000000000000000 : ℝ)
    (cell12241 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · have h := gap_lower (n := 12241) (a := (16684012815769 / 20000000000000 : ℝ)) (b := (168350097453 / 100000000000000 : ℝ)) (q := (2312772928421 / 100000000000000 : ℝ))
      (E := (cell12241 ⟨19, by decide⟩).energy) (xi := (346931426776877 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12241 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12241]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12241])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12241) (a := (16684012815769 / 20000000000000 : ℝ)) (b := (168350097453 / 100000000000000 : ℝ)) (q := (2312772928421 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12241])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12241])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12241]

theorem cert12242_0 : CellCertificate 12242 (899945312410443 / 10000000000000000 : ℝ) (1715788847812729 / 1000000000000000000 : ℝ) (346902325933491 / 10000000000000000 : ℝ)
    (cell12242 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · have h := gap_lower (n := 12242) (a := (21020794801567 / 25000000000000 : ℝ)) (b := (16833616087 / 10000000000000 : ℝ)) (q := (1156274546907 / 50000000000000 : ℝ))
      (E := (cell12242 ⟨0, by decide⟩).energy) (xi := (346902325933491 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12242 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12242]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12242])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12242) (a := (21020794801567 / 25000000000000 : ℝ)) (b := (16833616087 / 10000000000000 : ℝ)) (q := (1156274546907 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12242])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12242])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12242]

theorem cert12242_1 : CellCertificate 12242 (899945312410443 / 10000000000000000 : ℝ) (1715788847812729 / 1000000000000000000 : ℝ) (346902325933491 / 10000000000000000 : ℝ)
    (cell12242 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · have h := gap_lower (n := 12242) (a := (84048053401959 / 100000000000000 : ℝ)) (b := (16833616087 / 10000000000000 : ℝ)) (q := (2312553086437 / 100000000000000 : ℝ))
      (E := (cell12242 ⟨1, by decide⟩).energy) (xi := (346902325933491 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12242 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12242]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12242])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12242) (a := (84048053401959 / 100000000000000 : ℝ)) (b := (16833616087 / 10000000000000 : ℝ)) (q := (2312553086437 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12242])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12242])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12242]

theorem cert12242_2 : CellCertificate 12242 (899945312410443 / 10000000000000000 : ℝ) (1715788847812729 / 1000000000000000000 : ℝ) (346902325933491 / 10000000000000000 : ℝ)
    (cell12242 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · have h := gap_lower (n := 12242) (a := (42006476372831 / 50000000000000 : ℝ)) (b := (16833616087 / 10000000000000 : ℝ)) (q := (2312557094209 / 100000000000000 : ℝ))
      (E := (cell12242 ⟨2, by decide⟩).energy) (xi := (346902325933491 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12242 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12242]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12242])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12242) (a := (42006476372831 / 50000000000000 : ℝ)) (b := (16833616087 / 10000000000000 : ℝ)) (q := (2312557094209 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12242])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12242])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12242]

theorem cert12242_3 : CellCertificate 12242 (899945312410443 / 10000000000000000 : ℝ) (1715788847812729 / 1000000000000000000 : ℝ) (346902325933491 / 10000000000000000 : ℝ)
    (cell12242 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · have h := gap_lower (n := 12242) (a := (83977877200401 / 100000000000000 : ℝ)) (b := (16833616087 / 10000000000000 : ℝ)) (q := (2312561069089 / 100000000000000 : ℝ))
      (E := (cell12242 ⟨3, by decide⟩).energy) (xi := (346902325933491 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12242 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12242]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12242])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12242) (a := (83977877200401 / 100000000000000 : ℝ)) (b := (16833616087 / 10000000000000 : ℝ)) (q := (2312561069089 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12242])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12242])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12242]

theorem cert12242_4 : CellCertificate 12242 (899945312410443 / 10000000000000000 : ℝ) (1715788847812729 / 1000000000000000000 : ℝ) (346902325933491 / 10000000000000000 : ℝ)
    (cell12242 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · have h := gap_lower (n := 12242) (a := (83942826729397 / 100000000000000 : ℝ)) (b := (16833616087 / 10000000000000 : ℝ)) (q := (2312565078387 / 100000000000000 : ℝ))
      (E := (cell12242 ⟨4, by decide⟩).energy) (xi := (346902325933491 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12242 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12242]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12242])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12242) (a := (83942826729397 / 100000000000000 : ℝ)) (b := (16833616087 / 10000000000000 : ℝ)) (q := (2312565078387 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12242])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12242])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12242]

theorem cert12242_5 : CellCertificate 12242 (899945312410443 / 10000000000000000 : ℝ) (1715788847812729 / 1000000000000000000 : ℝ) (346902325933491 / 10000000000000000 : ℝ)
    (cell12242 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · have h := gap_lower (n := 12242) (a := (1311059395251 / 1562500000000 : ℝ)) (b := (16833616087 / 10000000000000 : ℝ)) (q := (2312569015613 / 100000000000000 : ℝ))
      (E := (cell12242 ⟨5, by decide⟩).energy) (xi := (346902325933491 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12242 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12242]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12242])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12242) (a := (1311059395251 / 1562500000000 : ℝ)) (b := (16833616087 / 10000000000000 : ℝ)) (q := (2312569015613 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12242])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12242])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12242]

theorem cert12242_6 : CellCertificate 12242 (899945312410443 / 10000000000000000 : ℝ) (1715788847812729 / 1000000000000000000 : ℝ) (346902325933491 / 10000000000000000 : ℝ)
    (cell12242 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · have h := gap_lower (n := 12242) (a := (83872800864011 / 100000000000000 : ℝ)) (b := (16833616087 / 10000000000000 : ℝ)) (q := (462514601087 / 20000000000000 : ℝ))
      (E := (cell12242 ⟨6, by decide⟩).energy) (xi := (346902325933491 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12242 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12242]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12242])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12242) (a := (83872800864011 / 100000000000000 : ℝ)) (b := (16833616087 / 10000000000000 : ℝ)) (q := (462514601087 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12242])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12242])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12242]

theorem cert12242_7 : CellCertificate 12242 (899945312410443 / 10000000000000000 : ℝ) (1715788847812729 / 1000000000000000000 : ℝ) (346902325933491 / 10000000000000000 : ℝ)
    (cell12242 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · have h := gap_lower (n := 12242) (a := (83837825397037 / 100000000000000 : ℝ)) (b := (16833616087 / 10000000000000 : ℝ)) (q := (2312576998677 / 100000000000000 : ℝ))
      (E := (cell12242 ⟨7, by decide⟩).energy) (xi := (346902325933491 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12242 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12242]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12242])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12242) (a := (83837825397037 / 100000000000000 : ℝ)) (b := (16833616087 / 10000000000000 : ℝ)) (q := (2312576998677 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12242])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12242])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12242]

theorem cert12242_8 : CellCertificate 12242 (899945312410443 / 10000000000000000 : ℝ) (1715788847812729 / 1000000000000000000 : ℝ) (346902325933491 / 10000000000000000 : ℝ)
    (cell12242 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · have h := gap_lower (n := 12242) (a := (83802874859133 / 100000000000000 : ℝ)) (b := (16833616087 / 10000000000000 : ℝ)) (q := (28907262547 / 1250000000000 : ℝ))
      (E := (cell12242 ⟨8, by decide⟩).energy) (xi := (346902325933491 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12242 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12242]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12242])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12242) (a := (83802874859133 / 100000000000000 : ℝ)) (b := (16833616087 / 10000000000000 : ℝ)) (q := (28907262547 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12242])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12242])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12242]

theorem cert12242_9 : CellCertificate 12242 (899945312410443 / 10000000000000000 : ℝ) (1715788847812729 / 1000000000000000000 : ℝ) (346902325933491 / 10000000000000000 : ℝ)
    (cell12242 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · have h := gap_lower (n := 12242) (a := (83767949214479 / 100000000000000 : ℝ)) (b := (16833616087 / 10000000000000 : ℝ)) (q := (144536564303 / 6250000000000 : ℝ))
      (E := (cell12242 ⟨9, by decide⟩).energy) (xi := (346902325933491 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12242 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12242]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12242])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12242) (a := (83767949214479 / 100000000000000 : ℝ)) (b := (16833616087 / 10000000000000 : ℝ)) (q := (144536564303 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12242])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12242])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12242]

theorem cert12242_10 : CellCertificate 12242 (899945312410443 / 10000000000000000 : ℝ) (1715788847812729 / 1000000000000000000 : ℝ) (346902325933491 / 10000000000000000 : ℝ)
    (cell12242 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · have h := gap_lower (n := 12242) (a := (41866524213721 / 50000000000000 : ℝ)) (b := (16833616087 / 10000000000000 : ℝ)) (q := (1156294511929 / 50000000000000 : ℝ))
      (E := (cell12242 ⟨10, by decide⟩).energy) (xi := (346902325933491 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12242 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12242]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12242])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12242) (a := (41866524213721 / 50000000000000 : ℝ)) (b := (16833616087 / 10000000000000 : ℝ)) (q := (1156294511929 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12242])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12242])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12242]

theorem cert12242_11 : CellCertificate 12242 (899945312410443 / 10000000000000000 : ℝ) (1715788847812729 / 1000000000000000000 : ℝ) (346902325933491 / 10000000000000000 : ℝ)
    (cell12242 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · have h := gap_lower (n := 12242) (a := (41849086231289 / 50000000000000 : ℝ)) (b := (16833616087 / 10000000000000 : ℝ)) (q := (289074124547 / 12500000000000 : ℝ))
      (E := (cell12242 ⟨11, by decide⟩).energy) (xi := (346902325933491 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12242 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12242]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12242])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12242) (a := (41849086231289 / 50000000000000 : ℝ)) (b := (16833616087 / 10000000000000 : ℝ)) (q := (289074124547 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12242])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12242])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12242]

theorem cert12242_12 : CellCertificate 12242 (899945312410443 / 10000000000000000 : ℝ) (1715788847812729 / 1000000000000000000 : ℝ) (346902325933491 / 10000000000000000 : ℝ)
    (cell12242 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · have h := gap_lower (n := 12242) (a := (41831660642313 / 50000000000000 : ℝ)) (b := (16833616087 / 10000000000000 : ℝ)) (q := (1156298476869 / 50000000000000 : ℝ))
      (E := (cell12242 ⟨12, by decide⟩).energy) (xi := (346902325933491 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12242 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12242]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12242])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12242) (a := (41831660642313 / 50000000000000 : ℝ)) (b := (16833616087 / 10000000000000 : ℝ)) (q := (1156298476869 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12242])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12242])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12242]

theorem cert12242_13 : CellCertificate 12242 (899945312410443 / 10000000000000000 : ℝ) (1715788847812729 / 1000000000000000000 : ℝ) (346902325933491 / 10000000000000000 : ℝ)
    (cell12242 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · have h := gap_lower (n := 12242) (a := (5226780928657 / 6250000000000 : ℝ)) (b := (16833616087 / 10000000000000 : ℝ)) (q := (578150240273 / 25000000000000 : ℝ))
      (E := (cell12242 ⟨13, by decide⟩).energy) (xi := (346902325933491 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12242 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12242]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12242])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12242) (a := (5226780928657 / 6250000000000 : ℝ)) (b := (16833616087 / 10000000000000 : ℝ)) (q := (578150240273 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12242])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12242])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12242]

theorem cert12242_14 : CellCertificate 12242 (899945312410443 / 10000000000000000 : ℝ) (1715788847812729 / 1000000000000000000 : ℝ) (346902325933491 / 10000000000000000 : ℝ)
    (cell12242 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · have h := gap_lower (n := 12242) (a := (2612302910917 / 3125000000000 : ℝ)) (b := (16833616087 / 10000000000000 : ℝ)) (q := (1156302483627 / 50000000000000 : ℝ))
      (E := (cell12242 ⟨14, by decide⟩).energy) (xi := (346902325933491 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12242 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12242]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12242])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12242) (a := (2612302910917 / 3125000000000 : ℝ)) (b := (16833616087 / 10000000000000 : ℝ)) (q := (1156302483627 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12242])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12242])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12242]

theorem cert12242_15 : CellCertificate 12242 (899945312410443 / 10000000000000000 : ℝ) (1715788847812729 / 1000000000000000000 : ℝ) (346902325933491 / 10000000000000000 : ℝ)
    (cell12242 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · have h := gap_lower (n := 12242) (a := (83558916122411 / 100000000000000 : ℝ)) (b := (16833616087 / 10000000000000 : ℝ)) (q := (231260897881 / 10000000000000 : ℝ))
      (E := (cell12242 ⟨15, by decide⟩).energy) (xi := (346902325933491 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12242 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12242]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12242])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12242) (a := (83558916122411 / 100000000000000 : ℝ)) (b := (16833616087 / 10000000000000 : ℝ)) (q := (231260897881 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12242])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12242])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12242]

theorem cert12242_16 : CellCertificate 12242 (899945312410443 / 10000000000000000 : ℝ) (1715788847812729 / 1000000000000000000 : ℝ) (346902325933491 / 10000000000000000 : ℝ)
    (cell12242 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · have h := gap_lower (n := 12242) (a := (41762081871593 / 50000000000000 : ℝ)) (b := (16833616087 / 10000000000000 : ℝ)) (q := (57815323599 / 2500000000000 : ℝ))
      (E := (cell12242 ⟨16, by decide⟩).energy) (xi := (346902325933491 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12242 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12242]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12242])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12242) (a := (41762081871593 / 50000000000000 : ℝ)) (b := (16833616087 / 10000000000000 : ℝ)) (q := (57815323599 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12242])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12242])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12242]

theorem cert12242_17 : CellCertificate 12242 (899945312410443 / 10000000000000000 : ℝ) (1715788847812729 / 1000000000000000000 : ℝ) (346902325933491 / 10000000000000000 : ℝ)
    (cell12242 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · have h := gap_lower (n := 12242) (a := (41744717988659 / 50000000000000 : ℝ)) (b := (16833616087 / 10000000000000 : ℝ)) (q := (578154231721 / 25000000000000 : ℝ))
      (E := (cell12242 ⟨17, by decide⟩).energy) (xi := (346902325933491 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12242 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12242]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12242])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12242) (a := (41744717988659 / 50000000000000 : ℝ)) (b := (16833616087 / 10000000000000 : ℝ)) (q := (578154231721 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12242])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12242])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12242]

theorem cert12242_18 : CellCertificate 12242 (899945312410443 / 10000000000000000 : ℝ) (1715788847812729 / 1000000000000000000 : ℝ) (346902325933491 / 10000000000000000 : ℝ)
    (cell12242 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · have h := gap_lower (n := 12242) (a := (83454732790637 / 100000000000000 : ℝ)) (b := (16833616087 / 10000000000000 : ℝ)) (q := (2312620933429 / 100000000000000 : ℝ))
      (E := (cell12242 ⟨18, by decide⟩).energy) (xi := (346902325933491 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12242 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12242]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12242])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12242) (a := (83454732790637 / 100000000000000 : ℝ)) (b := (16833616087 / 10000000000000 : ℝ)) (q := (2312620933429 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12242])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12242])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12242]

theorem cert12242_19 : CellCertificate 12242 (899945312410443 / 10000000000000000 : ℝ) (1715788847812729 / 1000000000000000000 : ℝ) (346902325933491 / 10000000000000000 : ℝ)
    (cell12242 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · have h := gap_lower (n := 12242) (a := (1668401082983 / 2000000000000 : ℝ)) (b := (16833616087 / 10000000000000 : ℝ)) (q := (578156227747 / 25000000000000 : ℝ))
      (E := (cell12242 ⟨19, by decide⟩).energy) (xi := (346902325933491 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12242 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12242]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12242])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12242) (a := (1668401082983 / 2000000000000 : ℝ)) (b := (16833616087 / 10000000000000 : ℝ)) (q := (578156227747 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12242])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12242])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12242]

theorem cert12243_0 : CellCertificate 12243 (899915332583033 / 10000000000000000 : ℝ) (857824327768311 / 500000000000000000 : ℝ) (346873230098909 / 10000000000000000 : ℝ)
    (cell12243 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · have h := gap_lower (n := 12243) (a := (84083162923541 / 100000000000000 : ℝ)) (b := (1346577813 / 800000000000 : ℝ)) (q := (1156200588319 / 50000000000000 : ℝ))
      (E := (cell12243 ⟨0, by decide⟩).energy) (xi := (346873230098909 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12243 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12243]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12243])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12243) (a := (84083162923541 / 100000000000000 : ℝ)) (b := (1346577813 / 800000000000 : ℝ)) (q := (1156200588319 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12243])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12243])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12243]

theorem cert12243_1 : CellCertificate 12243 (899915332583033 / 10000000000000000 : ℝ) (857824327768311 / 500000000000000000 : ℝ) (346873230098909 / 10000000000000000 : ℝ)
    (cell12243 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · have h := gap_lower (n := 12243) (a := (84048037457977 / 100000000000000 : ℝ)) (b := (1346577813 / 800000000000 : ℝ)) (q := (2312405162701 / 100000000000000 : ℝ))
      (E := (cell12243 ⟨1, by decide⟩).energy) (xi := (346873230098909 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12243 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12243]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12243])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12243) (a := (84048037457977 / 100000000000000 : ℝ)) (b := (1346577813 / 800000000000 : ℝ)) (q := (2312405162701 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12243])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12243])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12243]

theorem cert12243_2 : CellCertificate 12243 (899915332583033 / 10000000000000000 : ℝ) (857824327768311 / 500000000000000000 : ℝ) (346873230098909 / 10000000000000000 : ℝ)
    (cell12243 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · have h := gap_lower (n := 12243) (a := (10501617142493 / 12500000000000 : ℝ)) (b := (1346577813 / 800000000000 : ℝ)) (q := (2312409164717 / 100000000000000 : ℝ))
      (E := (cell12243 ⟨2, by decide⟩).energy) (xi := (346873230098909 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12243 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12243]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12243])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12243) (a := (10501617142493 / 12500000000000 : ℝ)) (b := (1346577813 / 800000000000 : ℝ)) (q := (2312409164717 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12243])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12243])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12243]

theorem cert12243_3 : CellCertificate 12243 (899915332583033 / 10000000000000000 : ℝ) (857824327768311 / 500000000000000000 : ℝ) (346873230098909 / 10000000000000000 : ℝ)
    (cell12243 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · have h := gap_lower (n := 12243) (a := (83977861932467 / 100000000000000 : ℝ)) (b := (1346577813 / 800000000000 : ℝ)) (q := (2312413134641 / 100000000000000 : ℝ))
      (E := (cell12243 ⟨3, by decide⟩).energy) (xi := (346873230098909 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12243 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12243]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12243])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12243) (a := (83977861932467 / 100000000000000 : ℝ)) (b := (1346577813 / 800000000000 : ℝ)) (q := (2312413134641 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12243])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12243])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12243]

theorem cert12243_4 : CellCertificate 12243 (899915332583033 / 10000000000000000 : ℝ) (857824327768311 / 500000000000000000 : ℝ) (346873230098909 / 10000000000000000 : ℝ)
    (cell12243 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · have h := gap_lower (n := 12243) (a := (83942811798767 / 100000000000000 : ℝ)) (b := (1346577813 / 800000000000 : ℝ)) (q := (462483427957 / 20000000000000 : ℝ))
      (E := (cell12243 ⟨4, by decide⟩).energy) (xi := (346873230098909 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12243 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12243]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12243])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12243) (a := (83942811798767 / 100000000000000 : ℝ)) (b := (1346577813 / 800000000000 : ℝ)) (q := (462483427957 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12243])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12243])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12243]

theorem cert12243_5 : CellCertificate 12243 (899915332583033 / 10000000000000000 : ℝ) (857824327768311 / 500000000000000000 : ℝ) (346873230098909 / 10000000000000000 : ℝ)
    (cell12243 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · have h := gap_lower (n := 12243) (a := (83907786702261 / 100000000000000 : ℝ)) (b := (1346577813 / 800000000000 : ℝ)) (q := (2312421131533 / 100000000000000 : ℝ))
      (E := (cell12243 ⟨5, by decide⟩).energy) (xi := (346873230098909 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12243 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12243]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12243])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12243) (a := (83907786702261 / 100000000000000 : ℝ)) (b := (1346577813 / 800000000000 : ℝ)) (q := (2312421131533 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12243])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12243])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12243]

theorem cert12243_6 : CellCertificate 12243 (899915332583033 / 10000000000000000 : ℝ) (857824327768311 / 500000000000000000 : ℝ) (346873230098909 / 10000000000000000 : ℝ)
    (cell12243 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · have h := gap_lower (n := 12243) (a := (41936393303279 / 50000000000000 : ℝ)) (b := (1346577813 / 800000000000 : ℝ)) (q := (2312425118821 / 100000000000000 : ℝ))
      (E := (cell12243 ⟨6, by decide⟩).energy) (xi := (346873230098909 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12243 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12243]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12243])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12243) (a := (41936393303279 / 50000000000000 : ℝ)) (b := (1346577813 / 800000000000 : ℝ)) (q := (2312425118821 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12243])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12243])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12243]

theorem cert12243_7 : CellCertificate 12243 (899915332583033 / 10000000000000000 : ℝ) (857824327768311 / 500000000000000000 : ℝ) (346873230098909 / 10000000000000000 : ℝ)
    (cell12243 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · have h := gap_lower (n := 12243) (a := (41918905737729 / 50000000000000 : ℝ)) (b := (1346577813 / 800000000000 : ℝ)) (q := (2312429110327 / 100000000000000 : ℝ))
      (E := (cell12243 ⟨7, by decide⟩).energy) (xi := (346873230098909 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12243 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12243]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12243])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12243) (a := (41918905737729 / 50000000000000 : ℝ)) (b := (1346577813 / 800000000000 : ℝ)) (q := (2312429110327 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12243])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12243])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12243]

theorem cert12243_8 : CellCertificate 12243 (899915332583033 / 10000000000000000 : ℝ) (857824327768311 / 500000000000000000 : ℝ) (346873230098909 / 10000000000000000 : ℝ)
    (cell12243 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · have h := gap_lower (n := 12243) (a := (41901430636477 / 50000000000000 : ℝ)) (b := (1346577813 / 800000000000 : ℝ)) (q := (578108278617 / 25000000000000 : ℝ))
      (E := (cell12243 ⟨8, by decide⟩).energy) (xi := (346873230098909 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12243 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12243]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12243])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12243) (a := (41901430636477 / 50000000000000 : ℝ)) (b := (1346577813 / 800000000000 : ℝ)) (q := (578108278617 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12243])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12243])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12243]

theorem cert12243_9 : CellCertificate 12243 (899915332583033 / 10000000000000000 : ℝ) (857824327768311 / 500000000000000000 : ℝ) (346873230098909 / 10000000000000000 : ℝ)
    (cell12243 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · have h := gap_lower (n := 12243) (a := (3350717438529 / 4000000000000 : ℝ)) (b := (1346577813 / 800000000000 : ℝ)) (q := (14452731759 / 625000000000 : ℝ))
      (E := (cell12243 ⟨9, by decide⟩).energy) (xi := (346873230098909 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12243 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12243]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12243])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12243) (a := (3350717438529 / 4000000000000 : ℝ)) (b := (1346577813 / 800000000000 : ℝ)) (q := (14452731759 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12243])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12243])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12243]

theorem cert12243_10 : CellCertificate 12243 (899915332583033 / 10000000000000000 : ℝ) (857824327768311 / 500000000000000000 : ℝ) (346873230098909 / 10000000000000000 : ℝ)
    (cell12243 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · have h := gap_lower (n := 12243) (a := (41866517755321 / 50000000000000 : ℝ)) (b := (1346577813 / 800000000000 : ℝ)) (q := (92497643083 / 4000000000000 : ℝ))
      (E := (cell12243 ⟨10, by decide⟩).energy) (xi := (346873230098909 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12243 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12243]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12243])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12243) (a := (41866517755321 / 50000000000000 : ℝ)) (b := (1346577813 / 800000000000 : ℝ)) (q := (92497643083 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12243])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12243])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12243]

theorem cert12243_11 : CellCertificate 12243 (899915332583033 / 10000000000000000 : ℝ) (857824327768311 / 500000000000000000 : ℝ) (346873230098909 / 10000000000000000 : ℝ)
    (cell12243 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · have h := gap_lower (n := 12243) (a := (41849079939879 / 50000000000000 : ℝ)) (b := (1346577813 / 800000000000 : ℝ)) (q := (2312445109033 / 100000000000000 : ℝ))
      (E := (cell12243 ⟨11, by decide⟩).energy) (xi := (346873230098909 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12243 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12243]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12243])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12243) (a := (41849079939879 / 50000000000000 : ℝ)) (b := (1346577813 / 800000000000 : ℝ)) (q := (2312445109033 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12243])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12243])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12243]

theorem cert12243_12 : CellCertificate 12243 (899915332583033 / 10000000000000000 : ℝ) (857824327768311 / 500000000000000000 : ℝ) (346873230098909 / 10000000000000000 : ℝ)
    (cell12243 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · have h := gap_lower (n := 12243) (a := (83663309035317 / 100000000000000 : ℝ)) (b := (1346577813 / 800000000000 : ℝ)) (q := (2312449068629 / 100000000000000 : ℝ))
      (E := (cell12243 ⟨12, by decide⟩).energy) (xi := (346873230098909 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12243 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12243]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12243])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12243) (a := (83663309035317 / 100000000000000 : ℝ)) (b := (1346577813 / 800000000000 : ℝ)) (q := (2312449068629 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12243])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12243])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12243]

theorem cert12243_13 : CellCertificate 12243 (899915332583033 / 10000000000000000 : ℝ) (857824327768311 / 500000000000000000 : ℝ) (346873230098909 / 10000000000000000 : ℝ)
    (cell12243 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · have h := gap_lower (n := 12243) (a := (20907120735561 / 25000000000000 : ℝ)) (b := (1346577813 / 800000000000 : ℝ)) (q := (231245307901 / 10000000000000 : ℝ))
      (E := (cell12243 ⟨13, by decide⟩).energy) (xi := (346873230098909 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12243 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12243]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12243])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12243) (a := (20907120735561 / 25000000000000 : ℝ)) (b := (1346577813 / 800000000000 : ℝ)) (q := (231245307901 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12243])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12243])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12243]

theorem cert12243_14 : CellCertificate 12243 (899915332583033 / 10000000000000000 : ℝ) (857824327768311 / 500000000000000000 : ℝ) (346873230098909 / 10000000000000000 : ℝ)
    (cell12243 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · have h := gap_lower (n := 12243) (a := (5224605097853 / 6250000000000 : ℝ)) (b := (1346577813 / 800000000000 : ℝ)) (q := (23124570309 / 1000000000000 : ℝ))
      (E := (cell12243 ⟨14, by decide⟩).energy) (xi := (346873230098909 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12243 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12243]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12243])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12243) (a := (5224605097853 / 6250000000000 : ℝ)) (b := (1346577813 / 800000000000 : ℝ)) (q := (23124570309 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12243])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12243])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12243]

theorem cert12243_15 : CellCertificate 12243 (899915332583033 / 10000000000000000 : ℝ) (857824327768311 / 500000000000000000 : ℝ) (346873230098909 / 10000000000000000 : ℝ)
    (cell12243 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · have h := gap_lower (n := 12243) (a := (4177945243541 / 5000000000000 : ℝ)) (b := (1346577813 / 800000000000 : ℝ)) (q := (1156230523519 / 50000000000000 : ℝ))
      (E := (cell12243 ⟨15, by decide⟩).energy) (xi := (346873230098909 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12243 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12243]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12243])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12243) (a := (4177945243541 / 5000000000000 : ℝ)) (b := (1346577813 / 800000000000 : ℝ)) (q := (1156230523519 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12243])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12243])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12243]

theorem cert12243_16 : CellCertificate 12243 (899915332583033 / 10000000000000000 : ℝ) (857824327768311 / 500000000000000000 : ℝ) (346873230098909 / 10000000000000000 : ℝ)
    (cell12243 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · have h := gap_lower (n := 12243) (a := (1305064887863 / 1562500000000 : ℝ)) (b := (1346577813 / 800000000000 : ℝ)) (q := (57811625439 / 2500000000000 : ℝ))
      (E := (cell12243 ⟨16, by decide⟩).energy) (xi := (346873230098909 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12243 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12243]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12243])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12243) (a := (1305064887863 / 1562500000000 : ℝ)) (b := (1346577813 / 800000000000 : ℝ)) (q := (57811625439 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12243])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12243])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12243]

theorem cert12243_17 : CellCertificate 12243 (899915332583033 / 10000000000000000 : ℝ) (857824327768311 / 500000000000000000 : ℝ) (346873230098909 / 10000000000000000 : ℝ)
    (cell12243 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · have h := gap_lower (n := 12243) (a := (16697885077707 / 20000000000000 : ℝ)) (b := (1346577813 / 800000000000 : ℝ)) (q := (578117251661 / 25000000000000 : ℝ))
      (E := (cell12243 ⟨17, by decide⟩).energy) (xi := (346873230098909 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12243 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12243]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12243])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12243) (a := (16697885077707 / 20000000000000 : ℝ)) (b := (1346577813 / 800000000000 : ℝ)) (q := (578117251661 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12243])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12243])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12243]

theorem cert12243_18 : CellCertificate 12243 (899915332583033 / 10000000000000000 : ℝ) (857824327768311 / 500000000000000000 : ℝ) (346873230098909 / 10000000000000000 : ℝ)
    (cell12243 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · have h := gap_lower (n := 12243) (a := (83454722532561 / 100000000000000 : ℝ)) (b := (1346577813 / 800000000000 : ℝ)) (q := (462494604027 / 20000000000000 : ℝ))
      (E := (cell12243 ⟨18, by decide⟩).energy) (xi := (346873230098909 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12243 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12243]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12243])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12243) (a := (83454722532561 / 100000000000000 : ℝ)) (b := (1346577813 / 800000000000 : ℝ)) (q := (462494604027 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12243])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12243])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12243]

theorem cert12243_19 : CellCertificate 12243 (899915332583033 / 10000000000000000 : ℝ) (857824327768311 / 500000000000000000 : ℝ) (346873230098909 / 10000000000000000 : ℝ)
    (cell12243 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · have h := gap_lower (n := 12243) (a := (41710022110659 / 50000000000000 : ℝ)) (b := (1346577813 / 800000000000 : ℝ)) (q := (144529812839 / 6250000000000 : ℝ))
      (E := (cell12243 ⟨19, by decide⟩).energy) (xi := (346873230098909 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12243 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12243]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12243])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12243) (a := (41710022110659 / 50000000000000 : ℝ)) (b := (1346577813 / 800000000000 : ℝ)) (q := (144529812839 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12243])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12243])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12243]

theorem cert12244_0 : CellCertificate 12244 (449942678737399 / 5000000000000000 : ℝ) (1715508486168073 / 1000000000000000000 : ℝ) (17342206963583 / 500000000000000 : ℝ)
    (cell12244 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · have h := gap_lower (n := 12244) (a := (84083146643477 / 100000000000000 : ℝ)) (b := (168308294717 / 100000000000000 : ℝ)) (q := (1156126684809 / 50000000000000 : ℝ))
      (E := (cell12244 ⟨0, by decide⟩).energy) (xi := (17342206963583 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12244 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12244]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12244])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12244) (a := (84083146643477 / 100000000000000 : ℝ)) (b := (168308294717 / 100000000000000 : ℝ)) (q := (1156126684809 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12244])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12244])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12244]

theorem cert12244_1 : CellCertificate 12244 (449942678737399 / 5000000000000000 : ℝ) (1715508486168073 / 1000000000000000000 : ℝ) (17342206963583 / 500000000000000 : ℝ)
    (cell12244 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · have h := gap_lower (n := 12244) (a := (10506002689577 / 12500000000000 : ℝ)) (b := (168308294717 / 100000000000000 : ℝ)) (q := (2312257349211 / 100000000000000 : ℝ))
      (E := (cell12244 ⟨1, by decide⟩).energy) (xi := (17342206963583 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12244 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12244]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12244])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12244) (a := (10506002689577 / 12500000000000 : ℝ)) (b := (168308294717 / 100000000000000 : ℝ)) (q := (2312257349211 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12244])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12244])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12244]

theorem cert12244_2 : CellCertificate 12244 (449942678737399 / 5000000000000000 : ℝ) (1715508486168073 / 1000000000000000000 : ℝ) (17342206963583 / 500000000000000 : ℝ)
    (cell12244 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · have h := gap_lower (n := 12244) (a := (84012921536803 / 100000000000000 : ℝ)) (b := (168308294717 / 100000000000000 : ℝ)) (q := (1156130672781 / 50000000000000 : ℝ))
      (E := (cell12244 ⟨2, by decide⟩).energy) (xi := (17342206963583 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12244 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12244]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12244])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12244) (a := (84012921536803 / 100000000000000 : ℝ)) (b := (168308294717 / 100000000000000 : ℝ)) (q := (1156130672781 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12244])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12244])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12244]

theorem cert12244_3 : CellCertificate 12244 (449942678737399 / 5000000000000000 : ℝ) (1715508486168073 / 1000000000000000000 : ℝ) (17342206963583 / 500000000000000 : ℝ)
    (cell12244 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · have h := gap_lower (n := 12244) (a := (83977846667067 / 100000000000000 : ℝ)) (b := (168308294717 / 100000000000000 : ℝ)) (q := (1156132655311 / 50000000000000 : ℝ))
      (E := (cell12244 ⟨3, by decide⟩).energy) (xi := (17342206963583 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12244 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12244]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12244])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12244) (a := (83977846667067 / 100000000000000 : ℝ)) (b := (168308294717 / 100000000000000 : ℝ)) (q := (1156132655311 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12244])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12244])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12244]

theorem cert12244_4 : CellCertificate 12244 (449942678737399 / 5000000000000000 : ℝ) (1715508486168073 / 1000000000000000000 : ℝ) (17342206963583 / 500000000000000 : ℝ)
    (cell12244 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · have h := gap_lower (n := 12244) (a := (8394279687063 / 10000000000000 : ℝ)) (b := (168308294717 / 100000000000000 : ℝ)) (q := (23122693117 / 1000000000000 : ℝ))
      (E := (cell12244 ⟨4, by decide⟩).energy) (xi := (17342206963583 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12244 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12244]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12244])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12244) (a := (8394279687063 / 10000000000000 : ℝ)) (b := (168308294717 / 100000000000000 : ℝ)) (q := (23122693117 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12244])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12244])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12244]

theorem cert12244_5 : CellCertificate 12244 (449942678737399 / 5000000000000000 : ℝ) (1715508486168073 / 1000000000000000000 : ℝ) (17342206963583 / 500000000000000 : ℝ)
    (cell12244 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · have h := gap_lower (n := 12244) (a := (20976943027727 / 25000000000000 : ℝ)) (b := (168308294717 / 100000000000000 : ℝ)) (q := (289034162523 / 12500000000000 : ℝ))
      (E := (cell12244 ⟨5, by decide⟩).energy) (xi := (17342206963583 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12244 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12244]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12244])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12244) (a := (20976943027727 / 25000000000000 : ℝ)) (b := (168308294717 / 100000000000000 : ℝ)) (q := (289034162523 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12244])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12244])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12244]

theorem cert12244_6 : CellCertificate 12244 (449942678737399 / 5000000000000000 : ℝ) (1715508486168073 / 1000000000000000000 : ℝ) (17342206963583 / 500000000000000 : ℝ)
    (cell12244 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · have h := gap_lower (n := 12244) (a := (83872772351513 / 100000000000000 : ℝ)) (b := (168308294717 / 100000000000000 : ℝ)) (q := (462455457001 / 20000000000000 : ℝ))
      (E := (cell12244 ⟨6, by decide⟩).energy) (xi := (17342206963583 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12244 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12244]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12244])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12244) (a := (83872772351513 / 100000000000000 : ℝ)) (b := (168308294717 / 100000000000000 : ℝ)) (q := (462455457001 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12244])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12244])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12244]

theorem cert12244_7 : CellCertificate 12244 (449942678737399 / 5000000000000000 : ℝ) (1715508486168073 / 1000000000000000000 : ℝ) (17342206963583 / 500000000000000 : ℝ)
    (cell12244 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · have h := gap_lower (n := 12244) (a := (16767559511249 / 20000000000000 : ℝ)) (b := (168308294717 / 100000000000000 : ℝ)) (q := (2312281274841 / 100000000000000 : ℝ))
      (E := (cell12244 ⟨7, by decide⟩).energy) (xi := (17342206963583 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12244 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12244]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12244])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12244) (a := (16767559511249 / 20000000000000 : ℝ)) (b := (168308294717 / 100000000000000 : ℝ)) (q := (2312281274841 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12244])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12244])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12244]

theorem cert12244_8 : CellCertificate 12244 (449942678737399 / 5000000000000000 : ℝ) (1715508486168073 / 1000000000000000000 : ℝ) (17342206963583 / 500000000000000 : ℝ)
    (cell12244 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · have h := gap_lower (n := 12244) (a := (83802847689097 / 100000000000000 : ℝ)) (b := (168308294717 / 100000000000000 : ℝ)) (q := (231228527811 / 10000000000000 : ℝ))
      (E := (cell12244 ⟨8, by decide⟩).energy) (xi := (17342206963583 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12244 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12244]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12244])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12244) (a := (83802847689097 / 100000000000000 : ℝ)) (b := (168308294717 / 100000000000000 : ℝ)) (q := (231228527811 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12244])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12244])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12244]

theorem cert12244_9 : CellCertificate 12244 (449942678737399 / 5000000000000000 : ℝ) (1715508486168073 / 1000000000000000000 : ℝ) (17342206963583 / 500000000000000 : ℝ)
    (cell12244 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · have h := gap_lower (n := 12244) (a := (20941980678563 / 25000000000000 : ℝ)) (b := (168308294717 / 100000000000000 : ℝ)) (q := (36129520359 / 1562500000000 : ℝ))
      (E := (cell12244 ⟨9, by decide⟩).energy) (xi := (17342206963583 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12244 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12244]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12244])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12244) (a := (20941980678563 / 25000000000000 : ℝ)) (b := (168308294717 / 100000000000000 : ℝ)) (q := (36129520359 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12244])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12244])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12244]

theorem cert12244_10 : CellCertificate 12244 (449942678737399 / 5000000000000000 : ℝ) (1715508486168073 / 1000000000000000000 : ℝ) (17342206963583 / 500000000000000 : ℝ)
    (cell12244 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · have h := gap_lower (n := 12244) (a := (83733022596079 / 100000000000000 : ℝ)) (b := (168308294717 / 100000000000000 : ℝ)) (q := (578073310339 / 25000000000000 : ℝ))
      (E := (cell12244 ⟨10, by decide⟩).energy) (xi := (17342206963583 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12244 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12244]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12244])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12244) (a := (83733022596079 / 100000000000000 : ℝ)) (b := (168308294717 / 100000000000000 : ℝ)) (q := (578073310339 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12244])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12244])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12244]

theorem cert12244_11 : CellCertificate 12244 (449942678737399 / 5000000000000000 : ℝ) (1715508486168073 / 1000000000000000000 : ℝ) (17342206963583 / 500000000000000 : ℝ)
    (cell12244 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · have h := gap_lower (n := 12244) (a := (16739629459827 / 20000000000000 : ℝ)) (b := (168308294717 / 100000000000000 : ℝ)) (q := (1156148637411 / 50000000000000 : ℝ))
      (E := (cell12244 ⟨11, by decide⟩).energy) (xi := (17342206963583 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12244 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12244]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12244])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12244) (a := (16739629459827 / 20000000000000 : ℝ)) (b := (168308294717 / 100000000000000 : ℝ)) (q := (1156148637411 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12244])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12244])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12244]

theorem cert12244_12 : CellCertificate 12244 (449942678737399 / 5000000000000000 : ℝ) (1715508486168073 / 1000000000000000000 : ℝ) (17342206963583 / 500000000000000 : ℝ)
    (cell12244 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · have h := gap_lower (n := 12244) (a := (83663296788163 / 100000000000000 : ℝ)) (b := (168308294717 / 100000000000000 : ℝ)) (q := (2312301236719 / 100000000000000 : ℝ))
      (E := (cell12244 ⟨12, by decide⟩).energy) (xi := (17342206963583 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12244 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12244]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12244])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12244) (a := (83663296788163 / 100000000000000 : ℝ)) (b := (168308294717 / 100000000000000 : ℝ)) (q := (2312301236719 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12244])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12244])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12244]

theorem cert12244_13 : CellCertificate 12244 (449942678737399 / 5000000000000000 : ℝ) (1715508486168073 / 1000000000000000000 : ℝ) (17342206963583 / 500000000000000 : ℝ)
    (cell12244 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · have h := gap_lower (n := 12244) (a := (10453558878511 / 12500000000000 : ℝ)) (b := (168308294717 / 100000000000000 : ℝ)) (q := (1156152625097 / 50000000000000 : ℝ))
      (E := (cell12244 ⟨13, by decide⟩).energy) (xi := (17342206963583 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12244 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12244]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12244])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12244) (a := (10453558878511 / 12500000000000 : ℝ)) (b := (168308294717 / 100000000000000 : ℝ)) (q := (1156152625097 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12244])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12244])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12244]

theorem cert12244_14 : CellCertificate 12244 (449942678737399 / 5000000000000000 : ℝ) (1715508486168073 / 1000000000000000000 : ℝ) (17342206963583 / 500000000000000 : ℝ)
    (cell12244 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · have h := gap_lower (n := 12244) (a := (41796834992011 / 50000000000000 : ℝ)) (b := (168308294717 / 100000000000000 : ℝ)) (q := (144519325373 / 6250000000000 : ℝ))
      (E := (cell12244 ⟨14, by decide⟩).energy) (xi := (17342206963583 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12244 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12244]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12244])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12244) (a := (41796834992011 / 50000000000000 : ℝ)) (b := (168308294717 / 100000000000000 : ℝ)) (q := (144519325373 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12244])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12244])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12244]

theorem cert12244_15 : CellCertificate 12244 (449942678737399 / 5000000000000000 : ℝ) (1715508486168073 / 1000000000000000000 : ℝ) (17342206963583 / 500000000000000 : ℝ)
    (cell12244 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · have h := gap_lower (n := 12244) (a := (10444861702657 / 12500000000000 : ℝ)) (b := (168308294717 / 100000000000000 : ℝ)) (q := (2312313226779 / 100000000000000 : ℝ))
      (E := (cell12244 ⟨15, by decide⟩).energy) (xi := (17342206963583 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12244 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12244]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12244])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12244) (a := (10444861702657 / 12500000000000 : ℝ)) (b := (168308294717 / 100000000000000 : ℝ)) (q := (2312313226779 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12244])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12244])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12244]

theorem cert12244_16 : CellCertificate 12244 (449942678737399 / 5000000000000000 : ℝ) (1715508486168073 / 1000000000000000000 : ℝ) (17342206963583 / 500000000000000 : ℝ)
    (cell12244 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · have h := gap_lower (n := 12244) (a := (5220258869079 / 6250000000000 : ℝ)) (b := (168308294717 / 100000000000000 : ℝ)) (q := (1156158601381 / 50000000000000 : ℝ))
      (E := (cell12244 ⟨16, by decide⟩).energy) (xi := (17342206963583 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12244 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12244]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12244])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12244) (a := (5220258869079 / 6250000000000 : ℝ)) (b := (168308294717 / 100000000000000 : ℝ)) (q := (1156158601381 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12244])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12244])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12244]

theorem cert12244_17 : CellCertificate 12244 (449942678737399 / 5000000000000000 : ℝ) (1715508486168073 / 1000000000000000000 : ℝ) (17342206963583 / 500000000000000 : ℝ)
    (cell12244 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · have h := gap_lower (n := 12244) (a := (41744707400849 / 50000000000000 : ℝ)) (b := (168308294717 / 100000000000000 : ℝ)) (q := (1156160599047 / 50000000000000 : ℝ))
      (E := (cell12244 ⟨17, by decide⟩).energy) (xi := (17342206963583 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12244 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12244]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12244])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12244) (a := (41744707400849 / 50000000000000 : ℝ)) (b := (168308294717 / 100000000000000 : ℝ)) (q := (1156160599047 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12244])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12244])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12244]

theorem cert12244_18 : CellCertificate 12244 (449942678737399 / 5000000000000000 : ℝ) (1715508486168073 / 1000000000000000000 : ℝ) (17342206963583 / 500000000000000 : ℝ)
    (cell12244 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · have h := gap_lower (n := 12244) (a := (83454712276389 / 100000000000000 : ℝ)) (b := (168308294717 / 100000000000000 : ℝ)) (q := (2312325218621 / 100000000000000 : ℝ))
      (E := (cell12244 ⟨18, by decide⟩).energy) (xi := (17342206963583 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12244 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12244]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12244])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12244) (a := (83454712276389 / 100000000000000 : ℝ)) (b := (168308294717 / 100000000000000 : ℝ)) (q := (2312325218621 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12244])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12244])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12244]

theorem cert12244_19 : CellCertificate 12244 (449942678737399 / 5000000000000000 : ℝ) (1715508486168073 / 1000000000000000000 : ℝ) (17342206963583 / 500000000000000 : ℝ)
    (cell12244 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · have h := gap_lower (n := 12244) (a := (41710017147673 / 50000000000000 : ℝ)) (b := (168308294717 / 100000000000000 : ℝ)) (q := (2312329211733 / 100000000000000 : ℝ))
      (E := (cell12244 ⟨19, by decide⟩).energy) (xi := (17342206963583 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12244 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12244]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12244])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12244) (a := (41710017147673 / 50000000000000 : ℝ)) (b := (168308294717 / 100000000000000 : ℝ)) (q := (2312329211733 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12244])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12244])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12244]

theorem cert12245_0 : CellCertificate 12245 (899855387084573 / 10000000000000000 : ℝ) (1715368339701469 / 1000000000000000000 : ℝ) (13872602138011 / 400000000000000 : ℝ)
    (cell12245 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · have h := gap_lower (n := 12245) (a := (21020782591519 / 25000000000000 : ℝ)) (b := (168294365147 / 100000000000000 : ℝ)) (q := (2312105614991 / 100000000000000 : ℝ))
      (E := (cell12245 ⟨0, by decide⟩).energy) (xi := (13872602138011 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12245 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12245]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12245])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12245) (a := (21020782591519 / 25000000000000 : ℝ)) (b := (168294365147 / 100000000000000 : ℝ)) (q := (2312105614991 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12245])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12245])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12245]

theorem cert12245_1 : CellCertificate 12245 (899855387084573 / 10000000000000000 : ℝ) (1715368339701469 / 1000000000000000000 : ℝ) (13872602138011 / 400000000000000 : ℝ)
    (cell12245 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · have h := gap_lower (n := 12245) (a := (42024002788937 / 50000000000000 : ℝ)) (b := (168294365147 / 100000000000000 : ℝ)) (q := (289013698523 / 12500000000000 : ℝ))
      (E := (cell12245 ⟨1, by decide⟩).energy) (xi := (13872602138011 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12245 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12245]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12245])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12245) (a := (42024002788937 / 50000000000000 : ℝ)) (b := (168294365147 / 100000000000000 : ℝ)) (q := (289013698523 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12245])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12245])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12245]

theorem cert12245_2 : CellCertificate 12245 (899855387084573 / 10000000000000000 : ℝ) (1715368339701469 / 1000000000000000000 : ℝ) (13872602138011 / 400000000000000 : ℝ)
    (cell12245 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · have h := gap_lower (n := 12245) (a := (1050161324203 / 1250000000000 : ℝ)) (b := (168294365147 / 100000000000000 : ℝ)) (q := (462422715787 / 20000000000000 : ℝ))
      (E := (cell12245 ⟨2, by decide⟩).energy) (xi := (13872602138011 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12245 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12245]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12245])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12245) (a := (1050161324203 / 1250000000000 : ℝ)) (b := (168294365147 / 100000000000000 : ℝ)) (q := (462422715787 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12245])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12245])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12245]

theorem cert12245_3 : CellCertificate 12245 (899855387084573 / 10000000000000000 : ℝ) (1715368339701469 / 1000000000000000000 : ℝ) (13872602138011 / 400000000000000 : ℝ)
    (cell12245 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · have h := gap_lower (n := 12245) (a := (41988915702101 / 50000000000000 : ℝ)) (b := (168294365147 / 100000000000000 : ℝ)) (q := (2312117597029 / 100000000000000 : ℝ))
      (E := (cell12245 ⟨3, by decide⟩).energy) (xi := (13872602138011 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12245 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12245]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12245])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12245) (a := (41988915702101 / 50000000000000 : ℝ)) (b := (168294365147 / 100000000000000 : ℝ)) (q := (2312117597029 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12245])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12245])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12245]

theorem cert12245_4 : CellCertificate 12245 (899855387084573 / 10000000000000000 : ℝ) (1715368339701469 / 1000000000000000000 : ℝ) (13872602138011 / 400000000000000 : ℝ)
    (cell12245 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · have h := gap_lower (n := 12245) (a := (10492847743123 / 12500000000000 : ℝ)) (b := (168294365147 / 100000000000000 : ℝ)) (q := (462424318827 / 20000000000000 : ℝ))
      (E := (cell12245 ⟨4, by decide⟩).energy) (xi := (13872602138011 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12245 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12245]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12245])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12245) (a := (10492847743123 / 12500000000000 : ℝ)) (b := (168294365147 / 100000000000000 : ℝ)) (q := (462424318827 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12245])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12245])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12245]

theorem cert12245_5 : CellCertificate 12245 (899855387084573 / 10000000000000000 : ℝ) (1715368339701469 / 1000000000000000000 : ℝ) (13872602138011 / 400000000000000 : ℝ)
    (cell12245 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · have h := gap_lower (n := 12245) (a := (16781551504401 / 20000000000000 : ℝ)) (b := (168294365147 / 100000000000000 : ℝ)) (q := (2312125579443 / 100000000000000 : ℝ))
      (E := (cell12245 ⟨5, by decide⟩).energy) (xi := (13872602138011 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12245 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12245]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12245])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12245) (a := (16781551504401 / 20000000000000 : ℝ)) (b := (168294365147 / 100000000000000 : ℝ)) (q := (2312125579443 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12245])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12245])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12245]

theorem cert12245_6 : CellCertificate 12245 (899855387084573 / 10000000000000000 : ℝ) (1715368339701469 / 1000000000000000000 : ℝ) (13872602138011 / 400000000000000 : ℝ)
    (cell12245 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · have h := gap_lower (n := 12245) (a := (41936379049437 / 50000000000000 : ℝ)) (b := (168294365147 / 100000000000000 : ℝ)) (q := (2312129561889 / 100000000000000 : ℝ))
      (E := (cell12245 ⟨6, by decide⟩).energy) (xi := (13872602138011 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12245 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12245]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12245])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12245) (a := (41936379049437 / 50000000000000 : ℝ)) (b := (168294365147 / 100000000000000 : ℝ)) (q := (2312129561889 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12245])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12245])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12245]

theorem cert12245_7 : CellCertificate 12245 (899855387084573 / 10000000000000000 : ℝ) (1715368339701469 / 1000000000000000000 : ℝ) (13872602138011 / 400000000000000 : ℝ)
    (cell12245 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · have h := gap_lower (n := 12245) (a := (20959445909849 / 25000000000000 : ℝ)) (b := (168294365147 / 100000000000000 : ℝ)) (q := (462426710029 / 20000000000000 : ℝ))
      (E := (cell12245 ⟨7, by decide⟩).energy) (xi := (13872602138011 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12245 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12245]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12245])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12245) (a := (20959445909849 / 25000000000000 : ℝ)) (b := (168294365147 / 100000000000000 : ℝ)) (q := (462426710029 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12245])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12245])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12245]

theorem cert12245_8 : CellCertificate 12245 (899855387084573 / 10000000000000000 : ℝ) (1715368339701469 / 1000000000000000000 : ℝ) (13872602138011 / 400000000000000 : ℝ)
    (cell12245 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · have h := gap_lower (n := 12245) (a := (83802834107563 / 100000000000000 : ℝ)) (b := (168294365147 / 100000000000000 : ℝ)) (q := (289017194079 / 12500000000000 : ℝ))
      (E := (cell12245 ⟨8, by decide⟩).energy) (xi := (13872602138011 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12245 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12245]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12245])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12245) (a := (83802834107563 / 100000000000000 : ℝ)) (b := (168294365147 / 100000000000000 : ℝ)) (q := (289017194079 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12245])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12245])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12245]

theorem cert12245_9 : CellCertificate 12245 (899855387084573 / 10000000000000000 : ℝ) (1715368339701469 / 1000000000000000000 : ℝ) (13872602138011 / 400000000000000 : ℝ)
    (cell12245 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · have h := gap_lower (n := 12245) (a := (2094197736689 / 2500000000000 : ℝ)) (b := (168294365147 / 100000000000000 : ℝ)) (q := (2312141519537 / 100000000000000 : ℝ))
      (E := (cell12245 ⟨9, by decide⟩).energy) (xi := (13872602138011 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12245 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12245]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12245])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12245) (a := (2094197736689 / 2500000000000 : ℝ)) (b := (168294365147 / 100000000000000 : ℝ)) (q := (2312141519537 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12245])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12245])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12245]

theorem cert12245_10 : CellCertificate 12245 (899855387084573 / 10000000000000000 : ℝ) (1715368339701469 / 1000000000000000000 : ℝ) (13872602138011 / 400000000000000 : ℝ)
    (cell12245 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · have h := gap_lower (n := 12245) (a := (16746601936751 / 20000000000000 : ℝ)) (b := (168294365147 / 100000000000000 : ℝ)) (q := (289018189587 / 12500000000000 : ℝ))
      (E := (cell12245 ⟨10, by decide⟩).energy) (xi := (13872602138011 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12245 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12245]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12245])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12245) (a := (16746601936751 / 20000000000000 : ℝ)) (b := (168294365147 / 100000000000000 : ℝ)) (q := (289018189587 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12245])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12245])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12245]

theorem cert12245_11 : CellCertificate 12245 (899855387084573 / 10000000000000000 : ℝ) (1715368339701469 / 1000000000000000000 : ℝ) (13872602138011 / 400000000000000 : ℝ)
    (cell12245 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · have h := gap_lower (n := 12245) (a := (20924533680177 / 25000000000000 : ℝ)) (b := (168294365147 / 100000000000000 : ℝ)) (q := (1156074775881 / 50000000000000 : ℝ))
      (E := (cell12245 ⟨11, by decide⟩).energy) (xi := (13872602138011 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12245 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12245]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12245])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12245) (a := (20924533680177 / 25000000000000 : ℝ)) (b := (168294365147 / 100000000000000 : ℝ)) (q := (1156074775881 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12245])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12245])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12245]

theorem cert12245_12 : CellCertificate 12245 (899855387084573 / 10000000000000000 : ℝ) (1715368339701469 / 1000000000000000000 : ℝ) (13872602138011 / 400000000000000 : ℝ)
    (cell12245 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · have h := gap_lower (n := 12245) (a := (41831642271581 / 50000000000000 : ℝ)) (b := (168294365147 / 100000000000000 : ℝ)) (q := (578038379013 / 25000000000000 : ℝ))
      (E := (cell12245 ⟨12, by decide⟩).energy) (xi := (13872602138011 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12245 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12245]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12245])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12245) (a := (41831642271581 / 50000000000000 : ℝ)) (b := (168294365147 / 100000000000000 : ℝ)) (q := (578038379013 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12245])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12245])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12245]

theorem cert12245_13 : CellCertificate 12245 (899855387084573 / 10000000000000000 : ℝ) (1715368339701469 / 1000000000000000000 : ℝ) (13872602138011 / 400000000000000 : ℝ)
    (cell12245 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · have h := gap_lower (n := 12245) (a := (20907114779011 / 25000000000000 : ℝ)) (b := (168294365147 / 100000000000000 : ℝ)) (q := (231215753271 / 10000000000000 : ℝ))
      (E := (cell12245 ⟨13, by decide⟩).energy) (xi := (13872602138011 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12245 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12245]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12245])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12245) (a := (20907114779011 / 25000000000000 : ℝ)) (b := (168294365147 / 100000000000000 : ℝ)) (q := (231215753271 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12245])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12245])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12245]

theorem cert12245_14 : CellCertificate 12245 (899855387084573 / 10000000000000000 : ℝ) (1715368339701469 / 1000000000000000000 : ℝ) (13872602138011 / 400000000000000 : ℝ)
    (cell12245 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · have h := gap_lower (n := 12245) (a := (41796829202233 / 50000000000000 : ℝ)) (b := (168294365147 / 100000000000000 : ℝ)) (q := (2312161492457 / 100000000000000 : ℝ))
      (E := (cell12245 ⟨14, by decide⟩).energy) (xi := (13872602138011 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12245 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12245]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12245])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12245) (a := (41796829202233 / 50000000000000 : ℝ)) (b := (168294365147 / 100000000000000 : ℝ)) (q := (2312161492457 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12245])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12245])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12245]

theorem cert12245_15 : CellCertificate 12245 (899855387084573 / 10000000000000000 : ℝ) (1715368339701469 / 1000000000000000000 : ℝ) (13872602138011 / 400000000000000 : ℝ)
    (cell12245 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · have h := gap_lower (n := 12245) (a := (83558882373721 / 100000000000000 : ℝ)) (b := (168294365147 / 100000000000000 : ℝ)) (q := (144510344877 / 6250000000000 : ℝ))
      (E := (cell12245 ⟨15, by decide⟩).energy) (xi := (13872602138011 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12245 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12245]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12245])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12245) (a := (83558882373721 / 100000000000000 : ℝ)) (b := (168294365147 / 100000000000000 : ℝ)) (q := (144510344877 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12245])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12245])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12245]

theorem cert12245_16 : CellCertificate 12245 (899855387084573 / 10000000000000000 : ℝ) (1715368339701469 / 1000000000000000000 : ℝ) (13872602138011 / 400000000000000 : ℝ)
    (cell12245 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · have h := gap_lower (n := 12245) (a := (41762065494641 / 50000000000000 : ℝ)) (b := (168294365147 / 100000000000000 : ℝ)) (q := (2312169499567 / 100000000000000 : ℝ))
      (E := (cell12245 ⟨16, by decide⟩).energy) (xi := (13872602138011 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12245 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12245]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12245])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12245) (a := (41762065494641 / 50000000000000 : ℝ)) (b := (168294365147 / 100000000000000 : ℝ)) (q := (2312169499567 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12245])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12245])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12245]

theorem cert12245_17 : CellCertificate 12245 (899855387084573 / 10000000000000000 : ℝ) (1715368339701469 / 1000000000000000000 : ℝ) (13872602138011 / 400000000000000 : ℝ)
    (cell12245 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · have h := gap_lower (n := 12245) (a := (20872351054201 / 25000000000000 : ℝ)) (b := (168294365147 / 100000000000000 : ℝ)) (q := (1156086750619 / 50000000000000 : ℝ))
      (E := (cell12245 ⟨17, by decide⟩).energy) (xi := (13872602138011 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12245 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12245]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12245])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12245) (a := (20872351054201 / 25000000000000 : ℝ)) (b := (168294365147 / 100000000000000 : ℝ)) (q := (1156086750619 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12245])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12245])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12245]

theorem cert12245_18 : CellCertificate 12245 (899855387084573 / 10000000000000000 : ℝ) (1715368339701469 / 1000000000000000000 : ℝ) (13872602138011 / 400000000000000 : ℝ)
    (cell12245 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · have h := gap_lower (n := 12245) (a := (83454702022119 / 100000000000000 : ℝ)) (b := (168294365147 / 100000000000000 : ℝ)) (q := (1156088735353 / 50000000000000 : ℝ))
      (E := (cell12245 ⟨18, by decide⟩).energy) (xi := (13872602138011 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12245 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12245]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12245])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12245) (a := (83454702022119 / 100000000000000 : ℝ)) (b := (168294365147 / 100000000000000 : ℝ)) (q := (1156088735353 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12245])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12245])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12245]

theorem cert12245_19 : CellCertificate 12245 (899855387084573 / 10000000000000000 : ℝ) (1715368339701469 / 1000000000000000000 : ℝ) (13872602138011 / 400000000000000 : ℝ)
    (cell12245 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · have h := gap_lower (n := 12245) (a := (20855006092809 / 25000000000000 : ℝ)) (b := (168294365147 / 100000000000000 : ℝ)) (q := (1156090735853 / 50000000000000 : ℝ))
      (E := (cell12245 ⟨19, by decide⟩).energy) (xi := (13872602138011 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12245 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12245]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12245])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12245) (a := (20855006092809 / 25000000000000 : ℝ)) (b := (168294365147 / 100000000000000 : ℝ)) (q := (1156090735853 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12245])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12245])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12245]

theorem cert12246_0 : CellCertificate 12246 (899825421411191 / 10000000000000000 : ℝ) (428807054032799 / 250000000000000000 : ℝ) (173392986316643 / 5000000000000000 : ℝ)
    (cell12246 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · have h := gap_lower (n := 12246) (a := (84083114091337 / 100000000000000 : ℝ)) (b := (84140218957 / 50000000000000 : ℝ)) (q := (1155978985261 / 50000000000000 : ℝ))
      (E := (cell12246 ⟨0, by decide⟩).energy) (xi := (173392986316643 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12246 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12246]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12246])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12246) (a := (84083114091337 / 100000000000000 : ℝ)) (b := (84140218957 / 50000000000000 : ℝ)) (q := (1155978985261 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12246])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12246])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12246]

theorem cert12246_1 : CellCertificate 12246 (899825421411191 / 10000000000000000 : ℝ) (428807054032799 / 250000000000000000 : ℝ) (173392986316643 / 5000000000000000 : ℝ)
    (cell12246 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · have h := gap_lower (n := 12246) (a := (84047989641751 / 100000000000000 : ℝ)) (b := (84140218957 / 50000000000000 : ℝ)) (q := (231196199519 / 10000000000000 : ℝ))
      (E := (cell12246 ⟨1, by decide⟩).energy) (xi := (173392986316643 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12246 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12246]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12246])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12246) (a := (84047989641751 / 100000000000000 : ℝ)) (b := (84140218957 / 50000000000000 : ℝ)) (q := (231196199519 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12246])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12246])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12246]

theorem cert12246_2 : CellCertificate 12246 (899825421411191 / 10000000000000000 : ℝ) (428807054032799 / 250000000000000000 : ℝ) (173392986316643 / 5000000000000000 : ℝ)
    (cell12246 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · have h := gap_lower (n := 12246) (a := (84012890338253 / 100000000000000 : ℝ)) (b := (84140218957 / 50000000000000 : ℝ)) (q := (288995747557 / 12500000000000 : ℝ))
      (E := (cell12246 ⟨2, by decide⟩).energy) (xi := (173392986316643 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12246 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12246]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12246])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12246) (a := (84012890338253 / 100000000000000 : ℝ)) (b := (84140218957 / 50000000000000 : ℝ)) (q := (288995747557 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12246])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12246])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12246]

theorem cert12246_3 : CellCertificate 12246 (899825421411191 / 10000000000000000 : ℝ) (428807054032799 / 250000000000000000 : ℝ) (173392986316643 / 5000000000000000 : ℝ)
    (cell12246 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · have h := gap_lower (n := 12246) (a := (83977816143871 / 100000000000000 : ℝ)) (b := (84140218957 / 50000000000000 : ℝ)) (q := (577992484009 / 25000000000000 : ℝ))
      (E := (cell12246 ⟨3, by decide⟩).energy) (xi := (173392986316643 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12246 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12246]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12246])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12246) (a := (83977816143871 / 100000000000000 : ℝ)) (b := (84140218957 / 50000000000000 : ℝ)) (q := (577992484009 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12246])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12246])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12246]

theorem cert12246_4 : CellCertificate 12246 (899825421411191 / 10000000000000000 : ℝ) (428807054032799 / 250000000000000000 : ℝ) (173392986316643 / 5000000000000000 : ℝ)
    (cell12246 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · have h := gap_lower (n := 12246) (a := (8394276702183 / 10000000000000 : ℝ)) (b := (84140218957 / 50000000000000 : ℝ)) (q := (462394785847 / 20000000000000 : ℝ))
      (E := (cell12246 ⟨4, by decide⟩).energy) (xi := (173392986316643 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12246 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12246]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12246])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12246) (a := (8394276702183 / 10000000000000 : ℝ)) (b := (84140218957 / 50000000000000 : ℝ)) (q := (462394785847 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12246])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12246])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12246]

theorem cert12246_5 : CellCertificate 12246 (899825421411191 / 10000000000000000 : ℝ) (428807054032799 / 250000000000000000 : ℝ) (173392986316643 / 5000000000000000 : ℝ)
    (cell12246 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · have h := gap_lower (n := 12246) (a := (1678154858711 / 2000000000000 : ℝ)) (b := (84140218957 / 50000000000000 : ℝ)) (q := (577994477859 / 25000000000000 : ℝ))
      (E := (cell12246 ⟨5, by decide⟩).energy) (xi := (173392986316643 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12246 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12246]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12246])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12246) (a := (1678154858711 / 2000000000000 : ℝ)) (b := (84140218957 / 50000000000000 : ℝ)) (q := (577994477859 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12246])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12246])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12246]

theorem cert12246_6 : CellCertificate 12246 (899825421411191 / 10000000000000000 : ℝ) (428807054032799 / 250000000000000000 : ℝ) (173392986316643 / 5000000000000000 : ℝ)
    (cell12246 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · have h := gap_lower (n := 12246) (a := (41936371924321 / 50000000000000 : ℝ)) (b := (84140218957 / 50000000000000 : ℝ)) (q := (1155990974737 / 50000000000000 : ℝ))
      (E := (cell12246 ⟨6, by decide⟩).energy) (xi := (173392986316643 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12246 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12246]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12246])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12246) (a := (41936371924321 / 50000000000000 : ℝ)) (b := (84140218957 / 50000000000000 : ℝ)) (q := (1155990974737 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12246])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12246])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12246]

theorem cert12246_7 : CellCertificate 12246 (899825421411191 / 10000000000000000 : ℝ) (428807054032799 / 250000000000000000 : ℝ) (173392986316643 / 5000000000000000 : ℝ)
    (cell12246 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · have h := gap_lower (n := 12246) (a := (83837769724911 / 100000000000000 : ℝ)) (b := (84140218957 / 50000000000000 : ℝ)) (q := (1155992968121 / 50000000000000 : ℝ))
      (E := (cell12246 ⟨7, by decide⟩).energy) (xi := (173392986316643 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12246 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12246]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12246])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12246) (a := (83837769724911 / 100000000000000 : ℝ)) (b := (84140218957 / 50000000000000 : ℝ)) (q := (1155992968121 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12246])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12246])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12246]

theorem cert12246_8 : CellCertificate 12246 (899825421411191 / 10000000000000000 : ℝ) (428807054032799 / 250000000000000000 : ℝ) (173392986316643 / 5000000000000000 : ℝ)
    (cell12246 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · have h := gap_lower (n := 12246) (a := (83802820528351 / 100000000000000 : ℝ)) (b := (84140218957 / 50000000000000 : ℝ)) (q := (2311989880087 / 100000000000000 : ℝ))
      (E := (cell12246 ⟨8, by decide⟩).energy) (xi := (173392986316643 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12246 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12246]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12246])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12246) (a := (83802820528351 / 100000000000000 : ℝ)) (b := (84140218957 / 50000000000000 : ℝ)) (q := (2311989880087 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12246])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12246])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12246]

theorem cert12246_9 : CellCertificate 12246 (899825421411191 / 10000000000000000 : ℝ) (428807054032799 / 250000000000000000 : ℝ) (173392986316643 / 5000000000000000 : ℝ)
    (cell12246 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · have h := gap_lower (n := 12246) (a := (41883948111573 / 50000000000000 : ℝ)) (b := (84140218957 / 50000000000000 : ℝ)) (q := (462398781009 / 20000000000000 : ℝ))
      (E := (cell12246 ⟨9, by decide⟩).energy) (xi := (173392986316643 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12246 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12246]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12246])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12246) (a := (41883948111573 / 50000000000000 : ℝ)) (b := (84140218957 / 50000000000000 : ℝ)) (q := (462398781009 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12246])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12246])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12246]

theorem cert12246_10 : CellCertificate 12246 (899825421411191 / 10000000000000000 : ℝ) (428807054032799 / 250000000000000000 : ℝ) (173392986316643 / 5000000000000000 : ℝ)
    (cell12246 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · have h := gap_lower (n := 12246) (a := (20933249193417 / 25000000000000 : ℝ)) (b := (84140218957 / 50000000000000 : ℝ)) (q := (23119979031 / 1000000000000 : ℝ))
      (E := (cell12246 ⟨10, by decide⟩).energy) (xi := (173392986316643 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12246 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12246]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12246])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12246) (a := (20933249193417 / 25000000000000 : ℝ)) (b := (84140218957 / 50000000000000 : ℝ)) (q := (23119979031 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12246])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12246])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12246]

theorem cert12246_11 : CellCertificate 12246 (899825421411191 / 10000000000000000 : ℝ) (428807054032799 / 250000000000000000 : ℝ) (173392986316643 / 5000000000000000 : ℝ)
    (cell12246 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · have h := gap_lower (n := 12246) (a := (20924530536119 / 25000000000000 : ℝ)) (b := (84140218957 / 50000000000000 : ℝ)) (q := (2312001881837 / 100000000000000 : ℝ))
      (E := (cell12246 ⟨11, by decide⟩).energy) (xi := (173392986316643 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12246 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12246]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12246])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12246) (a := (20924530536119 / 25000000000000 : ℝ)) (b := (84140218957 / 50000000000000 : ℝ)) (q := (2312001881837 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12246])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12246])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12246]

theorem cert12246_12 : CellCertificate 12246 (899825421411191 / 10000000000000000 : ℝ) (428807054032799 / 250000000000000000 : ℝ) (173392986316643 / 5000000000000000 : ℝ)
    (cell12246 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · have h := gap_lower (n := 12246) (a := (41831636150157 / 50000000000000 : ℝ)) (b := (84140218957 / 50000000000000 : ℝ)) (q := (1156002924293 / 50000000000000 : ℝ))
      (E := (cell12246 ⟨12, by decide⟩).energy) (xi := (173392986316643 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12246 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12246]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12246])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12246) (a := (41831636150157 / 50000000000000 : ℝ)) (b := (84140218957 / 50000000000000 : ℝ)) (q := (1156002924293 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12246])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12246])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12246]

theorem cert12246_13 : CellCertificate 12246 (899825421411191 / 10000000000000000 : ℝ) (428807054032799 / 250000000000000000 : ℝ) (173392986316643 / 5000000000000000 : ℝ)
    (cell12246 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · have h := gap_lower (n := 12246) (a := (83628447206111 / 100000000000000 : ℝ)) (b := (84140218957 / 50000000000000 : ℝ)) (q := (1156004934247 / 50000000000000 : ℝ))
      (E := (cell12246 ⟨13, by decide⟩).energy) (xi := (173392986316643 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12246 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12246]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12246])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12246) (a := (83628447206111 / 100000000000000 : ℝ)) (b := (84140218957 / 50000000000000 : ℝ)) (q := (1156004934247 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12246])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12246])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12246]

theorem cert12246_14 : CellCertificate 12246 (899825421411191 / 10000000000000000 : ℝ) (428807054032799 / 250000000000000000 : ℝ) (173392986316643 / 5000000000000000 : ℝ)
    (cell12246 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · have h := gap_lower (n := 12246) (a := (83593646826979 / 100000000000000 : ℝ)) (b := (84140218957 / 50000000000000 : ℝ)) (q := (1156006916141 / 50000000000000 : ℝ))
      (E := (cell12246 ⟨14, by decide⟩).energy) (xi := (173392986316643 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12246 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12246]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12246])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12246) (a := (83593646826979 / 100000000000000 : ℝ)) (b := (84140218957 / 50000000000000 : ℝ)) (q := (1156006916141 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12246])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12246])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12246]

theorem cert12246_15 : CellCertificate 12246 (899825421411191 / 10000000000000000 : ℝ) (428807054032799 / 250000000000000000 : ℝ) (173392986316643 / 5000000000000000 : ℝ)
    (cell12246 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · have h := gap_lower (n := 12246) (a := (83558871128213 / 100000000000000 : ℝ)) (b := (84140218957 / 50000000000000 : ℝ)) (q := (1156008931343 / 50000000000000 : ℝ))
      (E := (cell12246 ⟨15, by decide⟩).energy) (xi := (173392986316643 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12246 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12246]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12246])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12246) (a := (83558871128213 / 100000000000000 : ℝ)) (b := (84140218957 / 50000000000000 : ℝ)) (q := (1156008931343 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12246])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12246])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12246]

theorem cert12246_16 : CellCertificate 12246 (899825421411191 / 10000000000000000 : ℝ) (428807054032799 / 250000000000000000 : ℝ) (173392986316643 / 5000000000000000 : ℝ)
    (cell12246 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · have h := gap_lower (n := 12246) (a := (41762060037643 / 50000000000000 : ℝ)) (b := (84140218957 / 50000000000000 : ℝ)) (q := (1156010924919 / 50000000000000 : ℝ))
      (E := (cell12246 ⟨16, by decide⟩).energy) (xi := (173392986316643 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12246 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12246]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12246])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12246) (a := (41762060037643 / 50000000000000 : ℝ)) (b := (84140218957 / 50000000000000 : ℝ)) (q := (1156010924919 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12246])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12246])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12246]

theorem cert12246_17 : CellCertificate 12246 (899825421411191 / 10000000000000000 : ℝ) (428807054032799 / 250000000000000000 : ℝ) (173392986316643 / 5000000000000000 : ℝ)
    (cell12246 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · have h := gap_lower (n := 12246) (a := (16697878726771 / 20000000000000 : ℝ)) (b := (84140218957 / 50000000000000 : ℝ)) (q := (462405171583 / 20000000000000 : ℝ))
      (E := (cell12246 ⟨17, by decide⟩).energy) (xi := (173392986316643 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12246 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12246]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12246])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12246) (a := (16697878726771 / 20000000000000 : ℝ)) (b := (84140218957 / 50000000000000 : ℝ)) (q := (462405171583 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12246])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12246])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12246]

theorem cert12246_18 : CellCertificate 12246 (899825421411191 / 10000000000000000 : ℝ) (428807054032799 / 250000000000000000 : ℝ) (173392986316643 / 5000000000000000 : ℝ)
    (cell12246 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · have h := gap_lower (n := 12246) (a := (83454691769751 / 100000000000000 : ℝ)) (b := (84140218957 / 50000000000000 : ℝ)) (q := (144501864661 / 6250000000000 : ℝ))
      (E := (cell12246 ⟨18, by decide⟩).energy) (xi := (173392986316643 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12246 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12246]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12246])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12246) (a := (83454691769751 / 100000000000000 : ℝ)) (b := (84140218957 / 50000000000000 : ℝ)) (q := (144501864661 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12246])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12246])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12246]

theorem cert12246_19 : CellCertificate 12246 (899825421411191 / 10000000000000000 : ℝ) (428807054032799 / 250000000000000000 : ℝ) (173392986316643 / 5000000000000000 : ℝ)
    (cell12246 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · have h := gap_lower (n := 12246) (a := (83420014448987 / 100000000000000 : ℝ)) (b := (84140218957 / 50000000000000 : ℝ)) (q := (72251057611 / 3125000000000 : ℝ))
      (E := (cell12246 ⟨19, by decide⟩).energy) (xi := (173392986316643 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12246 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12246]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12246])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12246) (a := (83420014448987 / 100000000000000 : ℝ)) (b := (84140218957 / 50000000000000 : ℝ)) (q := (72251057611 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12246])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12246])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12246]

theorem cert12247_0 : CellCertificate 12247 (179959092090697 / 2000000000000000 : ℝ) (343017623090329 / 200000000000000000 : ℝ) (173378448409613 / 5000000000000000 : ℝ)
    (cell12247 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · have h := gap_lower (n := 12247) (a := (84083097819259 / 100000000000000 : ℝ)) (b := (21033314127 / 12500000000000 : ℝ)) (q := (1155905218107 / 50000000000000 : ℝ))
      (E := (cell12247 ⟨0, by decide⟩).energy) (xi := (173378448409613 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12247 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12247]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12247])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12247) (a := (84083097819259 / 100000000000000 : ℝ)) (b := (21033314127 / 12500000000000 : ℝ)) (q := (1155905218107 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12247])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12247])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12247]

theorem cert12247_1 : CellCertificate 12247 (179959092090697 / 2000000000000000 : ℝ) (343017623090329 / 200000000000000000 : ℝ) (173378448409613 / 5000000000000000 : ℝ)
    (cell12247 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · have h := gap_lower (n := 12247) (a := (84047973708247 / 100000000000000 : ℝ)) (b := (21033314127 / 12500000000000 : ℝ)) (q := (1155907198439 / 50000000000000 : ℝ))
      (E := (cell12247 ⟨1, by decide⟩).energy) (xi := (173378448409613 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12247 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12247]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12247])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12247) (a := (84047973708247 / 100000000000000 : ℝ)) (b := (21033314127 / 12500000000000 : ℝ)) (q := (1155907198439 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12247])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12247])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12247]

theorem cert12247_2 : CellCertificate 12247 (179959092090697 / 2000000000000000 : ℝ) (343017623090329 / 200000000000000000 : ℝ) (173378448409613 / 5000000000000000 : ℝ)
    (cell12247 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · have h := gap_lower (n := 12247) (a := (42006437371421 / 50000000000000 : ℝ)) (b := (21033314127 / 12500000000000 : ℝ)) (q := (4515270267 / 195312500000 : ℝ))
      (E := (cell12247 ⟨2, by decide⟩).energy) (xi := (173378448409613 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12247 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12247]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12247])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12247) (a := (42006437371421 / 50000000000000 : ℝ)) (b := (21033314127 / 12500000000000 : ℝ)) (q := (4515270267 / 195312500000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12247])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12247])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12247]

theorem cert12247_3 : CellCertificate 12247 (179959092090697 / 2000000000000000 : ℝ) (343017623090329 / 200000000000000000 : ℝ) (173378448409613 / 5000000000000000 : ℝ)
    (cell12247 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · have h := gap_lower (n := 12247) (a := (83977800886073 / 100000000000000 : ℝ)) (b := (21033314127 / 12500000000000 : ℝ)) (q := (577955596369 / 25000000000000 : ℝ))
      (E := (cell12247 ⟨3, by decide⟩).energy) (xi := (173378448409613 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12247 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12247]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12247])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12247) (a := (83977800886073 / 100000000000000 : ℝ)) (b := (21033314127 / 12500000000000 : ℝ)) (q := (577955596369 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12247])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12247])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12247]

theorem cert12247_4 : CellCertificate 12247 (179959092090697 / 2000000000000000 : ℝ) (343017623090329 / 200000000000000000 : ℝ) (173378448409613 / 5000000000000000 : ℝ)
    (cell12247 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · have h := gap_lower (n := 12247) (a := (83942752101167 / 100000000000000 : ℝ)) (b := (21033314127 / 12500000000000 : ℝ)) (q := (2311826374859 / 100000000000000 : ℝ))
      (E := (cell12247 ⟨4, by decide⟩).energy) (xi := (173378448409613 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12247 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12247]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12247])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12247) (a := (83942752101167 / 100000000000000 : ℝ)) (b := (21033314127 / 12500000000000 : ℝ)) (q := (2311826374859 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12247])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12247])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12247]

theorem cert12247_5 : CellCertificate 12247 (179959092090697 / 2000000000000000 : ℝ) (343017623090329 / 200000000000000000 : ℝ) (173378448409613 / 5000000000000000 : ℝ)
    (cell12247 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · have h := gap_lower (n := 12247) (a := (83907728351543 / 100000000000000 : ℝ)) (b := (21033314127 / 12500000000000 : ℝ)) (q := (577957588511 / 25000000000000 : ℝ))
      (E := (cell12247 ⟨5, by decide⟩).energy) (xi := (173378448409613 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12247 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12247]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12247])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12247) (a := (83907728351543 / 100000000000000 : ℝ)) (b := (21033314127 / 12500000000000 : ℝ)) (q := (577957588511 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12247])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12247])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12247]

theorem cert12247_6 : CellCertificate 12247 (179959092090697 / 2000000000000000 : ℝ) (343017623090329 / 200000000000000000 : ℝ) (173378448409613 / 5000000000000000 : ℝ)
    (cell12247 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · have h := gap_lower (n := 12247) (a := (5242045600051 / 6250000000000 : ℝ)) (b := (21033314127 / 12500000000000 : ℝ)) (q := (2311834389863 / 100000000000000 : ℝ))
      (E := (cell12247 ⟨6, by decide⟩).energy) (xi := (173378448409613 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12247 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12247]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12247])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12247) (a := (5242045600051 / 6250000000000 : ℝ)) (b := (21033314127 / 12500000000000 : ℝ)) (q := (2311834389863 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12247])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12247])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12247]

theorem cert12247_7 : CellCertificate 12247 (179959092090697 / 2000000000000000 : ℝ) (343017623090329 / 200000000000000000 : ℝ) (173378448409613 / 5000000000000000 : ℝ)
    (cell12247 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · have h := gap_lower (n := 12247) (a := (8383775581279 / 10000000000000 : ℝ)) (b := (21033314127 / 12500000000000 : ℝ)) (q := (2311838375209 / 100000000000000 : ℝ))
      (E := (cell12247 ⟨7, by decide⟩).energy) (xi := (173378448409613 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12247 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12247]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12247])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12247) (a := (8383775581279 / 10000000000000 : ℝ)) (b := (21033314127 / 12500000000000 : ℝ)) (q := (2311838375209 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12247])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12247])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12247]

theorem cert12247_8 : CellCertificate 12247 (179959092090697 / 2000000000000000 : ℝ) (343017623090329 / 200000000000000000 : ℝ) (173378448409613 / 5000000000000000 : ℝ)
    (cell12247 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · have h := gap_lower (n := 12247) (a := (4190140347573 / 5000000000000 : ℝ)) (b := (21033314127 / 12500000000000 : ℝ)) (q := (2311842318429 / 100000000000000 : ℝ))
      (E := (cell12247 ⟨8, by decide⟩).energy) (xi := (173378448409613 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12247 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12247]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12247])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12247) (a := (4190140347573 / 5000000000000 : ℝ)) (b := (21033314127 / 12500000000000 : ℝ)) (q := (2311842318429 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12247])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12247])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12247]

theorem cert12247_9 : CellCertificate 12247 (179959092090697 / 2000000000000000 : ℝ) (343017623090329 / 200000000000000000 : ℝ) (173378448409613 / 5000000000000000 : ℝ)
    (cell12247 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · have h := gap_lower (n := 12247) (a := (83767882981011 / 100000000000000 : ℝ)) (b := (21033314127 / 12500000000000 : ℝ)) (q := (2311846343557 / 100000000000000 : ℝ))
      (E := (cell12247 ⟨9, by decide⟩).energy) (xi := (173378448409613 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12247 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12247]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12247])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12247) (a := (83767882981011 / 100000000000000 : ℝ)) (b := (21033314127 / 12500000000000 : ℝ)) (q := (2311846343557 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12247])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12247])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12247]

theorem cert12247_10 : CellCertificate 12247 (179959092090697 / 2000000000000000 : ℝ) (343017623090329 / 200000000000000000 : ℝ) (173378448409613 / 5000000000000000 : ℝ)
    (cell12247 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · have h := gap_lower (n := 12247) (a := (41866491932909 / 50000000000000 : ℝ)) (b := (21033314127 / 12500000000000 : ℝ)) (q := (144490646411 / 6250000000000 : ℝ))
      (E := (cell12247 ⟨10, by decide⟩).energy) (xi := (173378448409613 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12247 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12247]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12247])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12247) (a := (41866491932909 / 50000000000000 : ℝ)) (b := (21033314127 / 12500000000000 : ℝ)) (q := (144490646411 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12247])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12247])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12247]

theorem cert12247_11 : CellCertificate 12247 (179959092090697 / 2000000000000000 : ℝ) (343017623090329 / 200000000000000000 : ℝ) (173378448409613 / 5000000000000000 : ℝ)
    (cell12247 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · have h := gap_lower (n := 12247) (a := (41849054785219 / 50000000000000 : ℝ)) (b := (21033314127 / 12500000000000 : ℝ)) (q := (231185432307 / 10000000000000 : ℝ))
      (E := (cell12247 ⟨11, by decide⟩).energy) (xi := (173378448409613 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12247 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12247]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12247])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12247) (a := (41849054785219 / 50000000000000 : ℝ)) (b := (21033314127 / 12500000000000 : ℝ)) (q := (231185432307 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12247])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12247])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12247]

theorem cert12247_12 : CellCertificate 12247 (179959092090697 / 2000000000000000 : ℝ) (343017623090329 / 200000000000000000 : ℝ) (173378448409613 / 5000000000000000 : ℝ)
    (cell12247 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · have h := gap_lower (n := 12247) (a := (83663260059619 / 100000000000000 : ℝ)) (b := (21033314127 / 12500000000000 : ℝ)) (q := (2311858292367 / 100000000000000 : ℝ))
      (E := (cell12247 ⟨12, by decide⟩).energy) (xi := (173378448409613 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12247 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12247]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12247])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12247) (a := (83663260059619 / 100000000000000 : ℝ)) (b := (21033314127 / 12500000000000 : ℝ)) (q := (2311858292367 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12247])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12247])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12247]

theorem cert12247_13 : CellCertificate 12247 (179959092090697 / 2000000000000000 : ℝ) (343017623090329 / 200000000000000000 : ℝ) (173378448409613 / 5000000000000000 : ℝ)
    (cell12247 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · have h := gap_lower (n := 12247) (a := (83628435298289 / 100000000000000 : ℝ)) (b := (21033314127 / 12500000000000 : ℝ)) (q := (462372463123 / 20000000000000 : ℝ))
      (E := (cell12247 ⟨13, by decide⟩).energy) (xi := (173378448409613 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12247 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12247]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12247])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12247) (a := (83628435298289 / 100000000000000 : ℝ)) (b := (21033314127 / 12500000000000 : ℝ)) (q := (462372463123 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12247])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12247])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12247]

theorem cert12247_14 : CellCertificate 12247 (179959092090697 / 2000000000000000 : ℝ) (343017623090329 / 200000000000000000 : ℝ) (173378448409613 / 5000000000000000 : ℝ)
    (cell12247 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · have h := gap_lower (n := 12247) (a := (83593635251561 / 100000000000000 : ℝ)) (b := (21033314127 / 12500000000000 : ℝ)) (q := (2311866283533 / 100000000000000 : ℝ))
      (E := (cell12247 ⟨14, by decide⟩).energy) (xi := (173378448409613 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12247 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12247]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12247])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12247) (a := (83593635251561 / 100000000000000 : ℝ)) (b := (21033314127 / 12500000000000 : ℝ)) (q := (2311866283533 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12247])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12247])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12247]

theorem cert12247_15 : CellCertificate 12247 (179959092090697 / 2000000000000000 : ℝ) (343017623090329 / 200000000000000000 : ℝ) (173378448409613 / 5000000000000000 : ℝ)
    (cell12247 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · have h := gap_lower (n := 12247) (a := (20889714971183 / 25000000000000 : ℝ)) (b := (21033314127 / 12500000000000 : ℝ)) (q := (288983782593 / 12500000000000 : ℝ))
      (E := (cell12247 ⟨15, by decide⟩).energy) (xi := (173378448409613 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12247 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12247]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12247])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12247) (a := (20889714971183 / 25000000000000 : ℝ)) (b := (21033314127 / 12500000000000 : ℝ)) (q := (288983782593 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12247])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12247])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12247]

theorem cert12247_16 : CellCertificate 12247 (179959092090697 / 2000000000000000 : ℝ) (343017623090329 / 200000000000000000 : ℝ) (173378448409613 / 5000000000000000 : ℝ)
    (cell12247 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · have h := gap_lower (n := 12247) (a := (3340964366531 / 4000000000000 : ℝ)) (b := (21033314127 / 12500000000000 : ℝ)) (q := (2311874253581 / 100000000000000 : ℝ))
      (E := (cell12247 ⟨16, by decide⟩).energy) (xi := (173378448409613 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12247 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12247]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12247])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12247) (a := (3340964366531 / 4000000000000 : ℝ)) (b := (21033314127 / 12500000000000 : ℝ)) (q := (2311874253581 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12247])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12247])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12247]

theorem cert12247_17 : CellCertificate 12247 (179959092090697 / 2000000000000000 : ℝ) (343017623090329 / 200000000000000000 : ℝ) (173378448409613 / 5000000000000000 : ℝ)
    (cell12247 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · have h := gap_lower (n := 12247) (a := (83489383052849 / 100000000000000 : ℝ)) (b := (21033314127 / 12500000000000 : ℝ)) (q := (2311878268129 / 100000000000000 : ℝ))
      (E := (cell12247 ⟨17, by decide⟩).energy) (xi := (173378448409613 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12247 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12247]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12247])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12247) (a := (83489383052849 / 100000000000000 : ℝ)) (b := (21033314127 / 12500000000000 : ℝ)) (q := (2311878268129 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12247])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12247])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12247]

theorem cert12247_18 : CellCertificate 12247 (179959092090697 / 2000000000000000 : ℝ) (343017623090329 / 200000000000000000 : ℝ) (173378448409613 / 5000000000000000 : ℝ)
    (cell12247 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · have h := gap_lower (n := 12247) (a := (16690936303857 / 20000000000000 : ℝ)) (b := (21033314127 / 12500000000000 : ℝ)) (q := (144492640753 / 6250000000000 : ℝ))
      (E := (cell12247 ⟨18, by decide⟩).energy) (xi := (173378448409613 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12247 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12247]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12247])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12247) (a := (16690936303857 / 20000000000000 : ℝ)) (b := (21033314127 / 12500000000000 : ℝ)) (q := (144492640753 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12247])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12247])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12247]

theorem cert12247_19 : CellCertificate 12247 (179959092090697 / 2000000000000000 : ℝ) (343017623090329 / 200000000000000000 : ℝ) (173378448409613 / 5000000000000000 : ℝ)
    (cell12247 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · have h := gap_lower (n := 12247) (a := (83420004528597 / 100000000000000 : ℝ)) (b := (21033314127 / 12500000000000 : ℝ)) (q := (2311886269069 / 100000000000000 : ℝ))
      (E := (cell12247 ⟨19, by decide⟩).energy) (xi := (173378448409613 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12247 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12247]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12247])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12247) (a := (83420004528597 / 100000000000000 : ℝ)) (b := (21033314127 / 12500000000000 : ℝ)) (q := (2311886269069 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12247])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12247])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12247]

theorem cert12248_0 : CellCertificate 12248 (899765504210291 / 10000000000000000 : ℝ) (342989607531441 / 200000000000000000 : ℝ) (86681956501657 / 2500000000000000 : ℝ)
    (cell12248 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · have h := gap_lower (n := 12248) (a := (42041540774921 / 50000000000000 : ℝ)) (b := (168252590453 / 100000000000000 : ℝ)) (q := (1155831477153 / 50000000000000 : ℝ))
      (E := (cell12248 ⟨0, by decide⟩).energy) (xi := (86681956501657 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12248 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12248]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12248])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12248) (a := (42041540774921 / 50000000000000 : ℝ)) (b := (168252590453 / 100000000000000 : ℝ)) (q := (1155831477153 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12248])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12248])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12248]

theorem cert12248_1 : CellCertificate 12248 (899765504210291 / 10000000000000000 : ℝ) (342989607531441 / 200000000000000000 : ℝ) (86681956501657 / 2500000000000000 : ℝ)
    (cell12248 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · have h := gap_lower (n := 12248) (a := (84047957777361 / 100000000000000 : ℝ)) (b := (168252590453 / 100000000000000 : ℝ)) (q := (1155833454409 / 50000000000000 : ℝ))
      (E := (cell12248 ⟨1, by decide⟩).energy) (xi := (86681956501657 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12248 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12248]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12248])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12248) (a := (84047957777361 / 100000000000000 : ℝ)) (b := (168252590453 / 100000000000000 : ℝ)) (q := (1155833454409 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12248])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12248])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12248]

theorem cert12248_2 : CellCertificate 12248 (899765504210291 / 10000000000000000 : ℝ) (342989607531441 / 200000000000000000 : ℝ) (86681956501657 / 2500000000000000 : ℝ)
    (cell12248 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · have h := gap_lower (n := 12248) (a := (42006429575003 / 50000000000000 : ℝ)) (b := (168252590453 / 100000000000000 : ℝ)) (q := (2311670941103 / 100000000000000 : ℝ))
      (E := (cell12248 ⟨2, by decide⟩).energy) (xi := (86681956501657 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12248 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12248]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12248])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12248) (a := (42006429575003 / 50000000000000 : ℝ)) (b := (168252590453 / 100000000000000 : ℝ)) (q := (2311670941103 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12248])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12248])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12248]

theorem cert12248_3 : CellCertificate 12248 (899765504210291 / 10000000000000000 : ℝ) (342989607531441 / 200000000000000000 : ℝ) (86681956501657 / 2500000000000000 : ℝ)
    (cell12248 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · have h := gap_lower (n := 12248) (a := (10497223203851 / 12500000000000 : ℝ)) (b := (168252590453 / 100000000000000 : ℝ)) (q := (46233498907 / 2000000000000 : ℝ))
      (E := (cell12248 ⟨3, by decide⟩).energy) (xi := (86681956501657 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12248 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12248]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12248])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12248) (a := (10497223203851 / 12500000000000 : ℝ)) (b := (168252590453 / 100000000000000 : ℝ)) (q := (46233498907 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12248])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12248])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12248]

theorem cert12248_4 : CellCertificate 12248 (899765504210291 / 10000000000000000 : ℝ) (342989607531441 / 200000000000000000 : ℝ) (86681956501657 / 2500000000000000 : ℝ)
    (cell12248 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · have h := gap_lower (n := 12248) (a := (41971368591497 / 50000000000000 : ℝ)) (b := (168252590453 / 100000000000000 : ℝ)) (q := (36119983297 / 1562500000000 : ℝ))
      (E := (cell12248 ⟨4, by decide⟩).energy) (xi := (86681956501657 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12248 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12248]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12248])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12248) (a := (41971368591497 / 50000000000000 : ℝ)) (b := (168252590453 / 100000000000000 : ℝ)) (q := (36119983297 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12248])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12248])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12248]

theorem cert12248_5 : CellCertificate 12248 (899765504210291 / 10000000000000000 : ℝ) (342989607531441 / 200000000000000000 : ℝ) (86681956501657 / 2500000000000000 : ℝ)
    (cell12248 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · have h := gap_lower (n := 12248) (a := (16781542753997 / 20000000000000 : ℝ)) (b := (168252590453 / 100000000000000 : ℝ)) (q := (1155841453633 / 50000000000000 : ℝ))
      (E := (cell12248 ⟨5, by decide⟩).energy) (xi := (86681956501657 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12248 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12248]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12248])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12248) (a := (16781542753997 / 20000000000000 : ℝ)) (b := (168252590453 / 100000000000000 : ℝ)) (q := (1155841453633 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12248])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12248])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12248]

theorem cert12248_6 : CellCertificate 12248 (899765504210291 / 10000000000000000 : ℝ) (342989607531441 / 200000000000000000 : ℝ) (86681956501657 / 2500000000000000 : ℝ)
    (cell12248 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · have h := gap_lower (n := 12248) (a := (16774543071079 / 20000000000000 : ℝ)) (b := (168252590453 / 100000000000000 : ℝ)) (q := (144480430191 / 6250000000000 : ℝ))
      (E := (cell12248 ⟨6, by decide⟩).energy) (xi := (86681956501657 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12248 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12248]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12248])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12248) (a := (16774543071079 / 20000000000000 : ℝ)) (b := (168252590453 / 100000000000000 : ℝ)) (q := (144480430191 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12248])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12248])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12248]

theorem cert12248_7 : CellCertificate 12248 (899765504210291 / 10000000000000000 : ℝ) (342989607531441 / 200000000000000000 : ℝ) (86681956501657 / 2500000000000000 : ℝ)
    (cell12248 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · have h := gap_lower (n := 12248) (a := (83837741903031 / 100000000000000 : ℝ)) (b := (168252590453 / 100000000000000 : ℝ)) (q := (2311690867049 / 100000000000000 : ℝ))
      (E := (cell12248 ⟨7, by decide⟩).energy) (xi := (86681956501657 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12248 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12248]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12248])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12248) (a := (83837741903031 / 100000000000000 : ℝ)) (b := (168252590453 / 100000000000000 : ℝ)) (q := (2311690867049 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12248])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12248])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12248]

theorem cert12248_8 : CellCertificate 12248 (899765504210291 / 10000000000000000 : ℝ) (342989607531441 / 200000000000000000 : ℝ) (86681956501657 / 2500000000000000 : ℝ)
    (cell12248 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · have h := gap_lower (n := 12248) (a := (83802793376889 / 100000000000000 : ℝ)) (b := (168252590453 / 100000000000000 : ℝ)) (q := (2311694867659 / 100000000000000 : ℝ))
      (E := (cell12248 ⟨8, by decide⟩).energy) (xi := (86681956501657 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12248 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12248]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12248])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12248) (a := (83802793376889 / 100000000000000 : ℝ)) (b := (168252590453 / 100000000000000 : ℝ)) (q := (2311694867659 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12248])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12248])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12248]

theorem cert12248_9 : CellCertificate 12248 (899765504210291 / 10000000000000000 : ℝ) (342989607531441 / 200000000000000000 : ℝ) (86681956501657 / 2500000000000000 : ℝ)
    (cell12248 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · have h := gap_lower (n := 12248) (a := (16753573948231 / 20000000000000 : ℝ)) (b := (168252590453 / 100000000000000 : ℝ)) (q := (1155849446523 / 50000000000000 : ℝ))
      (E := (cell12248 ⟨9, by decide⟩).energy) (xi := (86681956501657 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12248 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12248]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12248])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12248) (a := (16753573948231 / 20000000000000 : ℝ)) (b := (168252590453 / 100000000000000 : ℝ)) (q := (1155849446523 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12248])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12248])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12248]

theorem cert12248_10 : CellCertificate 12248 (899765504210291 / 10000000000000000 : ℝ) (342989607531441 / 200000000000000000 : ℝ) (86681956501657 / 2500000000000000 : ℝ)
    (cell12248 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · have h := gap_lower (n := 12248) (a := (20933242740051 / 25000000000000 : ℝ)) (b := (168252590453 / 100000000000000 : ℝ)) (q := (2311702835123 / 100000000000000 : ℝ))
      (E := (cell12248 ⟨10, by decide⟩).energy) (xi := (86681956501657 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12248 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12248]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12248])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12248) (a := (20933242740051 / 25000000000000 : ℝ)) (b := (168252590453 / 100000000000000 : ℝ)) (q := (2311702835123 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12248])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12248])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12248]

theorem cert12248_11 : CellCertificate 12248 (899765504210291 / 10000000000000000 : ℝ) (342989607531441 / 200000000000000000 : ℝ) (86681956501657 / 2500000000000000 : ℝ)
    (cell12248 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · have h := gap_lower (n := 12248) (a := (16739619399719 / 20000000000000 : ℝ)) (b := (168252590453 / 100000000000000 : ℝ)) (q := (115585343773 / 5000000000000 : ℝ))
      (E := (cell12248 ⟨11, by decide⟩).energy) (xi := (86681956501657 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12248 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12248]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12248])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12248) (a := (16739619399719 / 20000000000000 : ℝ)) (b := (168252590453 / 100000000000000 : ℝ)) (q := (115585343773 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12248])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12248])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12248]

theorem cert12248_12 : CellCertificate 12248 (899765504210291 / 10000000000000000 : ℝ) (342989607531441 / 200000000000000000 : ℝ) (86681956501657 / 2500000000000000 : ℝ)
    (cell12248 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · have h := gap_lower (n := 12248) (a := (3346529912843 / 4000000000000 : ℝ)) (b := (168252590453 / 100000000000000 : ℝ)) (q := (1155855423699 / 50000000000000 : ℝ))
      (E := (cell12248 ⟨12, by decide⟩).energy) (xi := (86681956501657 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12248 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12248]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12248])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12248) (a := (3346529912843 / 4000000000000 : ℝ)) (b := (168252590453 / 100000000000000 : ℝ)) (q := (1155855423699 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12248])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12248])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12248]

theorem cert12248_13 : CellCertificate 12248 (899765504210291 / 10000000000000000 : ℝ) (342989607531441 / 200000000000000000 : ℝ) (86681956501657 / 2500000000000000 : ℝ)
    (cell12248 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · have h := gap_lower (n := 12248) (a := (1306694115509 / 1562500000000 : ℝ)) (b := (168252590453 / 100000000000000 : ℝ)) (q := (2311714816009 / 100000000000000 : ℝ))
      (E := (cell12248 ⟨13, by decide⟩).energy) (xi := (86681956501657 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12248 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12248]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12248])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12248) (a := (1306694115509 / 1562500000000 : ℝ)) (b := (168252590453 / 100000000000000 : ℝ)) (q := (2311714816009 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12248])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12248])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12248]

theorem cert12248_14 : CellCertificate 12248 (899765504210291 / 10000000000000000 : ℝ) (342989607531441 / 200000000000000000 : ℝ) (86681956501657 / 2500000000000000 : ℝ)
    (cell12248 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · have h := gap_lower (n := 12248) (a := (83593623678211 / 100000000000000 : ℝ)) (b := (168252590453 / 100000000000000 : ℝ)) (q := (1155859423107 / 50000000000000 : ℝ))
      (E := (cell12248 ⟨14, by decide⟩).energy) (xi := (86681956501657 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12248 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12248]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12248])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12248) (a := (83593623678211 / 100000000000000 : ℝ)) (b := (168252590453 / 100000000000000 : ℝ)) (q := (1155859423107 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12248])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12248])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12248]

theorem cert12248_15 : CellCertificate 12248 (899765504210291 / 10000000000000000 : ℝ) (342989607531441 / 200000000000000000 : ℝ) (86681956501657 / 2500000000000000 : ℝ)
    (cell12248 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · have h := gap_lower (n := 12248) (a := (20889712160819 / 25000000000000 : ℝ)) (b := (168252590453 / 100000000000000 : ℝ)) (q := (1155861414217 / 50000000000000 : ℝ))
      (E := (cell12248 ⟨15, by decide⟩).energy) (xi := (86681956501657 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12248 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12248]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12248])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12248) (a := (20889712160819 / 25000000000000 : ℝ)) (b := (168252590453 / 100000000000000 : ℝ)) (q := (1155861414217 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12248])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12248])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12248]

theorem cert12248_16 : CellCertificate 12248 (899765504210291 / 10000000000000000 : ℝ) (342989607531441 / 200000000000000000 : ℝ) (86681956501657 / 2500000000000000 : ℝ)
    (cell12248 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · have h := gap_lower (n := 12248) (a := (83524098253249 / 100000000000000 : ℝ)) (b := (168252590453 / 100000000000000 : ℝ)) (q := (577931706767 / 25000000000000 : ℝ))
      (E := (cell12248 ⟨16, by decide⟩).energy) (xi := (86681956501657 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12248 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12248]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12248])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12248) (a := (83524098253249 / 100000000000000 : ℝ)) (b := (168252590453 / 100000000000000 : ℝ)) (q := (577931706767 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12248])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12248])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12248]

theorem cert12248_17 : CellCertificate 12248 (899765504210291 / 10000000000000000 : ℝ) (342989607531441 / 200000000000000000 : ℝ) (86681956501657 / 2500000000000000 : ℝ)
    (cell12248 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · have h := gap_lower (n := 12248) (a := (16697874494757 / 20000000000000 : ℝ)) (b := (168252590453 / 100000000000000 : ℝ)) (q := (2311730790043 / 100000000000000 : ℝ))
      (E := (cell12248 ⟨17, by decide⟩).energy) (xi := (86681956501657 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12248 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12248]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12248])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12248) (a := (16697874494757 / 20000000000000 : ℝ)) (b := (168252590453 / 100000000000000 : ℝ)) (q := (2311730790043 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12248])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12248])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12248]

theorem cert12248_18 : CellCertificate 12248 (899765504210291 / 10000000000000000 : ℝ) (342989607531441 / 200000000000000000 : ℝ) (86681956501657 / 2500000000000000 : ℝ)
    (cell12248 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · have h := gap_lower (n := 12248) (a := (260795847721 / 312500000000 : ℝ)) (b := (168252590453 / 100000000000000 : ℝ)) (q := (2311734781309 / 100000000000000 : ℝ))
      (E := (cell12248 ⟨18, by decide⟩).energy) (xi := (86681956501657 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12248 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12248]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12248])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12248) (a := (260795847721 / 312500000000 : ℝ)) (b := (168252590453 / 100000000000000 : ℝ)) (q := (2311734781309 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12248])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12248])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12248]

theorem cert12248_19 : CellCertificate 12248 (899765504210291 / 10000000000000000 : ℝ) (342989607531441 / 200000000000000000 : ℝ) (86681956501657 / 2500000000000000 : ℝ)
    (cell12248 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · have h := gap_lower (n := 12248) (a := (83419994610067 / 100000000000000 : ℝ)) (b := (168252590453 / 100000000000000 : ℝ)) (q := (2311738806463 / 100000000000000 : ℝ))
      (E := (cell12248 ⟨19, by decide⟩).energy) (xi := (86681956501657 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12248 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12248]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12248])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12248) (a := (83419994610067 / 100000000000000 : ℝ)) (b := (168252590453 / 100000000000000 : ℝ)) (q := (2311738806463 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12248])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12248])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12248]

theorem cert12249_0 : CellCertificate 12249 (899735552680443 / 10000000000000000 : ℝ) (6698468682587 / 3906250000000000 : ℝ) (346698760194027 / 10000000000000000 : ℝ)
    (cell12249 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · have h := gap_lower (n := 12249) (a := (16816613056617 / 20000000000000 : ℝ)) (b := (10514916889 / 6250000000000 : ℝ)) (q := (2311515582563 / 100000000000000 : ℝ))
      (E := (cell12249 ⟨0, by decide⟩).energy) (xi := (346698760194027 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12249 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12249]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12249])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12249) (a := (16816613056617 / 20000000000000 : ℝ)) (b := (10514916889 / 6250000000000 : ℝ)) (q := (2311515582563 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12249])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12249])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12249]

theorem cert12249_1 : CellCertificate 12249 (899735552680443 / 10000000000000000 : ℝ) (6698468682587 / 3906250000000000 : ℝ) (346698760194027 / 10000000000000000 : ℝ)
    (cell12249 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · have h := gap_lower (n := 12249) (a := (21011985462273 / 25000000000000 : ℝ)) (b := (10514916889 / 6250000000000 : ℝ)) (q := (1155759765507 / 50000000000000 : ℝ))
      (E := (cell12249 ⟨1, by decide⟩).energy) (xi := (346698760194027 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12249 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12249]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12249])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12249) (a := (21011985462273 / 25000000000000 : ℝ)) (b := (10514916889 / 6250000000000 : ℝ)) (q := (1155759765507 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12249])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12249])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12249]

theorem cert12249_2 : CellCertificate 12249 (899735552680443 / 10000000000000000 : ℝ) (6698468682587 / 3906250000000000 : ℝ) (346698760194027 / 10000000000000000 : ℝ)
    (cell12249 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · have h := gap_lower (n := 12249) (a := (16802568711949 / 20000000000000 : ℝ)) (b := (10514916889 / 6250000000000 : ℝ)) (q := (57788088951 / 2500000000000 : ℝ))
      (E := (cell12249 ⟨2, by decide⟩).energy) (xi := (346698760194027 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12249 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12249]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12249])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12249) (a := (16802568711949 / 20000000000000 : ℝ)) (b := (10514916889 / 6250000000000 : ℝ)) (q := (57788088951 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12249])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12249])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12249]

theorem cert12249_3 : CellCertificate 12249 (899735552680443 / 10000000000000000 : ℝ) (6698468682587 / 3906250000000000 : ℝ) (346698760194027 / 10000000000000000 : ℝ)
    (cell12249 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · have h := gap_lower (n := 12249) (a := (3359110815123 / 4000000000000 : ℝ)) (b := (10514916889 / 6250000000000 : ℝ)) (q := (2311527557829 / 100000000000000 : ℝ))
      (E := (cell12249 ⟨3, by decide⟩).energy) (xi := (346698760194027 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12249 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12249]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12249])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12249) (a := (3359110815123 / 4000000000000 : ℝ)) (b := (10514916889 / 6250000000000 : ℝ)) (q := (2311527557829 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12249])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12249])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12249]

theorem cert12249_4 : CellCertificate 12249 (899735552680443 / 10000000000000000 : ℝ) (6698468682587 / 3906250000000000 : ℝ) (346698760194027 / 10000000000000000 : ℝ)
    (cell12249 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · have h := gap_lower (n := 12249) (a := (8394272226731 / 10000000000000 : ℝ)) (b := (10514916889 / 6250000000000 : ℝ)) (q := (2311531539829 / 100000000000000 : ℝ))
      (E := (cell12249 ⟨4, by decide⟩).energy) (xi := (346698760194027 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12249 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12249]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12249])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12249) (a := (8394272226731 / 10000000000000 : ℝ)) (b := (10514916889 / 6250000000000 : ℝ)) (q := (2311531539829 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12249])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12249])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12249]

theorem cert12249_5 : CellCertificate 12249 (899735552680443 / 10000000000000000 : ℝ) (6698468682587 / 3906250000000000 : ℝ) (346698760194027 / 10000000000000000 : ℝ)
    (cell12249 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · have h := gap_lower (n := 12249) (a := (83907699190873 / 100000000000000 : ℝ)) (b := (10514916889 / 6250000000000 : ℝ)) (q := (2311535513229 / 100000000000000 : ℝ))
      (E := (cell12249 ⟨5, by decide⟩).energy) (xi := (346698760194027 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12249 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12249]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12249])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12249) (a := (83907699190873 / 100000000000000 : ℝ)) (b := (10514916889 / 6250000000000 : ℝ)) (q := (2311535513229 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12249])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12249])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12249]

theorem cert12249_6 : CellCertificate 12249 (899735552680443 / 10000000000000000 : ℝ) (6698468682587 / 3906250000000000 : ℝ) (346698760194027 / 10000000000000000 : ℝ)
    (cell12249 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · have h := gap_lower (n := 12249) (a := (41936350556189 / 50000000000000 : ℝ)) (b := (10514916889 / 6250000000000 : ℝ)) (q := (2311539486959 / 100000000000000 : ℝ))
      (E := (cell12249 ⟨6, by decide⟩).energy) (xi := (346698760194027 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12249 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12249]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12249])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12249) (a := (41936350556189 / 50000000000000 : ℝ)) (b := (10514916889 / 6250000000000 : ℝ)) (q := (2311539486959 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12249])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12249])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12249]

theorem cert12249_7 : CellCertificate 12249 (899735552680443 / 10000000000000000 : ℝ) (6698468682587 / 3906250000000000 : ℝ) (346698760194027 / 10000000000000000 : ℝ)
    (cell12249 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · have h := gap_lower (n := 12249) (a := (41918863997817 / 50000000000000 : ℝ)) (b := (10514916889 / 6250000000000 : ℝ)) (q := (2311543527613 / 100000000000000 : ℝ))
      (E := (cell12249 ⟨7, by decide⟩).energy) (xi := (346698760194027 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12249 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12249]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12249])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12249) (a := (41918863997817 / 50000000000000 : ℝ)) (b := (10514916889 / 6250000000000 : ℝ)) (q := (2311543527613 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12249])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12249])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12249]

theorem cert12249_8 : CellCertificate 12249 (899735552680443 / 10000000000000000 : ℝ) (6698468682587 / 3906250000000000 : ℝ) (346698760194027 / 10000000000000000 : ℝ)
    (cell12249 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · have h := gap_lower (n := 12249) (a := (41901389902319 / 50000000000000 : ℝ)) (b := (10514916889 / 6250000000000 : ℝ)) (q := (2311547469829 / 100000000000000 : ℝ))
      (E := (cell12249 ⟨8, by decide⟩).energy) (xi := (346698760194027 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12249 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12249]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12249])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12249) (a := (41901389902319 / 50000000000000 : ℝ)) (b := (10514916889 / 6250000000000 : ℝ)) (q := (2311547469829 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12249])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12249])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12249]

theorem cert12249_9 : CellCertificate 12249 (899735552680443 / 10000000000000000 : ℝ) (6698468682587 / 3906250000000000 : ℝ) (346698760194027 / 10000000000000000 : ℝ)
    (cell12249 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · have h := gap_lower (n := 12249) (a := (83767856503577 / 100000000000000 : ℝ)) (b := (10514916889 / 6250000000000 : ℝ)) (q := (1155775747771 / 50000000000000 : ℝ))
      (E := (cell12249 ⟨9, by decide⟩).energy) (xi := (346698760194027 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12249 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12249]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12249])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12249) (a := (83767856503577 / 100000000000000 : ℝ)) (b := (10514916889 / 6250000000000 : ℝ)) (q := (1155775747771 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12249])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12249])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12249]

theorem cert12249_10 : CellCertificate 12249 (899735552680443 / 10000000000000000 : ℝ) (6698468682587 / 3906250000000000 : ℝ) (346698760194027 / 10000000000000000 : ℝ)
    (cell12249 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · have h := gap_lower (n := 12249) (a := (3349318322273 / 4000000000000 : ℝ)) (b := (10514916889 / 6250000000000 : ℝ)) (q := (2311555496737 / 100000000000000 : ℝ))
      (E := (cell12249 ⟨10, by decide⟩).energy) (xi := (346698760194027 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12249 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12249]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12249])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12249) (a := (3349318322273 / 4000000000000 : ℝ)) (b := (10514916889 / 6250000000000 : ℝ)) (q := (2311555496737 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12249])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12249])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12249]

theorem cert12249_11 : CellCertificate 12249 (899735552680443 / 10000000000000000 : ℝ) (6698468682587 / 3906250000000000 : ℝ) (346698760194027 / 10000000000000000 : ℝ)
    (cell12249 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · have h := gap_lower (n := 12249) (a := (16739616885789 / 20000000000000 : ℝ)) (b := (10514916889 / 6250000000000 : ℝ)) (q := (2311559480991 / 100000000000000 : ℝ))
      (E := (cell12249 ⟨11, by decide⟩).energy) (xi := (346698760194027 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12249 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12249]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12249])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12249) (a := (16739616885789 / 20000000000000 : ℝ)) (b := (10514916889 / 6250000000000 : ℝ)) (q := (2311559480991 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12249])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12249])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12249]

theorem cert12249_12 : CellCertificate 12249 (899735552680443 / 10000000000000000 : ℝ) (6698468682587 / 3906250000000000 : ℝ) (346698760194027 / 10000000000000000 : ℝ)
    (cell12249 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · have h := gap_lower (n := 12249) (a := (20915808896171 / 25000000000000 : ℝ)) (b := (10514916889 / 6250000000000 : ℝ)) (q := (1155781727817 / 50000000000000 : ℝ))
      (E := (cell12249 ⟨12, by decide⟩).energy) (xi := (346698760194027 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12249 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12249]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12249])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12249) (a := (20915808896171 / 25000000000000 : ℝ)) (b := (10514916889 / 6250000000000 : ℝ)) (q := (1155781727817 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12249])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12249])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12249]

theorem cert12249_13 : CellCertificate 12249 (899735552680443 / 10000000000000000 : ℝ) (6698468682587 / 3906250000000000 : ℝ) (346698760194027 / 10000000000000000 : ℝ)
    (cell12249 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · have h := gap_lower (n := 12249) (a := (83628411488973 / 100000000000000 : ℝ)) (b := (10514916889 / 6250000000000 : ℝ)) (q := (72236482117 / 3125000000000 : ℝ))
      (E := (cell12249 ⟨13, by decide⟩).energy) (xi := (346698760194027 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12249 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12249]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12249])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12249) (a := (83628411488973 / 100000000000000 : ℝ)) (b := (10514916889 / 6250000000000 : ℝ)) (q := (72236482117 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12249])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12249])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12249]

theorem cert12249_14 : CellCertificate 12249 (899735552680443 / 10000000000000000 : ℝ) (6698468682587 / 3906250000000000 : ℝ) (346698760194027 / 10000000000000000 : ℝ)
    (cell12249 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · have h := gap_lower (n := 12249) (a := (83593612106929 / 100000000000000 : ℝ)) (b := (10514916889 / 6250000000000 : ℝ)) (q := (462314292447 / 20000000000000 : ℝ))
      (E := (cell12249 ⟨14, by decide⟩).energy) (xi := (346698760194027 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12249 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12249]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12249])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12249) (a := (83593612106929 / 100000000000000 : ℝ)) (b := (10514916889 / 6250000000000 : ℝ)) (q := (462314292447 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12249])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12249])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12249]

theorem cert12249_15 : CellCertificate 12249 (899735552680443 / 10000000000000000 : ℝ) (6698468682587 / 3906250000000000 : ℝ) (346698760194027 / 10000000000000000 : ℝ)
    (cell12249 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · have h := gap_lower (n := 12249) (a := (83558837403847 / 100000000000000 : ℝ)) (b := (10514916889 / 6250000000000 : ℝ)) (q := (577893862383 / 25000000000000 : ℝ))
      (E := (cell12249 ⟨15, by decide⟩).energy) (xi := (346698760194027 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12249 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12249]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12249])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12249) (a := (83558837403847 / 100000000000000 : ℝ)) (b := (10514916889 / 6250000000000 : ℝ)) (q := (577893862383 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12249])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12249])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12249]

theorem cert12249_16 : CellCertificate 12249 (899735552680443 / 10000000000000000 : ℝ) (6698468682587 / 3906250000000000 : ℝ) (346698760194027 / 10000000000000000 : ℝ)
    (cell12249 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · have h := gap_lower (n := 12249) (a := (41762043672603 / 50000000000000 : ℝ)) (b := (10514916889 / 6250000000000 : ℝ)) (q := (2311579454031 / 100000000000000 : ℝ))
      (E := (cell12249 ⟨16, by decide⟩).energy) (xi := (346698760194027 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12249 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12249]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12249])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12249) (a := (41762043672603 / 50000000000000 : ℝ)) (b := (10514916889 / 6250000000000 : ℝ)) (q := (2311579454031 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12249])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12249])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12249]

theorem cert12249_17 : CellCertificate 12249 (899735552680443 / 10000000000000000 : ℝ) (6698468682587 / 3906250000000000 : ℝ) (346698760194027 / 10000000000000000 : ℝ)
    (cell12249 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · have h := gap_lower (n := 12249) (a := (10436170237083 / 12500000000000 : ℝ)) (b := (10514916889 / 6250000000000 : ℝ)) (q := (462316684731 / 20000000000000 : ℝ))
      (E := (cell12249 ⟨17, by decide⟩).energy) (xi := (346698760194027 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12249 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12249]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12249])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12249) (a := (10436170237083 / 12500000000000 : ℝ)) (b := (10514916889 / 6250000000000 : ℝ)) (q := (462316684731 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12249])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12249])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12249]

theorem cert12249_18 : CellCertificate 12249 (899735552680443 / 10000000000000000 : ℝ) (6698468682587 / 3906250000000000 : ℝ) (346698760194027 / 10000000000000000 : ℝ)
    (cell12249 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · have h := gap_lower (n := 12249) (a := (16690932204811 / 20000000000000 : ℝ)) (b := (10514916889 / 6250000000000 : ℝ)) (q := (2311587422361 / 100000000000000 : ℝ))
      (E := (cell12249 ⟨18, by decide⟩).energy) (xi := (346698760194027 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12249 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12249]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12249])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12249) (a := (16690932204811 / 20000000000000 : ℝ)) (b := (10514916889 / 6250000000000 : ℝ)) (q := (2311587422361 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12249])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12249])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12249]

theorem cert12249_19 : CellCertificate 12249 (899735552680443 / 10000000000000000 : ℝ) (6698468682587 / 3906250000000000 : ℝ) (346698760194027 / 10000000000000000 : ℝ)
    (cell12249 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · have h := gap_lower (n := 12249) (a := (16683996938679 / 20000000000000 : ℝ)) (b := (10514916889 / 6250000000000 : ℝ)) (q := (2311591397531 / 100000000000000 : ℝ))
      (E := (cell12249 ⟨19, by decide⟩).energy) (xi := (346698760194027 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12249 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12249]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12249])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12249) (a := (16683996938679 / 20000000000000 : ℝ)) (b := (10514916889 / 6250000000000 : ℝ)) (q := (2311591397531 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12249])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12249])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12249]

end BstLean.Part263
