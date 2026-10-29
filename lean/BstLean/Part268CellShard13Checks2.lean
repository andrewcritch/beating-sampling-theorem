import BstLean.Part268CellShard13Checks1

/-! Twenty scalar cells per dimension in a 25-dimension shard. -/
namespace BstLean.Part268
open Real BstLean.Part263

theorem cert12675_40 : CellCertificate 12675 (887390288570421 / 10000000000000000 : ℝ) (33143104260069 / 20000000000000000 : ℝ) (83688365477403 / 2500000000000000 : ℝ)
    (cell12675 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · have h := gap_lower (n := 12675) (a := (41348081199303 / 50000000000000 : ℝ)) (b := (2031414591 / 1250000000000 : ℝ)) (q := (35229822043 / 1562500000000 : ℝ))
      (E := (cell12675 ⟨40, by decide⟩).energy) (xi := (83688365477403 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12675 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12675]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12675])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12675) (a := (41348081199303 / 50000000000000 : ℝ)) (b := (2031414591 / 1250000000000 : ℝ)) (q := (35229822043 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12675])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12675])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12675]

theorem cert12675_41 : CellCertificate 12675 (887390288570421 / 10000000000000000 : ℝ) (33143104260069 / 20000000000000000 : ℝ) (83688365477403 / 2500000000000000 : ℝ)
    (cell12675 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · have h := gap_lower (n := 12675) (a := (82662150513377 / 100000000000000 : ℝ)) (b := (2031414591 / 1250000000000 : ℝ)) (q := (1127356322609 / 50000000000000 : ℝ))
      (E := (cell12675 ⟨41, by decide⟩).energy) (xi := (83688365477403 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12675 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12675]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12675])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12675) (a := (82662150513377 / 100000000000000 : ℝ)) (b := (2031414591 / 1250000000000 : ℝ)) (q := (1127356322609 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12675])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12675])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12675]

theorem cert12675_42 : CellCertificate 12675 (887390288570421 / 10000000000000000 : ℝ) (33143104260069 / 20000000000000000 : ℝ) (83688365477403 / 2500000000000000 : ℝ)
    (cell12675 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · have h := gap_lower (n := 12675) (a := (41314081125659 / 50000000000000 : ℝ)) (b := (2031414591 / 1250000000000 : ℝ)) (q := (2254716614127 / 100000000000000 : ℝ))
      (E := (cell12675 ⟨42, by decide⟩).energy) (xi := (83688365477403 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12675 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12675]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12675])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12675) (a := (41314081125659 / 50000000000000 : ℝ)) (b := (2031414591 / 1250000000000 : ℝ)) (q := (2254716614127 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12675])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12675])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12675]

theorem cert12675_43 : CellCertificate 12675 (887390288570421 / 10000000000000000 : ℝ) (33143104260069 / 20000000000000000 : ℝ) (83688365477403 / 2500000000000000 : ℝ)
    (cell12675 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · have h := gap_lower (n := 12675) (a := (41297098791359 / 50000000000000 : ℝ)) (b := (2031414591 / 1250000000000 : ℝ)) (q := (2254720634257 / 100000000000000 : ℝ))
      (E := (cell12675 ⟨43, by decide⟩).energy) (xi := (83688365477403 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12675 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12675]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12675])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12675) (a := (41297098791359 / 50000000000000 : ℝ)) (b := (2031414591 / 1250000000000 : ℝ)) (q := (2254720634257 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12675])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12675])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12675]

theorem cert12675_44 : CellCertificate 12675 (887390288570421 / 10000000000000000 : ℝ) (33143104260069 / 20000000000000000 : ℝ) (83688365477403 / 2500000000000000 : ℝ)
    (cell12675 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · have h := gap_lower (n := 12675) (a := (1290004007469 / 1562500000000 : ℝ)) (b := (2031414591 / 1250000000000 : ℝ)) (q := (2254724645839 / 100000000000000 : ℝ))
      (E := (cell12675 ⟨44, by decide⟩).energy) (xi := (83688365477403 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12675 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12675]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12675])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12675) (a := (1290004007469 / 1562500000000 : ℝ)) (b := (2031414591 / 1250000000000 : ℝ)) (q := (2254724645839 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12675])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12675])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12675]

theorem cert12675_45 : CellCertificate 12675 (887390288570421 / 10000000000000000 : ℝ) (33143104260069 / 20000000000000000 : ℝ) (83688365477403 / 2500000000000000 : ℝ)
    (cell12675 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · have h := gap_lower (n := 12675) (a := (82526338907803 / 100000000000000 : ℝ)) (b := (2031414591 / 1250000000000 : ℝ)) (q := (2254728647653 / 100000000000000 : ℝ))
      (E := (cell12675 ⟨45, by decide⟩).energy) (xi := (83688365477403 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12675 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12675]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12675])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12675) (a := (82526338907803 / 100000000000000 : ℝ)) (b := (2031414591 / 1250000000000 : ℝ)) (q := (2254728647653 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12675])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12675])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12675]

theorem cert12675_46 : CellCertificate 12675 (887390288570421 / 10000000000000000 : ℝ) (33143104260069 / 20000000000000000 : ℝ) (83688365477403 / 2500000000000000 : ℝ)
    (cell12675 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · have h := gap_lower (n := 12675) (a := (82492444842813 / 100000000000000 : ℝ)) (b := (2031414591 / 1250000000000 : ℝ)) (q := (450946527653 / 20000000000000 : ℝ))
      (E := (cell12675 ⟨46, by decide⟩).energy) (xi := (83688365477403 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12675 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12675]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12675])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12675) (a := (82492444842813 / 100000000000000 : ℝ)) (b := (2031414591 / 1250000000000 : ℝ)) (q := (450946527653 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12675])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12675])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12675]

theorem cert12675_47 : CellCertificate 12675 (887390288570421 / 10000000000000000 : ℝ) (33143104260069 / 20000000000000000 : ℝ) (83688365477403 / 2500000000000000 : ℝ)
    (cell12675 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · have h := gap_lower (n := 12675) (a := (8245857425393 / 10000000000000 : ℝ)) (b := (2031414591 / 1250000000000 : ℝ)) (q := (281842084367 / 12500000000000 : ℝ))
      (E := (cell12675 ⟨47, by decide⟩).energy) (xi := (83688365477403 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12675 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12675]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12675])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12675) (a := (8245857425393 / 10000000000000 : ℝ)) (b := (2031414591 / 1250000000000 : ℝ)) (q := (281842084367 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12675])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12675])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12675]

theorem cert12675_48 : CellCertificate 12675 (887390288570421 / 10000000000000000 : ℝ) (33143104260069 / 20000000000000000 : ℝ) (83688365477403 / 2500000000000000 : ℝ)
    (cell12675 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · have h := gap_lower (n := 12675) (a := (10303090889023 / 12500000000000 : ℝ)) (b := (2031414591 / 1250000000000 : ℝ)) (q := (2254740638003 / 100000000000000 : ℝ))
      (E := (cell12675 ⟨48, by decide⟩).energy) (xi := (83688365477403 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12675 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12675]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12675])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12675) (a := (10303090889023 / 12500000000000 : ℝ)) (b := (2031414591 / 1250000000000 : ℝ)) (q := (2254740638003 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12675])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12675])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12675]

theorem cert12675_49 : CellCertificate 12675 (887390288570421 / 10000000000000000 : ℝ) (33143104260069 / 20000000000000000 : ℝ) (83688365477403 / 2500000000000000 : ℝ)
    (cell12675 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · have h := gap_lower (n := 12675) (a := (82390903388751 / 100000000000000 : ℝ)) (b := (2031414591 / 1250000000000 : ℝ)) (q := (225474464323 / 10000000000000 : ℝ))
      (E := (cell12675 ⟨49, by decide⟩).energy) (xi := (83688365477403 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12675 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12675]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12675])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12675) (a := (82390903388751 / 100000000000000 : ℝ)) (b := (2031414591 / 1250000000000 : ℝ)) (q := (225474464323 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12675])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12675])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12675]

theorem cert12675_50 : CellCertificate 12675 (887390288570421 / 10000000000000000 : ℝ) (33143104260069 / 20000000000000000 : ℝ) (83688365477403 / 2500000000000000 : ℝ)
    (cell12675 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · have h := gap_lower (n := 12675) (a := (82357103054951 / 100000000000000 : ℝ)) (b := (2031414591 / 1250000000000 : ℝ)) (q := (450949737679 / 20000000000000 : ℝ))
      (E := (cell12675 ⟨50, by decide⟩).energy) (xi := (83688365477403 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12675 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12675]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12675])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12675) (a := (82357103054951 / 100000000000000 : ℝ)) (b := (2031414591 / 1250000000000 : ℝ)) (q := (450949737679 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12675])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12675])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12675]

theorem cert12675_51 : CellCertificate 12675 (887390288570421 / 10000000000000000 : ℝ) (33143104260069 / 20000000000000000 : ℝ) (83688365477403 / 2500000000000000 : ℝ)
    (cell12675 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · have h := gap_lower (n := 12675) (a := (82323326082247 / 100000000000000 : ℝ)) (b := (2031414591 / 1250000000000 : ℝ)) (q := (450950530611 / 20000000000000 : ℝ))
      (E := (cell12675 ⟨51, by decide⟩).energy) (xi := (83688365477403 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12675 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12675]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12675])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12675) (a := (82323326082247 / 100000000000000 : ℝ)) (b := (2031414591 / 1250000000000 : ℝ)) (q := (450950530611 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12675])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12675])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12675]

theorem cert12675_52 : CellCertificate 12675 (887390288570421 / 10000000000000000 : ℝ) (33143104260069 / 20000000000000000 : ℝ) (83688365477403 / 2500000000000000 : ℝ)
    (cell12675 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · have h := gap_lower (n := 12675) (a := (16457914488449 / 20000000000000 : ℝ)) (b := (2031414591 / 1250000000000 : ℝ)) (q := (1127378326239 / 50000000000000 : ℝ))
      (E := (cell12675 ⟨52, by decide⟩).energy) (xi := (83688365477403 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12675 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12675]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12675])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12675) (a := (16457914488449 / 20000000000000 : ℝ)) (b := (2031414591 / 1250000000000 : ℝ)) (q := (1127378326239 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12675])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12675])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12675]

theorem cert12675_53 : CellCertificate 12675 (887390288570421 / 10000000000000000 : ℝ) (33143104260069 / 20000000000000000 : ℝ) (83688365477403 / 2500000000000000 : ℝ)
    (cell12675 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · have h := gap_lower (n := 12675) (a := (10281980263337 / 12500000000000 : ℝ)) (b := (2031414591 / 1250000000000 : ℝ)) (q := (1127380341903 / 50000000000000 : ℝ))
      (E := (cell12675 ⟨53, by decide⟩).energy) (xi := (83688365477403 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12675 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12675]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12675])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12675) (a := (10281980263337 / 12500000000000 : ℝ)) (b := (2031414591 / 1250000000000 : ℝ)) (q := (1127380341903 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12675])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12675])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12675]

theorem cert12675_54 : CellCertificate 12675 (887390288570421 / 10000000000000000 : ℝ) (33143104260069 / 20000000000000000 : ℝ) (83688365477403 / 2500000000000000 : ℝ)
    (cell12675 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · have h := gap_lower (n := 12675) (a := (82222135047487 / 100000000000000 : ℝ)) (b := (2031414591 / 1250000000000 : ℝ)) (q := (1127382342449 / 50000000000000 : ℝ))
      (E := (cell12675 ⟨54, by decide⟩).energy) (xi := (83688365477403 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12675 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12675]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12675])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12675) (a := (82222135047487 / 100000000000000 : ℝ)) (b := (2031414591 / 1250000000000 : ℝ)) (q := (1127382342449 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12675])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12675])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12675]

theorem cert12675_55 : CellCertificate 12675 (887390288570421 / 10000000000000000 : ℝ) (33143104260069 / 20000000000000000 : ℝ) (83688365477403 / 2500000000000000 : ℝ)
    (cell12675 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · have h := gap_lower (n := 12675) (a := (82188451236651 / 100000000000000 : ℝ)) (b := (2031414591 / 1250000000000 : ℝ)) (q := (1127384355751 / 50000000000000 : ℝ))
      (E := (cell12675 ⟨55, by decide⟩).energy) (xi := (83688365477403 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12675 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12675]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12675])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12675) (a := (82188451236651 / 100000000000000 : ℝ)) (b := (2031414591 / 1250000000000 : ℝ)) (q := (1127384355751 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12675])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12675])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12675]

theorem cert12675_56 : CellCertificate 12675 (887390288570421 / 10000000000000000 : ℝ) (33143104260069 / 20000000000000000 : ℝ) (83688365477403 / 2500000000000000 : ℝ)
    (cell12675 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · have h := gap_lower (n := 12675) (a := (20538697661589 / 25000000000000 : ℝ)) (b := (2031414591 / 1250000000000 : ℝ)) (q := (450954540203 / 20000000000000 : ℝ))
      (E := (cell12675 ⟨56, by decide⟩).energy) (xi := (83688365477403 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12675 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12675]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12675])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12675) (a := (20538697661589 / 25000000000000 : ℝ)) (b := (2031414591 / 1250000000000 : ℝ)) (q := (450954540203 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12675])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12675])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12675]

theorem cert12675_57 : CellCertificate 12675 (887390288570421 / 10000000000000000 : ℝ) (33143104260069 / 20000000000000000 : ℝ) (83688365477403 / 2500000000000000 : ℝ)
    (cell12675 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · have h := gap_lower (n := 12675) (a := (82121153248913 / 100000000000000 : ℝ)) (b := (2031414591 / 1250000000000 : ℝ)) (q := (2254776708813 / 100000000000000 : ℝ))
      (E := (cell12675 ⟨57, by decide⟩).energy) (xi := (83688365477403 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12675 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12675]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12675])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12675) (a := (82121153248913 / 100000000000000 : ℝ)) (b := (2031414591 / 1250000000000 : ℝ)) (q := (2254776708813 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12675])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12675])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12675]

theorem cert12675_58 : CellCertificate 12675 (887390288570421 / 10000000000000000 : ℝ) (33143104260069 / 20000000000000000 : ℝ) (83688365477403 / 2500000000000000 : ℝ)
    (cell12675 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · have h := gap_lower (n := 12675) (a := (1282617797137 / 1562500000000 : ℝ)) (b := (2031414591 / 1250000000000 : ℝ)) (q := (1127390365499 / 50000000000000 : ℝ))
      (E := (cell12675 ⟨58, by decide⟩).energy) (xi := (83688365477403 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12675 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12675]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12675])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12675) (a := (1282617797137 / 1562500000000 : ℝ)) (b := (2031414591 / 1250000000000 : ℝ)) (q := (1127390365499 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12675])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12675])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12675]

theorem cert12675_59 : CellCertificate 12675 (887390288570421 / 10000000000000000 : ℝ) (33143104260069 / 20000000000000000 : ℝ) (83688365477403 / 2500000000000000 : ℝ)
    (cell12675 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · have h := gap_lower (n := 12675) (a := (16410789584501 / 20000000000000 : ℝ)) (b := (2031414591 / 1250000000000 : ℝ)) (q := (140924044017 / 6250000000000 : ℝ))
      (E := (cell12675 ⟨59, by decide⟩).energy) (xi := (83688365477403 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12675 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12675]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12675])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12675) (a := (16410789584501 / 20000000000000 : ℝ)) (b := (2031414591 / 1250000000000 : ℝ)) (q := (140924044017 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12675])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12675])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12675]

theorem cert12676_40 : CellCertificate 12676 (887362248039349 / 10000000000000000 : ℝ) (66280977528967 / 40000000000000000 : ℝ) (10460200200167 / 312500000000000 : ℝ)
    (cell12676 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · have h := gap_lower (n := 12676) (a := (10337019963347 / 12500000000000 : ℝ)) (b := (40625047419 / 25000000000000 : ℝ)) (q := (90183402161 / 4000000000000 : ℝ))
      (E := (cell12676 ⟨40, by decide⟩).energy) (xi := (10460200200167 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12676 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12676]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12676])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12676) (a := (10337019963347 / 12500000000000 : ℝ)) (b := (40625047419 / 25000000000000 : ℝ)) (q := (90183402161 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12676])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12676])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12676]

theorem cert12676_41 : CellCertificate 12676 (887362248039349 / 10000000000000000 : ℝ) (66280977528967 / 40000000000000000 : ℝ) (10460200200167 / 312500000000000 : ℝ)
    (cell12676 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · have h := gap_lower (n := 12676) (a := (82662148125123 / 100000000000000 : ℝ)) (b := (40625047419 / 25000000000000 : ℝ)) (q := (563647255777 / 25000000000000 : ℝ))
      (E := (cell12676 ⟨41, by decide⟩).energy) (xi := (10460200200167 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12676 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12676]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12676])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12676) (a := (82662148125123 / 100000000000000 : ℝ)) (b := (40625047419 / 25000000000000 : ℝ)) (q := (563647255777 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12676])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12676])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12676]

theorem cert12676_42 : CellCertificate 12676 (887362248039349 / 10000000000000000 : ℝ) (66280977528967 / 40000000000000000 : ℝ) (10460200200167 / 312500000000000 : ℝ)
    (cell12676 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · have h := gap_lower (n := 12676) (a := (41314080083111 / 50000000000000 : ℝ)) (b := (40625047419 / 25000000000000 : ℝ)) (q := (450918608973 / 20000000000000 : ℝ))
      (E := (cell12676 ⟨42, by decide⟩).energy) (xi := (10460200200167 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12676 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12676]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12676])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12676) (a := (41314080083111 / 50000000000000 : ℝ)) (b := (40625047419 / 25000000000000 : ℝ)) (q := (450918608973 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12676])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12676])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12676]

theorem cert12676_43 : CellCertificate 12676 (887362248039349 / 10000000000000000 : ℝ) (66280977528967 / 40000000000000000 : ℝ) (10460200200167 / 312500000000000 : ℝ)
    (cell12676 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · have h := gap_lower (n := 12676) (a := (82594195800361 / 100000000000000 : ℝ)) (b := (40625047419 / 25000000000000 : ℝ)) (q := (2254597059769 / 100000000000000 : ℝ))
      (E := (cell12676 ⟨43, by decide⟩).energy) (xi := (10460200200167 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12676 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12676]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12676])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12676) (a := (82594195800361 / 100000000000000 : ℝ)) (b := (40625047419 / 25000000000000 : ℝ)) (q := (2254597059769 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12676])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12676])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12676]

theorem cert12676_44 : CellCertificate 12676 (887362248039349 / 10000000000000000 : ℝ) (66280977528967 / 40000000000000000 : ℝ) (10460200200167 / 312500000000000 : ℝ)
    (cell12676 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · have h := gap_lower (n := 12676) (a := (82560254997983 / 100000000000000 : ℝ)) (b := (40625047419 / 25000000000000 : ℝ)) (q := (35228141669 / 1562500000000 : ℝ))
      (E := (cell12676 ⟨44, by decide⟩).energy) (xi := (10460200200167 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12676 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12676]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12676])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12676) (a := (82560254997983 / 100000000000000 : ℝ)) (b := (40625047419 / 25000000000000 : ℝ)) (q := (35228141669 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12676])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12676])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12676]

theorem cert12676_45 : CellCertificate 12676 (887362248039349 / 10000000000000000 : ℝ) (66280977528967 / 40000000000000000 : ℝ) (10460200200167 / 312500000000000 : ℝ)
    (cell12676 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · have h := gap_lower (n := 12676) (a := (41263168864837 / 50000000000000 : ℝ)) (b := (40625047419 / 25000000000000 : ℝ)) (q := (225460506479 / 10000000000000 : ℝ))
      (E := (cell12676 ⟨45, by decide⟩).energy) (xi := (10460200200167 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12676 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12676]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12676])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12676) (a := (41263168864837 / 50000000000000 : ℝ)) (b := (40625047419 / 25000000000000 : ℝ)) (q := (225460506479 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12676])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12676])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12676]

theorem cert12676_46 : CellCertificate 12676 (887362248039349 / 10000000000000000 : ℝ) (66280977528967 / 40000000000000000 : ℝ) (10460200200167 / 312500000000000 : ℝ)
    (cell12676 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · have h := gap_lower (n := 12676) (a := (41246221983087 / 50000000000000 : ℝ)) (b := (40625047419 / 25000000000000 : ℝ)) (q := (1127304526127 / 50000000000000 : ℝ))
      (E := (cell12676 ⟨46, by decide⟩).energy) (xi := (10460200200167 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12676 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12676]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12676])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12676) (a := (41246221983087 / 50000000000000 : ℝ)) (b := (40625047419 / 25000000000000 : ℝ)) (q := (1127304526127 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12676])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12676])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12676]

theorem cert12676_47 : CellCertificate 12676 (887362248039349 / 10000000000000000 : ℝ) (66280977528967 / 40000000000000000 : ℝ) (10460200200167 / 312500000000000 : ℝ)
    (cell12676 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · have h := gap_lower (n := 12676) (a := (41229286839183 / 50000000000000 : ℝ)) (b := (40625047419 / 25000000000000 : ℝ)) (q := (563653271617 / 25000000000000 : ℝ))
      (E := (cell12676 ⟨47, by decide⟩).energy) (xi := (10460200200167 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12676 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12676]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12676])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12676) (a := (41229286839183 / 50000000000000 : ℝ)) (b := (40625047419 / 25000000000000 : ℝ)) (q := (563653271617 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12676])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12676])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12676]

theorem cert12676_48 : CellCertificate 12676 (887362248039349 / 10000000000000000 : ℝ) (66280977528967 / 40000000000000000 : ℝ) (10460200200167 / 312500000000000 : ℝ)
    (cell12676 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · have h := gap_lower (n := 12676) (a := (515154542733 / 625000000000 : ℝ)) (b := (40625047419 / 25000000000000 : ℝ)) (q := (2254617047769 / 100000000000000 : ℝ))
      (E := (cell12676 ⟨48, by decide⟩).energy) (xi := (10460200200167 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12676 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12676]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12676])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12676) (a := (515154542733 / 625000000000 : ℝ)) (b := (40625047419 / 25000000000000 : ℝ)) (q := (2254617047769 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12676])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12676])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12676]

theorem cert12676_49 : CellCertificate 12676 (887362248039349 / 10000000000000000 : ℝ) (66280977528967 / 40000000000000000 : ℝ) (10460200200167 / 312500000000000 : ℝ)
    (cell12676 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · have h := gap_lower (n := 12676) (a := (82390903414093 / 100000000000000 : ℝ)) (b := (40625047419 / 25000000000000 : ℝ)) (q := (28182763149 / 1250000000000 : ℝ))
      (E := (cell12676 ⟨49, by decide⟩).energy) (xi := (10460200200167 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12676 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12676]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12676])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12676) (a := (82390903414093 / 100000000000000 : ℝ)) (b := (40625047419 / 25000000000000 : ℝ)) (q := (28182763149 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12676])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12676])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12676]

theorem cert12676_50 : CellCertificate 12676 (887362248039349 / 10000000000000000 : ℝ) (66280977528967 / 40000000000000000 : ℝ) (10460200200167 / 312500000000000 : ℝ)
    (cell12676 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · have h := gap_lower (n := 12676) (a := (41178551690063 / 50000000000000 : ℝ)) (b := (40625047419 / 25000000000000 : ℝ)) (q := (2254625096697 / 100000000000000 : ℝ))
      (E := (cell12676 ⟨50, by decide⟩).energy) (xi := (10460200200167 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12676 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12676]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12676])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12676) (a := (41178551690063 / 50000000000000 : ℝ)) (b := (40625047419 / 25000000000000 : ℝ)) (q := (2254625096697 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12676])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12676])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12676]

theorem cert12676_51 : CellCertificate 12676 (887362248039349 / 10000000000000000 : ℝ) (66280977528967 / 40000000000000000 : ℝ) (10460200200167 / 312500000000000 : ℝ)
    (cell12676 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · have h := gap_lower (n := 12676) (a := (82323326706843 / 100000000000000 : ℝ)) (b := (40625047419 / 25000000000000 : ℝ)) (q := (2254629061659 / 100000000000000 : ℝ))
      (E := (cell12676 ⟨51, by decide⟩).energy) (xi := (10460200200167 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12676 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12676]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12676])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12676) (a := (82323326706843 / 100000000000000 : ℝ)) (b := (40625047419 / 25000000000000 : ℝ)) (q := (2254629061659 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12676])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12676])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12676]

theorem cert12676_52 : CellCertificate 12676 (887362248039349 / 10000000000000000 : ℝ) (66280977528967 / 40000000000000000 : ℝ) (10460200200167 / 312500000000000 : ℝ)
    (cell12676 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · have h := gap_lower (n := 12676) (a := (82289573365851 / 100000000000000 : ℝ)) (b := (40625047419 / 25000000000000 : ℝ)) (q := (281829132759 / 12500000000000 : ℝ))
      (E := (cell12676 ⟨52, by decide⟩).energy) (xi := (10460200200167 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12676 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12676]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12676])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12676) (a := (82289573365851 / 100000000000000 : ℝ)) (b := (40625047419 / 25000000000000 : ℝ)) (q := (281829132759 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12676])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12676])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12676]

theorem cert12676_53 : CellCertificate 12676 (887362248039349 / 10000000000000000 : ℝ) (66280977528967 / 40000000000000000 : ℝ) (10460200200167 / 312500000000000 : ℝ)
    (cell12676 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · have h := gap_lower (n := 12676) (a := (82255843328899 / 100000000000000 : ℝ)) (b := (40625047419 / 25000000000000 : ℝ)) (q := (2254637095077 / 100000000000000 : ℝ))
      (E := (cell12676 ⟨53, by decide⟩).energy) (xi := (10460200200167 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12676 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12676]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12676])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12676) (a := (82255843328899 / 100000000000000 : ℝ)) (b := (40625047419 / 25000000000000 : ℝ)) (q := (2254637095077 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12676])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12676])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12676]

theorem cert12676_54 : CellCertificate 12676 (887362248039349 / 10000000000000000 : ℝ) (66280977528967 / 40000000000000000 : ℝ) (10460200200167 / 312500000000000 : ℝ)
    (cell12676 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · have h := gap_lower (n := 12676) (a := (82222136567879 / 100000000000000 : ℝ)) (b := (40625047419 / 25000000000000 : ℝ)) (q := (563660274633 / 25000000000000 : ℝ))
      (E := (cell12676 ⟨54, by decide⟩).energy) (xi := (10460200200167 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12676 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12676]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12676])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12676) (a := (82222136567879 / 100000000000000 : ℝ)) (b := (40625047419 / 25000000000000 : ℝ)) (q := (563660274633 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12676])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12676])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12676]

theorem cert12676_55 : CellCertificate 12676 (887362248039349 / 10000000000000000 : ℝ) (66280977528967 / 40000000000000000 : ℝ) (10460200200167 / 312500000000000 : ℝ)
    (cell12676 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · have h := gap_lower (n := 12676) (a := (41094226527411 / 50000000000000 : ℝ)) (b := (40625047419 / 25000000000000 : ℝ)) (q := (1127322564093 / 50000000000000 : ℝ))
      (E := (cell12676 ⟨55, by decide⟩).energy) (xi := (10460200200167 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12676 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12676]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12676])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12676) (a := (41094226527411 / 50000000000000 : ℝ)) (b := (40625047419 / 25000000000000 : ℝ)) (q := (1127322564093 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12676])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12676])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12676]

theorem cert12676_56 : CellCertificate 12676 (887362248039349 / 10000000000000000 : ℝ) (66280977528967 / 40000000000000000 : ℝ) (10460200200167 / 312500000000000 : ℝ)
    (cell12676 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · have h := gap_lower (n := 12676) (a := (82154792761897 / 100000000000000 : ℝ)) (b := (40625047419 / 25000000000000 : ℝ)) (q := (2254649121433 / 100000000000000 : ℝ))
      (E := (cell12676 ⟨56, by decide⟩).energy) (xi := (10460200200167 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12676 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12676]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12676])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12676) (a := (82154792761897 / 100000000000000 : ℝ)) (b := (40625047419 / 25000000000000 : ℝ)) (q := (2254649121433 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12676])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12676])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12676]

theorem cert12676_57 : CellCertificate 12676 (887362248039349 / 10000000000000000 : ℝ) (66280977528967 / 40000000000000000 : ℝ) (10460200200167 / 312500000000000 : ℝ)
    (cell12676 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · have h := gap_lower (n := 12676) (a := (10265144457677 / 12500000000000 : ℝ)) (b := (40625047419 / 25000000000000 : ℝ)) (q := (2254653133651 / 100000000000000 : ℝ))
      (E := (cell12676 ⟨57, by decide⟩).energy) (xi := (10460200200167 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12676 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12676]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12676])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12676) (a := (10265144457677 / 12500000000000 : ℝ)) (b := (40625047419 / 25000000000000 : ℝ)) (q := (2254653133651 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12676])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12676])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12676]

theorem cert12676_58 : CellCertificate 12676 (887362248039349 / 10000000000000000 : ℝ) (66280977528967 / 40000000000000000 : ℝ) (10460200200167 / 312500000000000 : ℝ)
    (cell12676 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · have h := gap_lower (n := 12676) (a := (41043770862913 / 50000000000000 : ℝ)) (b := (40625047419 / 25000000000000 : ℝ)) (q := (2254657101771 / 100000000000000 : ℝ))
      (E := (cell12676 ⟨58, by decide⟩).energy) (xi := (10460200200167 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12676 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12676]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12676])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12676) (a := (41043770862913 / 50000000000000 : ℝ)) (b := (40625047419 / 25000000000000 : ℝ)) (q := (2254657101771 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12676])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12676])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12676]

theorem cert12676_59 : CellCertificate 12676 (887362248039349 / 10000000000000000 : ℝ) (66280977528967 / 40000000000000000 : ℝ) (10460200200167 / 312500000000000 : ℝ)
    (cell12676 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · have h := gap_lower (n := 12676) (a := (82053950927711 / 100000000000000 : ℝ)) (b := (40625047419 / 25000000000000 : ℝ)) (q := (2254661139999 / 100000000000000 : ℝ))
      (E := (cell12676 ⟨59, by decide⟩).energy) (xi := (10460200200167 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12676 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12676]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12676])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12676) (a := (82053950927711 / 100000000000000 : ℝ)) (b := (40625047419 / 25000000000000 : ℝ)) (q := (2254661139999 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12676])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12676])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12676]

theorem cert12677_40 : CellCertificate 12677 (22183355293917 / 250000000000000 : ℝ) (1656893684083513 / 1000000000000000000 : ℝ) (334699355336829 / 10000000000000000 : ℝ)
    (cell12677 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · have h := gap_lower (n := 12677) (a := (5168509813489 / 6250000000000 : ℝ)) (b := (162487214159 / 100000000000000 : ℝ)) (q := (1127230747053 / 50000000000000 : ℝ))
      (E := (cell12677 ⟨40, by decide⟩).energy) (xi := (334699355336829 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12677 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12677]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12677])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12677) (a := (5168509813489 / 6250000000000 : ℝ)) (b := (162487214159 / 100000000000000 : ℝ)) (q := (1127230747053 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12677])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12677])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12677]

theorem cert12677_41 : CellCertificate 12677 (22183355293917 / 250000000000000 : ℝ) (1656893684083513 / 1000000000000000000 : ℝ) (334699355336829 / 10000000000000000 : ℝ)
    (cell12677 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · have h := gap_lower (n := 12677) (a := (82662145737711 / 100000000000000 : ℝ)) (b := (162487214159 / 100000000000000 : ℝ)) (q := (2254465456611 / 100000000000000 : ℝ))
      (E := (cell12677 ⟨41, by decide⟩).energy) (xi := (334699355336829 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12677 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12677]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12677])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12677) (a := (82662145737711 / 100000000000000 : ℝ)) (b := (162487214159 / 100000000000000 : ℝ)) (q := (2254465456611 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12677])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12677])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12677]

theorem cert12677_42 : CellCertificate 12677 (22183355293917 / 250000000000000 : ℝ) (1656893684083513 / 1000000000000000000 : ℝ) (334699355336829 / 10000000000000000 : ℝ)
    (cell12677 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · have h := gap_lower (n := 12677) (a := (82628158081931 / 100000000000000 : ℝ)) (b := (162487214159 / 100000000000000 : ℝ)) (q := (563617368121 / 25000000000000 : ℝ))
      (E := (cell12677 ⟨42, by decide⟩).energy) (xi := (334699355336829 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12677 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12677]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12677])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12677) (a := (82628158081931 / 100000000000000 : ℝ)) (b := (162487214159 / 100000000000000 : ℝ)) (q := (563617368121 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12677])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12677])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12677]

theorem cert12677_43 : CellCertificate 12677 (22183355293917 / 250000000000000 : ℝ) (1656893684083513 / 1000000000000000000 : ℝ) (334699355336829 / 10000000000000000 : ℝ)
    (cell12677 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · have h := gap_lower (n := 12677) (a := (41297097009387 / 50000000000000 : ℝ)) (b := (162487214159 / 100000000000000 : ℝ)) (q := (1127236741099 / 50000000000000 : ℝ))
      (E := (cell12677 ⟨43, by decide⟩).energy) (xi := (334699355336829 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12677 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12677]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12677])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12677) (a := (41297097009387 / 50000000000000 : ℝ)) (b := (162487214159 / 100000000000000 : ℝ)) (q := (1127236741099 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12677])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12677])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12677]

theorem cert12677_44 : CellCertificate 12677 (22183355293917 / 250000000000000 : ℝ) (1656893684083513 / 1000000000000000000 : ℝ) (334699355336829 / 10000000000000000 : ℝ)
    (cell12677 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · have h := gap_lower (n := 12677) (a := (2064006337967 / 2500000000000 : ℝ)) (b := (162487214159 / 100000000000000 : ℝ)) (q := (2254477484751 / 100000000000000 : ℝ))
      (E := (cell12677 ⟨44, by decide⟩).energy) (xi := (334699355336829 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12677 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12677]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12677])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12677) (a := (2064006337967 / 2500000000000 : ℝ)) (b := (162487214159 / 100000000000000 : ℝ)) (q := (2254477484751 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12677])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12677])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12677]

theorem cert12677_45 : CellCertificate 12677 (22183355293917 / 250000000000000 : ℝ) (1656893684083513 / 1000000000000000000 : ℝ) (334699355336829 / 10000000000000000 : ℝ)
    (cell12677 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · have h := gap_lower (n := 12677) (a := (82526336552241 / 100000000000000 : ℝ)) (b := (162487214159 / 100000000000000 : ℝ)) (q := (1127240739461 / 50000000000000 : ℝ))
      (E := (cell12677 ⟨45, by decide⟩).energy) (xi := (334699355336829 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12677 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12677]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12677])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12677) (a := (82526336552241 / 100000000000000 : ℝ)) (b := (162487214159 / 100000000000000 : ℝ)) (q := (1127240739461 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12677])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12677])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12677]

theorem cert12677_46 : CellCertificate 12677 (22183355293917 / 250000000000000 : ℝ) (1656893684083513 / 1000000000000000000 : ℝ) (334699355336829 / 10000000000000000 : ℝ)
    (cell12677 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · have h := gap_lower (n := 12677) (a := (41246221545097 / 50000000000000 : ℝ)) (b := (162487214159 / 100000000000000 : ℝ)) (q := (2254485522161 / 100000000000000 : ℝ))
      (E := (cell12677 ⟨46, by decide⟩).energy) (xi := (334699355336829 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12677 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12677]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12677])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12677) (a := (41246221545097 / 50000000000000 : ℝ)) (b := (162487214159 / 100000000000000 : ℝ)) (q := (2254485522161 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12677])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12677])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12677]

theorem cert12677_47 : CellCertificate 12677 (22183355293917 / 250000000000000 : ℝ) (1656893684083513 / 1000000000000000000 : ℝ) (334699355336829 / 10000000000000000 : ℝ)
    (cell12677 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · have h := gap_lower (n := 12677) (a := (82458573103423 / 100000000000000 : ℝ)) (b := (162487214159 / 100000000000000 : ℝ)) (q := (225448949507 / 10000000000000 : ℝ))
      (E := (cell12677 ⟨47, by decide⟩).energy) (xi := (334699355336829 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12677 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12677]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12677])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12677) (a := (82458573103423 / 100000000000000 : ℝ)) (b := (162487214159 / 100000000000000 : ℝ)) (q := (225448949507 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12677])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12677])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12677]

theorem cert12677_48 : CellCertificate 12677 (22183355293917 / 250000000000000 : ℝ) (1656893684083513 / 1000000000000000000 : ℝ) (334699355336829 / 10000000000000000 : ℝ)
    (cell12677 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · have h := gap_lower (n := 12677) (a := (82424726562961 / 100000000000000 : ℝ)) (b := (162487214159 / 100000000000000 : ℝ)) (q := (90179740543 / 4000000000000 : ℝ))
      (E := (cell12677 ⟨48, by decide⟩).energy) (xi := (334699355336829 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12677 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12677]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12677])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12677) (a := (82424726562961 / 100000000000000 : ℝ)) (b := (162487214159 / 100000000000000 : ℝ)) (q := (90179740543 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12677])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12677])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12677]

theorem cert12677_49 : CellCertificate 12677 (22183355293917 / 250000000000000 : ℝ) (1656893684083513 / 1000000000000000000 : ℝ) (334699355336829 / 10000000000000000 : ℝ)
    (cell12677 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · have h := gap_lower (n := 12677) (a := (5149431464999 / 6250000000000 : ℝ)) (b := (162487214159 / 100000000000000 : ℝ)) (q := (225449751671 / 10000000000000 : ℝ))
      (E := (cell12677 ⟨49, by decide⟩).energy) (xi := (334699355336829 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12677 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12677]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12677])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12677) (a := (5149431464999 / 6250000000000 : ℝ)) (b := (162487214159 / 100000000000000 : ℝ)) (q := (225449751671 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12677])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12677])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12677]

theorem cert12677_50 : CellCertificate 12677 (22183355293917 / 250000000000000 : ℝ) (1656893684083513 / 1000000000000000000 : ℝ) (334699355336829 / 10000000000000000 : ℝ)
    (cell12677 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · have h := gap_lower (n := 12677) (a := (41178551852907 / 50000000000000 : ℝ)) (b := (162487214159 / 100000000000000 : ℝ)) (q := (2254501502181 / 100000000000000 : ℝ))
      (E := (cell12677 ⟨50, by decide⟩).energy) (xi := (334699355336829 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12677 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12677]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12677])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12677) (a := (41178551852907 / 50000000000000 : ℝ)) (b := (162487214159 / 100000000000000 : ℝ)) (q := (2254501502181 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12677])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12677])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12677]

theorem cert12677_51 : CellCertificate 12677 (22183355293917 / 250000000000000 : ℝ) (1656893684083513 / 1000000000000000000 : ℝ) (334699355336829 / 10000000000000000 : ℝ)
    (cell12677 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · have h := gap_lower (n := 12677) (a := (16464665466383 / 20000000000000 : ℝ)) (b := (162487214159 / 100000000000000 : ℝ)) (q := (1127252763243 / 50000000000000 : ℝ))
      (E := (cell12677 ⟨51, by decide⟩).energy) (xi := (334699355336829 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12677 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12677]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12677])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12677) (a := (16464665466383 / 20000000000000 : ℝ)) (b := (162487214159 / 100000000000000 : ℝ)) (q := (1127252763243 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12677])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12677])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12677]

theorem cert12677_52 : CellCertificate 12677 (22183355293917 / 250000000000000 : ℝ) (1656893684083513 / 1000000000000000000 : ℝ) (334699355336829 / 10000000000000000 : ℝ)
    (cell12677 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · have h := gap_lower (n := 12677) (a := (10286196786237 / 12500000000000 : ℝ)) (b := (162487214159 / 100000000000000 : ℝ)) (q := (2254509527949 / 100000000000000 : ℝ))
      (E := (cell12677 ⟨52, by decide⟩).energy) (xi := (334699355336829 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12677 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12677]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12677])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12677) (a := (10286196786237 / 12500000000000 : ℝ)) (b := (162487214159 / 100000000000000 : ℝ)) (q := (2254509527949 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12677])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12677])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12677]

theorem cert12677_53 : CellCertificate 12677 (22183355293917 / 250000000000000 : ℝ) (1656893684083513 / 1000000000000000000 : ℝ) (334699355336829 / 10000000000000000 : ℝ)
    (cell12677 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · have h := gap_lower (n := 12677) (a := (82255844551507 / 100000000000000 : ℝ)) (b := (162487214159 / 100000000000000 : ℝ)) (q := (2254513562691 / 100000000000000 : ℝ))
      (E := (cell12677 ⟨53, by decide⟩).energy) (xi := (334699355336829 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12677 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12677]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12677])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12677) (a := (82255844551507 / 100000000000000 : ℝ)) (b := (162487214159 / 100000000000000 : ℝ)) (q := (2254513562691 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12677])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12677])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12677]

theorem cert12677_54 : CellCertificate 12677 (22183355293917 / 250000000000000 : ℝ) (1656893684083513 / 1000000000000000000 : ℝ) (334699355336829 / 10000000000000000 : ℝ)
    (cell12677 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · have h := gap_lower (n := 12677) (a := (82222138088639 / 100000000000000 : ℝ)) (b := (162487214159 / 100000000000000 : ℝ)) (q := (225451756857 / 10000000000000 : ℝ))
      (E := (cell12677 ⟨54, by decide⟩).energy) (xi := (334699355336829 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12677 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12677]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12677])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12677) (a := (82222138088639 / 100000000000000 : ℝ)) (b := (162487214159 / 100000000000000 : ℝ)) (q := (225451756857 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12677])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12677])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12677]

theorem cert12677_55 : CellCertificate 12677 (22183355293917 / 250000000000000 : ℝ) (1656893684083513 / 1000000000000000000 : ℝ) (334699355336829 / 10000000000000000 : ℝ)
    (cell12677 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · have h := gap_lower (n := 12677) (a := (20547113718331 / 25000000000000 : ℝ)) (b := (162487214159 / 100000000000000 : ℝ)) (q := (2254521542237 / 100000000000000 : ℝ))
      (E := (cell12677 ⟨55, by decide⟩).energy) (xi := (334699355336829 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12677 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12677]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12677])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12677) (a := (20547113718331 / 25000000000000 : ℝ)) (b := (162487214159 / 100000000000000 : ℝ)) (q := (2254521542237 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12677])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12677])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12677]

theorem cert12677_56 : CellCertificate 12677 (22183355293917 / 250000000000000 : ℝ) (1656893684083513 / 1000000000000000000 : ℝ) (334699355336829 / 10000000000000000 : ℝ)
    (cell12677 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · have h := gap_lower (n := 12677) (a := (41077397438867 / 50000000000000 : ℝ)) (b := (162487214159 / 100000000000000 : ℝ)) (q := (450905107851 / 20000000000000 : ℝ))
      (E := (cell12677 ⟨56, by decide⟩).energy) (xi := (334699355336829 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12677 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12677]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12677])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12677) (a := (41077397438867 / 50000000000000 : ℝ)) (b := (162487214159 / 100000000000000 : ℝ)) (q := (450905107851 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12677])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12677])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12677]

theorem cert12677_57 : CellCertificate 12677 (22183355293917 / 250000000000000 : ℝ) (1656893684083513 / 1000000000000000000 : ℝ) (334699355336829 / 10000000000000000 : ℝ)
    (cell12677 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · have h := gap_lower (n := 12677) (a := (82121158074179 / 100000000000000 : ℝ)) (b := (162487214159 / 100000000000000 : ℝ)) (q := (2254529555929 / 100000000000000 : ℝ))
      (E := (cell12677 ⟨57, by decide⟩).energy) (xi := (334699355336829 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12677 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12677]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12677])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12677) (a := (82121158074179 / 100000000000000 : ℝ)) (b := (162487214159 / 100000000000000 : ℝ)) (q := (2254529555929 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12677])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12677])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12677]

theorem cert12677_58 : CellCertificate 12677 (22183355293917 / 250000000000000 : ℝ) (1656893684083513 / 1000000000000000000 : ℝ) (334699355336829 / 10000000000000000 : ℝ)
    (cell12677 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · have h := gap_lower (n := 12677) (a := (82087544435107 / 100000000000000 : ℝ)) (b := (162487214159 / 100000000000000 : ℝ)) (q := (1127266794179 / 50000000000000 : ℝ))
      (E := (cell12677 ⟨58, by decide⟩).energy) (xi := (334699355336829 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12677 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12677]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12677])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12677) (a := (82087544435107 / 100000000000000 : ℝ)) (b := (162487214159 / 100000000000000 : ℝ)) (q := (1127266794179 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12677])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12677])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12677]

theorem cert12677_59 : CellCertificate 12677 (22183355293917 / 250000000000000 : ℝ) (1656893684083513 / 1000000000000000000 : ℝ) (334699355336829 / 10000000000000000 : ℝ)
    (cell12677 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · have h := gap_lower (n := 12677) (a := (5128372120819 / 6250000000000 : ℝ)) (b := (162487214159 / 100000000000000 : ℝ)) (q := (2254537573241 / 100000000000000 : ℝ))
      (E := (cell12677 ⟨59, by decide⟩).energy) (xi := (334699355336829 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12677 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12677]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12677])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12677) (a := (5128372120819 / 6250000000000 : ℝ)) (b := (162487214159 / 100000000000000 : ℝ)) (q := (2254537573241 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12677])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12677])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12677]

theorem cert12678_40 : CellCertificate 12678 (887306179721403 / 10000000000000000 : ℝ) (1656762950576577 / 1000000000000000000 : ℝ) (334672308702881 / 10000000000000000 : ℝ)
    (cell12678 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · have h := gap_lower (n := 12678) (a := (330784617303 / 400000000000 : ℝ)) (b := (16247424073 / 10000000000000 : ℝ)) (q := (1127168994869 / 50000000000000 : ℝ))
      (E := (cell12678 ⟨40, by decide⟩).energy) (xi := (334672308702881 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12678 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12678]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12678])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12678) (a := (330784617303 / 400000000000 : ℝ)) (b := (16247424073 / 10000000000000 : ℝ)) (q := (1127168994869 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12678])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12678])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12678]

theorem cert12678_41 : CellCertificate 12678 (887306179721403 / 10000000000000000 : ℝ) (1656762950576577 / 1000000000000000000 : ℝ) (334672308702881 / 10000000000000000 : ℝ)
    (cell12678 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · have h := gap_lower (n := 12678) (a := (82662143351141 / 100000000000000 : ℝ)) (b := (16247424073 / 10000000000000 : ℝ)) (q := (90173677829 / 4000000000000 : ℝ))
      (E := (cell12678 ⟨41, by decide⟩).energy) (xi := (334672308702881 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12678 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12678]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12678])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12678) (a := (82662143351141 / 100000000000000 : ℝ)) (b := (16247424073 / 10000000000000 : ℝ)) (q := (90173677829 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12678])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12678])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12678]

theorem cert12678_42 : CellCertificate 12678 (887306179721403 / 10000000000000000 : ℝ) (1656762950576577 / 1000000000000000000 : ℝ) (334672308702881 / 10000000000000000 : ℝ)
    (cell12678 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · have h := gap_lower (n := 12678) (a := (16525631199689 / 20000000000000 : ℝ)) (b := (16247424073 / 10000000000000 : ℝ)) (q := (2254345955777 / 100000000000000 : ℝ))
      (E := (cell12678 ⟨42, by decide⟩).energy) (xi := (334672308702881 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12678 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12678]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12678])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12678) (a := (16525631199689 / 20000000000000 : ℝ)) (b := (16247424073 / 10000000000000 : ℝ)) (q := (2254345955777 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12678])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12678])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12678]

theorem cert12678_43 : CellCertificate 12678 (887306179721403 / 10000000000000000 : ℝ) (1656762950576577 / 1000000000000000000 : ℝ) (334672308702881 / 10000000000000000 : ℝ)
    (cell12678 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · have h := gap_lower (n := 12678) (a := (41297096118977 / 50000000000000 : ℝ)) (b := (16247424073 / 10000000000000 : ℝ)) (q := (2254349960363 / 100000000000000 : ℝ))
      (E := (cell12678 ⟨43, by decide⟩).energy) (xi := (334672308702881 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12678 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12678]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12678])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12678) (a := (41297096118977 / 50000000000000 : ℝ)) (b := (16247424073 / 10000000000000 : ℝ)) (q := (2254349960363 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12678])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12678])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12678]

theorem cert12678_44 : CellCertificate 12678 (887306179721403 / 10000000000000000 : ℝ) (1656762950576577 / 1000000000000000000 : ℝ) (334672308702881 / 10000000000000000 : ℝ)
    (cell12678 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · have h := gap_lower (n := 12678) (a := (8256025204011 / 10000000000000 : ℝ)) (b := (16247424073 / 10000000000000 : ℝ)) (q := (2254353958481 / 100000000000000 : ℝ))
      (E := (cell12678 ⟨44, by decide⟩).energy) (xi := (334672308702881 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12678 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12678]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12678])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12678) (a := (8256025204011 / 10000000000000 : ℝ)) (b := (16247424073 / 10000000000000 : ℝ)) (q := (2254353958481 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12678])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12678])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12678]

theorem cert12678_45 : CellCertificate 12678 (887306179721403 / 10000000000000000 : ℝ) (1656762950576577 / 1000000000000000000 : ℝ) (334672308702881 / 10000000000000000 : ℝ)
    (cell12678 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · have h := gap_lower (n := 12678) (a := (82526335375503 / 100000000000000 : ℝ)) (b := (16247424073 / 10000000000000 : ℝ)) (q := (2254358007773 / 100000000000000 : ℝ))
      (E := (cell12678 ⟨45, by decide⟩).energy) (xi := (334672308702881 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12678 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12678]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12678])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12678) (a := (82526335375503 / 100000000000000 : ℝ)) (b := (16247424073 / 10000000000000 : ℝ)) (q := (2254358007773 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12678])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12678])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12678]

theorem cert12678_46 : CellCertificate 12678 (887306179721403 / 10000000000000000 : ℝ) (1656762950576577 / 1000000000000000000 : ℝ) (334672308702881 / 10000000000000000 : ℝ)
    (cell12678 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · have h := gap_lower (n := 12678) (a := (10311555276859 / 12500000000000 : ℝ)) (b := (16247424073 / 10000000000000 : ℝ)) (q := (22543619891 / 1000000000000 : ℝ))
      (E := (cell12678 ⟨46, by decide⟩).energy) (xi := (334672308702881 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12678 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12678]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12678])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12678) (a := (10311555276859 / 12500000000000 : ℝ)) (b := (16247424073 / 10000000000000 : ℝ)) (q := (22543619891 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12678])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12678])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12678]

theorem cert12678_47 : CellCertificate 12678 (887306179721403 / 10000000000000000 : ℝ) (1656762950576577 / 1000000000000000000 : ℝ) (334672308702881 / 10000000000000000 : ℝ)
    (cell12678 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · have h := gap_lower (n := 12678) (a := (82458572529103 / 100000000000000 : ℝ)) (b := (16247424073 / 10000000000000 : ℝ)) (q := (2254366018559 / 100000000000000 : ℝ))
      (E := (cell12678 ⟨47, by decide⟩).energy) (xi := (334672308702881 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12678 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12678]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12678])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12678) (a := (82458572529103 / 100000000000000 : ℝ)) (b := (16247424073 / 10000000000000 : ℝ)) (q := (2254366018559 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12678])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12678])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12678]

theorem cert12678_48 : CellCertificate 12678 (887306179721403 / 10000000000000000 : ℝ) (1656762950576577 / 1000000000000000000 : ℝ) (334672308702881 / 10000000000000000 : ℝ)
    (cell12678 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · have h := gap_lower (n := 12678) (a := (82424726289227 / 100000000000000 : ℝ)) (b := (16247424073 / 10000000000000 : ℝ)) (q := (2254369976487 / 100000000000000 : ℝ))
      (E := (cell12678 ⟨48, by decide⟩).energy) (xi := (334672308702881 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12678 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12678]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12678])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12678) (a := (82424726289227 / 100000000000000 : ℝ)) (b := (16247424073 / 10000000000000 : ℝ)) (q := (2254369976487 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12678])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12678])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12678]

theorem cert12678_49 : CellCertificate 12678 (887306179721403 / 10000000000000000 : ℝ) (1656762950576577 / 1000000000000000000 : ℝ) (334672308702881 / 10000000000000000 : ℝ)
    (cell12678 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · have h := gap_lower (n := 12678) (a := (10298862933303 / 12500000000000 : ℝ)) (b := (16247424073 / 10000000000000 : ℝ)) (q := (563593494661 / 25000000000000 : ℝ))
      (E := (cell12678 ⟨49, by decide⟩).energy) (xi := (334672308702881 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12678 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12678]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12678])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12678) (a := (10298862933303 / 12500000000000 : ℝ)) (b := (16247424073 / 10000000000000 : ℝ)) (q := (563593494661 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12678])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12678])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12678]

theorem cert12678_50 : CellCertificate 12678 (887306179721403 / 10000000000000000 : ℝ) (1656762950576577 / 1000000000000000000 : ℝ) (334672308702881 / 10000000000000000 : ℝ)
    (cell12678 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · have h := gap_lower (n := 12678) (a := (41178552016007 / 50000000000000 : ℝ)) (b := (16247424073 / 10000000000000 : ℝ)) (q := (2254378022807 / 100000000000000 : ℝ))
      (E := (cell12678 ⟨50, by decide⟩).energy) (xi := (334672308702881 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12678 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12678]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12678])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12678) (a := (41178552016007 / 50000000000000 : ℝ)) (b := (16247424073 / 10000000000000 : ℝ)) (q := (2254378022807 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12678])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12678])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12678]

theorem cert12678_51 : CellCertificate 12678 (887306179721403 / 10000000000000000 : ℝ) (1656762950576577 / 1000000000000000000 : ℝ) (334672308702881 / 10000000000000000 : ℝ)
    (cell12678 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · have h := gap_lower (n := 12678) (a := (10290415994683 / 12500000000000 : ℝ)) (b := (16247424073 / 10000000000000 : ℝ)) (q := (225438198853 / 10000000000000 : ℝ))
      (E := (cell12678 ⟨51, by decide⟩).energy) (xi := (334672308702881 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12678 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12678]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12678])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12678) (a := (10290415994683 / 12500000000000 : ℝ)) (b := (16247424073 / 10000000000000 : ℝ)) (q := (225438198853 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12678])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12678])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12678]

theorem cert12678_52 : CellCertificate 12678 (887306179721403 / 10000000000000000 : ℝ) (1656762950576577 / 1000000000000000000 : ℝ) (334672308702881 / 10000000000000000 : ℝ)
    (cell12678 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · have h := gap_lower (n := 12678) (a := (82289575214381 / 100000000000000 : ℝ)) (b := (16247424073 / 10000000000000 : ℝ)) (q := (2254385991081 / 100000000000000 : ℝ))
      (E := (cell12678 ⟨52, by decide⟩).energy) (xi := (334672308702881 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12678 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12678]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12678])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12678) (a := (82289575214381 / 100000000000000 : ℝ)) (b := (16247424073 / 10000000000000 : ℝ)) (q := (2254385991081 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12678])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12678])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12678]

theorem cert12678_53 : CellCertificate 12678 (887306179721403 / 10000000000000000 : ℝ) (1656762950576577 / 1000000000000000000 : ℝ) (334672308702881 / 10000000000000000 : ℝ)
    (cell12678 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · have h := gap_lower (n := 12678) (a := (41127922887259 / 50000000000000 : ℝ)) (b := (16247424073 / 10000000000000 : ℝ)) (q := (1127195013799 / 50000000000000 : ℝ))
      (E := (cell12678 ⟨53, by decide⟩).energy) (xi := (334672308702881 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12678 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12678]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12678])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12678) (a := (41127922887259 / 50000000000000 : ℝ)) (b := (16247424073 / 10000000000000 : ℝ)) (q := (1127195013799 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12678])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12678])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12678]

theorem cert12678_54 : CellCertificate 12678 (887306179721403 / 10000000000000000 : ℝ) (1656762950576577 / 1000000000000000000 : ℝ) (334672308702881 / 10000000000000000 : ℝ)
    (cell12678 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · have h := gap_lower (n := 12678) (a := (41111069804883 / 50000000000000 : ℝ)) (b := (16247424073 / 10000000000000 : ℝ)) (q := (1127197017969 / 50000000000000 : ℝ))
      (E := (cell12678 ⟨54, by decide⟩).energy) (xi := (334672308702881 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12678 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12678]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12678])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12678) (a := (41111069804883 / 50000000000000 : ℝ)) (b := (16247424073 / 10000000000000 : ℝ)) (q := (1127197017969 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12678])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12678])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12678]

theorem cert12678_55 : CellCertificate 12678 (887306179721403 / 10000000000000000 : ℝ) (1656762950576577 / 1000000000000000000 : ℝ) (334672308702881 / 10000000000000000 : ℝ)
    (cell12678 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · have h := gap_lower (n := 12678) (a := (41094228346079 / 50000000000000 : ℝ)) (b := (16247424073 / 10000000000000 : ℝ)) (q := (140899875797 / 6250000000000 : ℝ))
      (E := (cell12678 ⟨55, by decide⟩).energy) (xi := (334672308702881 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12678 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12678]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12678])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12678) (a := (41094228346079 / 50000000000000 : ℝ)) (b := (16247424073 / 10000000000000 : ℝ)) (q := (140899875797 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12678])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12678])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12678]

theorem cert12678_56 : CellCertificate 12678 (887306179721403 / 10000000000000000 : ℝ) (1656762950576577 / 1000000000000000000 : ℝ) (334672308702881 / 10000000000000000 : ℝ)
    (cell12678 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · have h := gap_lower (n := 12678) (a := (41077398496933 / 50000000000000 : ℝ)) (b := (16247424073 / 10000000000000 : ℝ)) (q := (1127201006801 / 50000000000000 : ℝ))
      (E := (cell12678 ⟨56, by decide⟩).energy) (xi := (334672308702881 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12678 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12678]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12678])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12678) (a := (41077398496933 / 50000000000000 : ℝ)) (b := (16247424073 / 10000000000000 : ℝ)) (q := (1127201006801 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12678])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12678])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12678]

theorem cert12678_57 : CellCertificate 12678 (887306179721403 / 10000000000000000 : ℝ) (1656762950576577 / 1000000000000000000 : ℝ) (334672308702881 / 10000000000000000 : ℝ)
    (cell12678 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · have h := gap_lower (n := 12678) (a := (82121160487201 / 100000000000000 : ℝ)) (b := (16247424073 / 10000000000000 : ℝ)) (q := (2254406034793 / 100000000000000 : ℝ))
      (E := (cell12678 ⟨57, by decide⟩).energy) (xi := (334672308702881 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12678 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12678]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12678])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12678) (a := (82121160487201 / 100000000000000 : ℝ)) (b := (16247424073 / 10000000000000 : ℝ)) (q := (2254406034793 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12678])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12678])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12678]

theorem cert12678_58 : CellCertificate 12678 (887306179721403 / 10000000000000000 : ℝ) (1656762950576577 / 1000000000000000000 : ℝ) (334672308702881 / 10000000000000000 : ℝ)
    (cell12678 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · have h := gap_lower (n := 12678) (a := (20521886786153 / 25000000000000 : ℝ)) (b := (16247424073 / 10000000000000 : ℝ)) (q := (1127205036211 / 50000000000000 : ℝ))
      (E := (cell12678 ⟨58, by decide⟩).energy) (xi := (334672308702881 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12678 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12678]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12678])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12678) (a := (20521886786153 / 25000000000000 : ℝ)) (b := (16247424073 / 10000000000000 : ℝ)) (q := (1127205036211 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12678])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12678])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12678]

theorem cert12678_59 : CellCertificate 12678 (887306179721403 / 10000000000000000 : ℝ) (1656762950576577 / 1000000000000000000 : ℝ) (334672308702881 / 10000000000000000 : ℝ)
    (cell12678 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · have h := gap_lower (n := 12678) (a := (16410791387737 / 20000000000000 : ℝ)) (b := (16247424073 / 10000000000000 : ℝ)) (q := (2254414063189 / 100000000000000 : ℝ))
      (E := (cell12678 ⟨59, by decide⟩).energy) (xi := (334672308702881 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12678 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12678]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12678])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12678) (a := (16410791387737 / 20000000000000 : ℝ)) (b := (16247424073 / 10000000000000 : ℝ)) (q := (2254414063189 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12678])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12678])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12678]

theorem cert12679_40 : CellCertificate 12679 (443639075966253 / 5000000000000000 : ℝ) (414158059424621 / 250000000000000000 : ℝ) (334645266502311 / 10000000000000000 : ℝ)
    (cell12679 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · have h := gap_lower (n := 12679) (a := (16539230327311 / 20000000000000 : ℝ)) (b := (40615317347 / 25000000000000 : ℝ)) (q := (2254214482177 / 100000000000000 : ℝ))
      (E := (cell12679 ⟨40, by decide⟩).energy) (xi := (334645266502311 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12679 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12679]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12679])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12679) (a := (16539230327311 / 20000000000000 : ℝ)) (b := (40615317347 / 25000000000000 : ℝ)) (q := (2254214482177 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12679])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12679])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12679]

theorem cert12679_41 : CellCertificate 12679 (443639075966253 / 5000000000000000 : ℝ) (414158059424621 / 250000000000000000 : ℝ) (334645266502311 / 10000000000000000 : ℝ)
    (cell12679 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · have h := gap_lower (n := 12679) (a := (82662140965413 / 100000000000000 : ℝ)) (b := (40615317347 / 25000000000000 : ℝ)) (q := (2254218490453 / 100000000000000 : ℝ))
      (E := (cell12679 ⟨41, by decide⟩).energy) (xi := (334645266502311 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12679 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12679]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12679])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12679) (a := (82662140965413 / 100000000000000 : ℝ)) (b := (40615317347 / 25000000000000 : ℝ)) (q := (2254218490453 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12679])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12679])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12679]

theorem cert12679_42 : CellCertificate 12679 (443639075966253 / 5000000000000000 : ℝ) (414158059424621 / 250000000000000000 : ℝ) (334645266502311 / 10000000000000000 : ℝ)
    (cell12679 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · have h := gap_lower (n := 12679) (a := (20657038478941 / 25000000000000 : ℝ)) (b := (40615317347 / 25000000000000 : ℝ)) (q := (281777811843 / 12500000000000 : ℝ))
      (E := (cell12679 ⟨42, by decide⟩).energy) (xi := (334645266502311 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12679 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12679]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12679])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12679) (a := (20657038478941 / 25000000000000 : ℝ)) (b := (40615317347 / 25000000000000 : ℝ)) (q := (281777811843 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12679])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12679])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12679]

theorem cert12679_43 : CellCertificate 12679 (443639075966253 / 5000000000000000 : ℝ) (414158059424621 / 250000000000000000 : ℝ) (334645266502311 / 10000000000000000 : ℝ)
    (cell12679 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · have h := gap_lower (n := 12679) (a := (41297095228951 / 50000000000000 : ℝ)) (b := (40615317347 / 25000000000000 : ℝ)) (q := (281778311783 / 12500000000000 : ℝ))
      (E := (cell12679 ⟨43, by decide⟩).energy) (xi := (334645266502311 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12679 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12679]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12679])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12679) (a := (41297095228951 / 50000000000000 : ℝ)) (b := (40615317347 / 25000000000000 : ℝ)) (q := (281778311783 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12679])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12679])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12679]

theorem cert12679_44 : CellCertificate 12679 (443639075966253 / 5000000000000000 : ℝ) (414158059424621 / 250000000000000000 : ℝ) (334645266502311 / 10000000000000000 : ℝ)
    (cell12679 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · have h := gap_lower (n := 12679) (a := (8256025056227 / 10000000000000 : ℝ)) (b := (40615317347 / 25000000000000 : ℝ)) (q := (281778811001 / 12500000000000 : ℝ))
      (E := (cell12679 ⟨44, by decide⟩).energy) (xi := (334645266502311 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12679 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12679]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12679])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12679) (a := (8256025056227 / 10000000000000 : ℝ)) (b := (40615317347 / 25000000000000 : ℝ)) (q := (281778811001 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12679])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12679])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12679]

theorem cert12679_45 : CellCertificate 12679 (443639075966253 / 5000000000000000 : ℝ) (414158059424621 / 250000000000000000 : ℝ) (334645266502311 / 10000000000000000 : ℝ)
    (cell12679 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · have h := gap_lower (n := 12679) (a := (82526334199459 / 100000000000000 : ℝ)) (b := (40615317347 / 25000000000000 : ℝ)) (q := (2254234533619 / 100000000000000 : ℝ))
      (E := (cell12679 ⟨45, by decide⟩).energy) (xi := (334645266502311 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12679 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12679]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12679])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12679) (a := (82526334199459 / 100000000000000 : ℝ)) (b := (40615317347 / 25000000000000 : ℝ)) (q := (2254234533619 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12679])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12679])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12679]

theorem cert12679_46 : CellCertificate 12679 (443639075966253 / 5000000000000000 : ℝ) (414158059424621 / 250000000000000000 : ℝ) (334645266502311 / 10000000000000000 : ℝ)
    (cell12679 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · have h := gap_lower (n := 12679) (a := (5155777583763 / 6250000000000 : ℝ)) (b := (40615317347 / 25000000000000 : ℝ)) (q := (1127119255979 / 50000000000000 : ℝ))
      (E := (cell12679 ⟨46, by decide⟩).energy) (xi := (334645266502311 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12679 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12679]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12679])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12679) (a := (5155777583763 / 6250000000000 : ℝ)) (b := (40615317347 / 25000000000000 : ℝ)) (q := (1127119255979 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12679])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12679])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12679]

theorem cert12679_47 : CellCertificate 12679 (443639075966253 / 5000000000000000 : ℝ) (414158059424621 / 250000000000000000 : ℝ) (334645266502311 / 10000000000000000 : ℝ)
    (cell12679 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · have h := gap_lower (n := 12679) (a := (82458571955403 / 100000000000000 : ℝ)) (b := (40615317347 / 25000000000000 : ℝ)) (q := (28178031739 / 1250000000000 : ℝ))
      (E := (cell12679 ⟨47, by decide⟩).energy) (xi := (334645266502311 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12679 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12679]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12679])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12679) (a := (82458571955403 / 100000000000000 : ℝ)) (b := (40615317347 / 25000000000000 : ℝ)) (q := (28178031739 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12679])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12679])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12679]

theorem cert12679_48 : CellCertificate 12679 (443639075966253 / 5000000000000000 : ℝ) (414158059424621 / 250000000000000000 : ℝ) (334645266502311 / 10000000000000000 : ℝ)
    (cell12679 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · have h := gap_lower (n := 12679) (a := (82424726016079 / 100000000000000 : ℝ)) (b := (40615317347 / 25000000000000 : ℝ)) (q := (2254246495439 / 100000000000000 : ℝ))
      (E := (cell12679 ⟨48, by decide⟩).energy) (xi := (334645266502311 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12679 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12679]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12679])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12679) (a := (82424726016079 / 100000000000000 : ℝ)) (b := (40615317347 / 25000000000000 : ℝ)) (q := (2254246495439 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12679])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12679])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12679]

theorem cert12679_49 : CellCertificate 12679 (443639075966253 / 5000000000000000 : ℝ) (414158059424621 / 250000000000000000 : ℝ) (334645266502311 / 10000000000000000 : ℝ)
    (cell12679 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · have h := gap_lower (n := 12679) (a := (20597725873353 / 25000000000000 : ℝ)) (b := (40615317347 / 25000000000000 : ℝ)) (q := (56356262417 / 2500000000000 : ℝ))
      (E := (cell12679 ⟨49, by decide⟩).energy) (xi := (334645266502311 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12679 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12679]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12679])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12679) (a := (20597725873353 / 25000000000000 : ℝ)) (b := (40615317347 / 25000000000000 : ℝ)) (q := (56356262417 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12679])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12679])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12679]

theorem cert12679_50 : CellCertificate 12679 (443639075966253 / 5000000000000000 : ℝ) (414158059424621 / 250000000000000000 : ℝ) (334645266502311 / 10000000000000000 : ℝ)
    (cell12679 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · have h := gap_lower (n := 12679) (a := (41178552179363 / 50000000000000 : ℝ)) (b := (40615317347 / 25000000000000 : ℝ)) (q := (1127127270307 / 50000000000000 : ℝ))
      (E := (cell12679 ⟨50, by decide⟩).energy) (xi := (334645266502311 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12679 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12679]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12679])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12679) (a := (41178552179363 / 50000000000000 : ℝ)) (b := (40615317347 / 25000000000000 : ℝ)) (q := (1127127270307 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12679])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12679])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12679]

theorem cert12679_51 : CellCertificate 12679 (443639075966253 / 5000000000000000 : ℝ) (414158059424621 / 250000000000000000 : ℝ) (334645266502311 / 10000000000000000 : ℝ)
    (cell12679 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · have h := gap_lower (n := 12679) (a := (1286302009117 / 1562500000000 : ℝ)) (b := (40615317347 / 25000000000000 : ℝ)) (q := (1127129253399 / 50000000000000 : ℝ))
      (E := (cell12679 ⟨51, by decide⟩).energy) (xi := (334645266502311 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12679 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12679]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12679])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12679) (a := (1286302009117 / 1562500000000 : ℝ)) (b := (40615317347 / 25000000000000 : ℝ)) (q := (1127129253399 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12679])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12679])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12679]

theorem cert12679_52 : CellCertificate 12679 (443639075966253 / 5000000000000000 : ℝ) (414158059424621 / 250000000000000000 : ℝ) (334645266502311 / 10000000000000000 : ℝ)
    (cell12679 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · have h := gap_lower (n := 12679) (a := (41144788069653 / 50000000000000 : ℝ)) (b := (40615317347 / 25000000000000 : ℝ)) (q := (563565642381 / 25000000000000 : ℝ))
      (E := (cell12679 ⟨52, by decide⟩).energy) (xi := (334645266502311 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12679 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12679]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12679])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12679) (a := (41144788069653 / 50000000000000 : ℝ)) (b := (40615317347 / 25000000000000 : ℝ)) (q := (563565642381 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12679])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12679])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12679]

theorem cert12679_53 : CellCertificate 12679 (443639075966253 / 5000000000000000 : ℝ) (414158059424621 / 250000000000000000 : ℝ) (334645266502311 / 10000000000000000 : ℝ)
    (cell12679 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · have h := gap_lower (n := 12679) (a := (82255846997933 / 100000000000000 : ℝ)) (b := (40615317347 / 25000000000000 : ℝ)) (q := (2254266548849 / 100000000000000 : ℝ))
      (E := (cell12679 ⟨53, by decide⟩).energy) (xi := (334645266502311 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12679 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12679]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12679])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12679) (a := (82255846997933 / 100000000000000 : ℝ)) (b := (40615317347 / 25000000000000 : ℝ)) (q := (2254266548849 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12679])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12679])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12679]

theorem cert12679_54 : CellCertificate 12679 (443639075966253 / 5000000000000000 : ℝ) (414158059424621 / 250000000000000000 : ℝ) (334645266502311 / 10000000000000000 : ℝ)
    (cell12679 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · have h := gap_lower (n := 12679) (a := (82222141131261 / 100000000000000 : ℝ)) (b := (40615317347 / 25000000000000 : ℝ)) (q := (2254270559711 / 100000000000000 : ℝ))
      (E := (cell12679 ⟨54, by decide⟩).energy) (xi := (334645266502311 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12679 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12679]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12679])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12679) (a := (82222141131261 / 100000000000000 : ℝ)) (b := (40615317347 / 25000000000000 : ℝ)) (q := (2254270559711 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12679])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12679])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12679]

theorem cert12679_55 : CellCertificate 12679 (443639075966253 / 5000000000000000 : ℝ) (414158059424621 / 250000000000000000 : ℝ) (334645266502311 / 10000000000000000 : ℝ)
    (cell12679 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · have h := gap_lower (n := 12679) (a := (82188458511323 / 100000000000000 : ℝ)) (b := (40615317347 / 25000000000000 : ℝ)) (q := (563568634933 / 25000000000000 : ℝ))
      (E := (cell12679 ⟨55, by decide⟩).energy) (xi := (334645266502311 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12679 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12679]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12679])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12679) (a := (82188458511323 / 100000000000000 : ℝ)) (b := (40615317347 / 25000000000000 : ℝ)) (q := (563568634933 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12679])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12679])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12679]

theorem cert12679_56 : CellCertificate 12679 (443639075966253 / 5000000000000000 : ℝ) (414158059424621 / 250000000000000000 : ℝ) (334645266502311 / 10000000000000000 : ℝ)
    (cell12679 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · have h := gap_lower (n := 12679) (a := (82154799110293 / 100000000000000 : ℝ)) (b := (40615317347 / 25000000000000 : ℝ)) (q := (1127139272237 / 50000000000000 : ℝ))
      (E := (cell12679 ⟨56, by decide⟩).energy) (xi := (334645266502311 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12679 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12679]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12679])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12679) (a := (82154799110293 / 100000000000000 : ℝ)) (b := (40615317347 / 25000000000000 : ℝ)) (q := (1127139272237 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12679])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12679])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12679]

theorem cert12679_57 : CellCertificate 12679 (443639075966253 / 5000000000000000 : ℝ) (414158059424621 / 250000000000000000 : ℝ) (334645266502311 / 10000000000000000 : ℝ)
    (cell12679 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · have h := gap_lower (n := 12679) (a := (41060581450241 / 50000000000000 : ℝ)) (b := (40615317347 / 25000000000000 : ℝ)) (q := (1127141285121 / 50000000000000 : ℝ))
      (E := (cell12679 ⟨57, by decide⟩).energy) (xi := (334645266502311 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12679 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12679]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12679])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12679) (a := (41060581450241 / 50000000000000 : ℝ)) (b := (40615317347 / 25000000000000 : ℝ)) (q := (1127141285121 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12679])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12679])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12679]

theorem cert12679_58 : CellCertificate 12679 (443639075966253 / 5000000000000000 : ℝ) (414158059424621 / 250000000000000000 : ℝ) (334645266502311 / 10000000000000000 : ℝ)
    (cell12679 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · have h := gap_lower (n := 12679) (a := (82087549854339 / 100000000000000 : ℝ)) (b := (40615317347 / 25000000000000 : ℝ)) (q := (450857310793 / 20000000000000 : ℝ))
      (E := (cell12679 ⟨58, by decide⟩).energy) (xi := (334645266502311 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12679 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12679]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12679])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12679) (a := (82087549854339 / 100000000000000 : ℝ)) (b := (40615317347 / 25000000000000 : ℝ)) (q := (450857310793 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12679])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12679])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12679]

theorem cert12679_59 : CellCertificate 12679 (443639075966253 / 5000000000000000 : ℝ) (414158059424621 / 250000000000000000 : ℝ) (334645266502311 / 10000000000000000 : ℝ)
    (cell12679 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · have h := gap_lower (n := 12679) (a := (82053959944453 / 100000000000000 : ℝ)) (b := (40615317347 / 25000000000000 : ℝ)) (q := (2254290609843 / 100000000000000 : ℝ))
      (E := (cell12679 ⟨59, by decide⟩).energy) (xi := (334645266502311 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12679 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12679]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12679])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12679) (a := (82053959944453 / 100000000000000 : ℝ)) (b := (40615317347 / 25000000000000 : ℝ)) (q := (2254290609843 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12679])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12679])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12679]

theorem cert12680_40 : CellCertificate 12680 (887250128388977 / 10000000000000000 : ℝ) (1617677290473 / 976562500000000 : ℝ) (66923645746787 / 2000000000000000 : ℝ)
    (cell12680 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · have h := gap_lower (n := 12680) (a := (41348074474119 / 50000000000000 : ℝ)) (b := (40612075033 / 25000000000000 : ℝ)) (q := (225409103017 / 10000000000000 : ℝ))
      (E := (cell12680 ⟨40, by decide⟩).energy) (xi := (66923645746787 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12680 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12680]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12680])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12680) (a := (41348074474119 / 50000000000000 : ℝ)) (b := (40612075033 / 25000000000000 : ℝ)) (q := (225409103017 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12680])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12680])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12680]

theorem cert12680_41 : CellCertificate 12680 (887250128388977 / 10000000000000000 : ℝ) (1617677290473 / 976562500000000 : ℝ) (66923645746787 / 2000000000000000 : ℝ)
    (cell12680 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · have h := gap_lower (n := 12680) (a := (3306485543221 / 4000000000000 : ℝ)) (b := (40612075033 / 25000000000000 : ℝ)) (q := (563523758007 / 25000000000000 : ℝ))
      (E := (cell12680 ⟨41, by decide⟩).energy) (xi := (66923645746787 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12680 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12680]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12680])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12680) (a := (3306485543221 / 4000000000000 : ℝ)) (b := (40612075033 / 25000000000000 : ℝ)) (q := (563523758007 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12680])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12680])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12680]

theorem cert12680_42 : CellCertificate 12680 (887250128388977 / 10000000000000000 : ℝ) (1617677290473 / 976562500000000 : ℝ) (66923645746787 / 2000000000000000 : ℝ)
    (cell12680 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · have h := gap_lower (n := 12680) (a := (82628151833887 / 100000000000000 : ℝ)) (b := (40612075033 / 25000000000000 : ℝ)) (q := (563524757649 / 25000000000000 : ℝ))
      (E := (cell12680 ⟨42, by decide⟩).energy) (xi := (66923645746787 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12680 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12680]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12680])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12680) (a := (82628151833887 / 100000000000000 : ℝ)) (b := (40612075033 / 25000000000000 : ℝ)) (q := (563524757649 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12680])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12680])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12680]

theorem cert12680_43 : CellCertificate 12680 (887250128388977 / 10000000000000000 : ℝ) (1617677290473 / 976562500000000 : ℝ) (66923645746787 / 2000000000000000 : ℝ)
    (cell12680 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · have h := gap_lower (n := 12680) (a := (41297094339309 / 50000000000000 : ℝ)) (b := (40612075033 / 25000000000000 : ℝ)) (q := (2254103083903 / 100000000000000 : ℝ))
      (E := (cell12680 ⟨43, by decide⟩).energy) (xi := (66923645746787 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12680 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12680]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12680])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12680) (a := (41297094339309 / 50000000000000 : ℝ)) (b := (40612075033 / 25000000000000 : ℝ)) (q := (2254103083903 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12680])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12680])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12680]

theorem cert12680_44 : CellCertificate 12680 (887250128388977 / 10000000000000000 : ℝ) (1617677290473 / 976562500000000 : ℝ) (66923645746787 / 2000000000000000 : ℝ)
    (cell12680 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · have h := gap_lower (n := 12680) (a := (41280124542581 / 50000000000000 : ℝ)) (b := (40612075033 / 25000000000000 : ℝ)) (q := (1127053536667 / 50000000000000 : ℝ))
      (E := (cell12680 ⟨44, by decide⟩).energy) (xi := (66923645746787 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12680 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12680]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12680])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12680) (a := (41280124542581 / 50000000000000 : ℝ)) (b := (40612075033 / 25000000000000 : ℝ)) (q := (1127053536667 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12680])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12680])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12680]

theorem cert12680_45 : CellCertificate 12680 (887250128388977 / 10000000000000000 : ℝ) (1617677290473 / 976562500000000 : ℝ) (66923645746787 / 2000000000000000 : ℝ)
    (cell12680 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · have h := gap_lower (n := 12680) (a := (82526333024109 / 100000000000000 : ℝ)) (b := (40612075033 / 25000000000000 : ℝ)) (q := (2254111056463 / 100000000000000 : ℝ))
      (E := (cell12680 ⟨45, by decide⟩).energy) (xi := (66923645746787 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12680 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12680]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12680])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12680) (a := (82526333024109 / 100000000000000 : ℝ)) (b := (40612075033 / 25000000000000 : ℝ)) (q := (2254111056463 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12680])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12680])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12680]

theorem cert12680_46 : CellCertificate 12680 (887250128388977 / 10000000000000000 : ℝ) (1617677290473 / 976562500000000 : ℝ) (66923645746787 / 2000000000000000 : ℝ)
    (cell12680 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · have h := gap_lower (n := 12680) (a := (82492440466201 / 100000000000000 : ℝ)) (b := (40612075033 / 25000000000000 : ℝ)) (q := (2254115090737 / 100000000000000 : ℝ))
      (E := (cell12680 ⟨46, by decide⟩).energy) (xi := (66923645746787 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12680 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12680]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12680])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12680) (a := (82492440466201 / 100000000000000 : ℝ)) (b := (40612075033 / 25000000000000 : ℝ)) (q := (2254115090737 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12680])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12680])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12680]

theorem cert12680_47 : CellCertificate 12680 (887250128388977 / 10000000000000000 : ℝ) (1617677290473 / 976562500000000 : ℝ) (66923645746787 / 2000000000000000 : ℝ)
    (cell12680 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · have h := gap_lower (n := 12680) (a := (41229285691163 / 50000000000000 : ℝ)) (b := (40612075033 / 25000000000000 : ℝ)) (q := (2254119056751 / 100000000000000 : ℝ))
      (E := (cell12680 ⟨47, by decide⟩).energy) (xi := (66923645746787 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12680 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12680]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12680])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12680) (a := (41229285691163 / 50000000000000 : ℝ)) (b := (40612075033 / 25000000000000 : ℝ)) (q := (2254119056751 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12680])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12680])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12680]

theorem cert12680_48 : CellCertificate 12680 (887250128388977 / 10000000000000000 : ℝ) (1617677290473 / 976562500000000 : ℝ) (66923645746787 / 2000000000000000 : ℝ)
    (cell12680 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · have h := gap_lower (n := 12680) (a := (16484945148703 / 20000000000000 : ℝ)) (b := (40612075033 / 25000000000000 : ℝ)) (q := (450824614087 / 20000000000000 : ℝ))
      (E := (cell12680 ⟨48, by decide⟩).energy) (xi := (66923645746787 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12680 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12680]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12680])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12680) (a := (16484945148703 / 20000000000000 : ℝ)) (b := (40612075033 / 25000000000000 : ℝ)) (q := (450824614087 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12680])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12680])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12680]

theorem cert12680_49 : CellCertificate 12680 (887250128388977 / 10000000000000000 : ℝ) (1617677290473 / 976562500000000 : ℝ) (66923645746787 / 2000000000000000 : ℝ)
    (cell12680 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · have h := gap_lower (n := 12680) (a := (82390903520949 / 100000000000000 : ℝ)) (b := (40612075033 / 25000000000000 : ℝ)) (q := (1127063535409 / 50000000000000 : ℝ))
      (E := (cell12680 ⟨49, by decide⟩).energy) (xi := (66923645746787 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12680 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12680]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12680])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12680) (a := (82390903520949 / 100000000000000 : ℝ)) (b := (40612075033 / 25000000000000 : ℝ)) (q := (1127063535409 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12680])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12680])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12680]

theorem cert12680_50 : CellCertificate 12680 (887250128388977 / 10000000000000000 : ℝ) (1617677290473 / 976562500000000 : ℝ) (66923645746787 / 2000000000000000 : ℝ)
    (cell12680 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · have h := gap_lower (n := 12680) (a := (82357104685951 / 100000000000000 : ℝ)) (b := (40612075033 / 25000000000000 : ℝ)) (q := (450826222917 / 20000000000000 : ℝ))
      (E := (cell12680 ⟨50, by decide⟩).energy) (xi := (66923645746787 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12680 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12680]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12680])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12680) (a := (82357104685951 / 100000000000000 : ℝ)) (b := (40612075033 / 25000000000000 : ℝ)) (q := (450826222917 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12680])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12680])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12680]

theorem cert12680_51 : CellCertificate 12680 (887250128388977 / 10000000000000000 : ℝ) (1617677290473 / 976562500000000 : ℝ) (66923645746787 / 2000000000000000 : ℝ)
    (cell12680 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · have h := gap_lower (n := 12680) (a := (20580832302497 / 25000000000000 : ℝ)) (b := (40612075033 / 25000000000000 : ℝ)) (q := (2254135081291 / 100000000000000 : ℝ))
      (E := (cell12680 ⟨51, by decide⟩).energy) (xi := (66923645746787 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12680 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12680]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12680])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12680) (a := (20580832302497 / 25000000000000 : ℝ)) (b := (40612075033 / 25000000000000 : ℝ)) (q := (2254135081291 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12680])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12680])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12680]

theorem cert12680_52 : CellCertificate 12680 (887250128388977 / 10000000000000000 : ℝ) (1617677290473 / 976562500000000 : ℝ) (66923645746787 / 2000000000000000 : ℝ)
    (cell12680 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · have h := gap_lower (n := 12680) (a := (82289577064671 / 100000000000000 : ℝ)) (b := (40612075033 / 25000000000000 : ℝ)) (q := (2254139086197 / 100000000000000 : ℝ))
      (E := (cell12680 ⟨52, by decide⟩).energy) (xi := (66923645746787 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12680 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12680]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12680])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12680) (a := (82289577064671 / 100000000000000 : ℝ)) (b := (40612075033 / 25000000000000 : ℝ)) (q := (2254139086197 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12680])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12680])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12680]

theorem cert12680_53 : CellCertificate 12680 (887250128388977 / 10000000000000000 : ℝ) (1617677290473 / 976562500000000 : ℝ) (66923645746787 / 2000000000000000 : ℝ)
    (cell12680 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · have h := gap_lower (n := 12680) (a := (82255848221751 / 100000000000000 : ℝ)) (b := (40612075033 / 25000000000000 : ℝ)) (q := (1127071563223 / 50000000000000 : ℝ))
      (E := (cell12680 ⟨53, by decide⟩).energy) (xi := (66923645746787 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12680 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12680]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12680])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12680) (a := (82255848221751 / 100000000000000 : ℝ)) (b := (40612075033 / 25000000000000 : ℝ)) (q := (1127071563223 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12680])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12680])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12680]

theorem cert12680_54 : CellCertificate 12680 (887250128388977 / 10000000000000000 : ℝ) (1617677290473 / 976562500000000 : ℝ) (66923645746787 / 2000000000000000 : ℝ)
    (cell12680 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · have h := gap_lower (n := 12680) (a := (41111071326561 / 50000000000000 : ℝ)) (b := (40612075033 / 25000000000000 : ℝ)) (q := (140884192551 / 6250000000000 : ℝ))
      (E := (cell12680 ⟨54, by decide⟩).energy) (xi := (66923645746787 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12680 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12680]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12680])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12680) (a := (41111071326561 / 50000000000000 : ℝ)) (b := (40612075033 / 25000000000000 : ℝ)) (q := (140884192551 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12680])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12680])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12680]

theorem cert12680_55 : CellCertificate 12680 (887250128388977 / 10000000000000000 : ℝ) (1617677290473 / 976562500000000 : ℝ) (66923645746787 / 2000000000000000 : ℝ)
    (cell12680 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · have h := gap_lower (n := 12680) (a := (82188460330819 / 100000000000000 : ℝ)) (b := (40612075033 / 25000000000000 : ℝ)) (q := (2254151123179 / 100000000000000 : ℝ))
      (E := (cell12680 ⟨55, by decide⟩).energy) (xi := (66923645746787 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12680 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12680]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12680])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12680) (a := (82188460330819 / 100000000000000 : ℝ)) (b := (40612075033 / 25000000000000 : ℝ)) (q := (2254151123179 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12680])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12680])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12680]

theorem cert12680_56 : CellCertificate 12680 (887250128388977 / 10000000000000000 : ℝ) (1617677290473 / 976562500000000 : ℝ) (66923645746787 / 2000000000000000 : ℝ)
    (cell12680 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · have h := gap_lower (n := 12680) (a := (16430960245403 / 20000000000000 : ℝ)) (b := (40612075033 / 25000000000000 : ℝ)) (q := (1127077565937 / 50000000000000 : ℝ))
      (E := (cell12680 ⟨56, by decide⟩).energy) (xi := (66923645746787 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12680 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12680]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12680])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12680) (a := (16430960245403 / 20000000000000 : ℝ)) (b := (40612075033 / 25000000000000 : ℝ)) (q := (1127077565937 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12680])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12680])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12680]

theorem cert12680_57 : CellCertificate 12680 (887250128388977 / 10000000000000000 : ℝ) (1617677290473 / 976562500000000 : ℝ) (66923645746787 / 2000000000000000 : ℝ)
    (cell12680 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · have h := gap_lower (n := 12680) (a := (41060582657011 / 50000000000000 : ℝ)) (b := (40612075033 / 25000000000000 : ℝ)) (q := (1127079551567 / 50000000000000 : ℝ))
      (E := (cell12680 ⟨57, by decide⟩).energy) (xi := (66923645746787 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12680 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12680]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12680])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12680) (a := (41060582657011 / 50000000000000 : ℝ)) (b := (40612075033 / 25000000000000 : ℝ)) (q := (1127079551567 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12680])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12680])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12680]

theorem cert12680_58 : CellCertificate 12680 (887250128388977 / 10000000000000000 : ℝ) (1617677290473 / 976562500000000 : ℝ) (66923645746787 / 2000000000000000 : ℝ)
    (cell12680 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · have h := gap_lower (n := 12680) (a := (82087552564291 / 100000000000000 : ℝ)) (b := (40612075033 / 25000000000000 : ℝ)) (q := (1127081575661 / 50000000000000 : ℝ))
      (E := (cell12680 ⟨58, by decide⟩).energy) (xi := (66923645746787 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12680 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12680]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12680])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12680) (a := (82087552564291 / 100000000000000 : ℝ)) (b := (40612075033 / 25000000000000 : ℝ)) (q := (1127081575661 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12680])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12680])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12680]

theorem cert12680_59 : CellCertificate 12680 (887250128388977 / 10000000000000000 : ℝ) (1617677290473 / 976562500000000 : ℝ) (66923645746787 / 2000000000000000 : ℝ)
    (cell12680 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · have h := gap_lower (n := 12680) (a := (82053962950409 / 100000000000000 : ℝ)) (b := (40612075033 / 25000000000000 : ℝ)) (q := (2254167154013 / 100000000000000 : ℝ))
      (E := (cell12680 ⟨59, by decide⟩).energy) (xi := (66923645746787 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12680 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12680]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12680])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12680) (a := (82053962950409 / 100000000000000 : ℝ)) (b := (40612075033 / 25000000000000 : ℝ)) (q := (2254167154013 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12680])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12680])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12680]

theorem cert12681_40 : CellCertificate 12681 (887222109089807 / 10000000000000000 : ℝ) (16563708738093 / 10000000000000000 : ℝ) (83647798849141 / 2500000000000000 : ℝ)
    (cell12681 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · have h := gap_lower (n := 12681) (a := (82696146260799 / 100000000000000 : ℝ)) (b := (81217666481 / 50000000000000 : ℝ)) (q := (2253967633717 / 100000000000000 : ℝ))
      (E := (cell12681 ⟨40, by decide⟩).energy) (xi := (83647798849141 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12681 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12681]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12681])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12681) (a := (82696146260799 / 100000000000000 : ℝ)) (b := (81217666481 / 50000000000000 : ℝ)) (q := (2253967633717 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12681])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12681])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12681]

theorem cert12681_41 : CellCertificate 12681 (887222109089807 / 10000000000000000 : ℝ) (16563708738093 / 10000000000000000 : ℝ) (83647798849141 / 2500000000000000 : ℝ)
    (cell12681 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · have h := gap_lower (n := 12681) (a := (41331068098239 / 50000000000000 : ℝ)) (b := (81217666481 / 50000000000000 : ℝ)) (q := (112698581461 / 5000000000000 : ℝ))
      (E := (cell12681 ⟨41, by decide⟩).energy) (xi := (83647798849141 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12681 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12681]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12681])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12681) (a := (41331068098239 / 50000000000000 : ℝ)) (b := (81217666481 / 50000000000000 : ℝ)) (q := (112698581461 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12681])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12681])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12681]

theorem cert12681_42 : CellCertificate 12681 (887222109089807 / 10000000000000000 : ℝ) (16563708738093 / 10000000000000000 : ℝ) (83647798849141 / 2500000000000000 : ℝ)
    (cell12681 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · have h := gap_lower (n := 12681) (a := (41314074876407 / 50000000000000 : ℝ)) (b := (81217666481 / 50000000000000 : ℝ)) (q := (18031804977 / 800000000000 : ℝ))
      (E := (cell12681 ⟨42, by decide⟩).energy) (xi := (83647798849141 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12681 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12681]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12681])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12681) (a := (41314074876407 / 50000000000000 : ℝ)) (b := (81217666481 / 50000000000000 : ℝ)) (q := (18031804977 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12681])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12681])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12681]

theorem cert12681_43 : CellCertificate 12681 (887222109089807 / 10000000000000000 : ℝ) (16563708738093 / 10000000000000000 : ℝ) (83647798849141 / 2500000000000000 : ℝ)
    (cell12681 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · have h := gap_lower (n := 12681) (a := (41297093450051 / 50000000000000 : ℝ)) (b := (81217666481 / 50000000000000 : ℝ)) (q := (2253979670463 / 100000000000000 : ℝ))
      (E := (cell12681 ⟨43, by decide⟩).energy) (xi := (83647798849141 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12681 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12681]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12681])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12681) (a := (41297093450051 / 50000000000000 : ℝ)) (b := (81217666481 / 50000000000000 : ℝ)) (q := (2253979670463 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12681])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12681])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12681]

theorem cert12681_44 : CellCertificate 12681 (887222109089807 / 10000000000000000 : ℝ) (16563708738093 / 10000000000000000 : ℝ) (83647798849141 / 2500000000000000 : ℝ)
    (cell12681 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · have h := gap_lower (n := 12681) (a := (5160015475549 / 6250000000000 : ℝ)) (b := (81217666481 / 50000000000000 : ℝ)) (q := (112699182781 / 5000000000000 : ℝ))
      (E := (cell12681 ⟨44, by decide⟩).energy) (xi := (83647798849141 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12681 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12681]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12681])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12681) (a := (5160015475549 / 6250000000000 : ℝ)) (b := (81217666481 / 50000000000000 : ℝ)) (q := (112699182781 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12681])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12681])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12681]

theorem cert12681_45 : CellCertificate 12681 (887222109089807 / 10000000000000000 : ℝ) (16563708738093 / 10000000000000000 : ℝ) (83647798849141 / 2500000000000000 : ℝ)
    (cell12681 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · have h := gap_lower (n := 12681) (a := (41263165924727 / 50000000000000 : ℝ)) (b := (81217666481 / 50000000000000 : ℝ)) (q := (1126993817583 / 50000000000000 : ℝ))
      (E := (cell12681 ⟨45, by decide⟩).energy) (xi := (83647798849141 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12681 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12681]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12681])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12681) (a := (41263165924727 / 50000000000000 : ℝ)) (b := (81217666481 / 50000000000000 : ℝ)) (q := (1126993817583 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12681])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12681])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12681]

theorem cert12681_46 : CellCertificate 12681 (887222109089807 / 10000000000000000 : ℝ) (16563708738093 / 10000000000000000 : ℝ) (83647798849141 / 2500000000000000 : ℝ)
    (cell12681 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · have h := gap_lower (n := 12681) (a := (82492439592853 / 100000000000000 : ℝ)) (b := (81217666481 / 50000000000000 : ℝ)) (q := (2253991666549 / 100000000000000 : ℝ))
      (E := (cell12681 ⟨46, by decide⟩).energy) (xi := (83647798849141 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12681 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12681]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12681])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12681) (a := (82492439592853 / 100000000000000 : ℝ)) (b := (81217666481 / 50000000000000 : ℝ)) (q := (2253991666549 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12681])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12681])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12681]

theorem cert12681_47 : CellCertificate 12681 (887222109089807 / 10000000000000000 : ℝ) (16563708738093 / 10000000000000000 : ℝ) (83647798849141 / 2500000000000000 : ℝ)
    (cell12681 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · have h := gap_lower (n := 12681) (a := (82458570809869 / 100000000000000 : ℝ)) (b := (81217666481 / 50000000000000 : ℝ)) (q := (90159827571 / 4000000000000 : ℝ))
      (E := (cell12681 ⟨47, by decide⟩).energy) (xi := (83647798849141 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12681 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12681]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12681])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12681) (a := (82458570809869 / 100000000000000 : ℝ)) (b := (81217666481 / 50000000000000 : ℝ)) (q := (90159827571 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12681])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12681])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12681]

theorem cert12681_48 : CellCertificate 12681 (887222109089807 / 10000000000000000 : ℝ) (16563708738093 / 10000000000000000 : ℝ) (83647798849141 / 2500000000000000 : ℝ)
    (cell12681 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · have h := gap_lower (n := 12681) (a := (5151545341971 / 6250000000000 : ℝ)) (b := (81217666481 / 50000000000000 : ℝ)) (q := (2253999642539 / 100000000000000 : ℝ))
      (E := (cell12681 ⟨48, by decide⟩).energy) (xi := (83647798849141 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12681 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12681]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12681])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12681) (a := (5151545341971 / 6250000000000 : ℝ)) (b := (81217666481 / 50000000000000 : ℝ)) (q := (2253999642539 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12681])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12681])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12681]

theorem cert12681_49 : CellCertificate 12681 (887222109089807 / 10000000000000000 : ℝ) (16563708738093 / 10000000000000000 : ℝ) (83647798849141 / 2500000000000000 : ℝ)
    (cell12681 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · have h := gap_lower (n := 12681) (a := (41195451774517 / 50000000000000 : ℝ)) (b := (81217666481 / 50000000000000 : ℝ)) (q := (2254003701061 / 100000000000000 : ℝ))
      (E := (cell12681 ⟨49, by decide⟩).energy) (xi := (83647798849141 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12681 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12681]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12681])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12681) (a := (41195451774517 / 50000000000000 : ℝ)) (b := (81217666481 / 50000000000000 : ℝ)) (q := (2254003701061 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12681])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12681])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12681]

theorem cert12681_50 : CellCertificate 12681 (887222109089807 / 10000000000000000 : ℝ) (16563708738093 / 10000000000000000 : ℝ) (83647798849141 / 2500000000000000 : ℝ)
    (cell12681 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · have h := gap_lower (n := 12681) (a := (82357105013687 / 100000000000000 : ℝ)) (b := (81217666481 / 50000000000000 : ℝ)) (q := (2254007685741 / 100000000000000 : ℝ))
      (E := (cell12681 ⟨50, by decide⟩).energy) (xi := (83647798849141 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12681 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12681]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12681])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12681) (a := (82357105013687 / 100000000000000 : ℝ)) (b := (81217666481 / 50000000000000 : ℝ)) (q := (2254007685741 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12681])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12681])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12681]

theorem cert12681_51 : CellCertificate 12681 (887222109089807 / 10000000000000000 : ℝ) (16563708738093 / 10000000000000000 : ℝ) (83647798849141 / 2500000000000000 : ℝ)
    (cell12681 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · have h := gap_lower (n := 12681) (a := (20580832459241 / 25000000000000 : ℝ)) (b := (81217666481 / 50000000000000 : ℝ)) (q := (281751464001 / 12500000000000 : ℝ))
      (E := (cell12681 ⟨51, by decide⟩).energy) (xi := (83647798849141 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12681 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12681]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12681])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12681) (a := (20580832459241 / 25000000000000 : ℝ)) (b := (81217666481 / 50000000000000 : ℝ)) (q := (281751464001 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12681])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12681])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12681]

theorem cert12681_52 : CellCertificate 12681 (887222109089807 / 10000000000000000 : ℝ) (16563708738093 / 10000000000000000 : ℝ) (83647798849141 / 2500000000000000 : ℝ)
    (cell12681 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · have h := gap_lower (n := 12681) (a := (41144788995237 / 50000000000000 : ℝ)) (b := (81217666481 / 50000000000000 : ℝ)) (q := (450803143637 / 20000000000000 : ℝ))
      (E := (cell12681 ⟨52, by decide⟩).energy) (xi := (83647798849141 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12681 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12681]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12681])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12681) (a := (41144788995237 / 50000000000000 : ℝ)) (b := (81217666481 / 50000000000000 : ℝ)) (q := (450803143637 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12681])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12681])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12681]

theorem cert12681_53 : CellCertificate 12681 (887222109089807 / 10000000000000000 : ℝ) (16563708738093 / 10000000000000000 : ℝ) (83647798849141 / 2500000000000000 : ℝ)
    (cell12681 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · have h := gap_lower (n := 12681) (a := (20563962361493 / 25000000000000 : ℝ)) (b := (81217666481 / 50000000000000 : ℝ)) (q := (1127009850669 / 50000000000000 : ℝ))
      (E := (cell12681 ⟨53, by decide⟩).energy) (xi := (83647798849141 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12681 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12681]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12681])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12681) (a := (20563962361493 / 25000000000000 : ℝ)) (b := (81217666481 / 50000000000000 : ℝ)) (q := (1127009850669 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12681])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12681])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12681]

theorem cert12681_54 : CellCertificate 12681 (887222109089807 / 10000000000000000 : ℝ) (16563708738093 / 10000000000000000 : ℝ) (83647798849141 / 2500000000000000 : ℝ)
    (cell12681 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · have h := gap_lower (n := 12681) (a := (82222144175351 / 100000000000000 : ℝ)) (b := (81217666481 / 50000000000000 : ℝ)) (q := (2254023717401 / 100000000000000 : ℝ))
      (E := (cell12681 ⟨54, by decide⟩).energy) (xi := (83647798849141 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12681 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12681]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12681])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12681) (a := (82222144175351 / 100000000000000 : ℝ)) (b := (81217666481 / 50000000000000 : ℝ)) (q := (2254023717401 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12681])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12681])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12681]

theorem cert12681_55 : CellCertificate 12681 (887222109089807 / 10000000000000000 : ℝ) (16563708738093 / 10000000000000000 : ℝ) (83647798849141 / 2500000000000000 : ℝ)
    (cell12681 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · have h := gap_lower (n := 12681) (a := (41094231075323 / 50000000000000 : ℝ)) (b := (81217666481 / 50000000000000 : ℝ)) (q := (450805540799 / 20000000000000 : ℝ))
      (E := (cell12681 ⟨55, by decide⟩).energy) (xi := (83647798849141 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12681 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12681]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12681])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12681) (a := (41094231075323 / 50000000000000 : ℝ)) (b := (81217666481 / 50000000000000 : ℝ)) (q := (450805540799 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12681])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12681])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12681]

theorem cert12681_56 : CellCertificate 12681 (887222109089807 / 10000000000000000 : ℝ) (16563708738093 / 10000000000000000 : ℝ) (83647798849141 / 2500000000000000 : ℝ)
    (cell12681 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · have h := gap_lower (n := 12681) (a := (2567337604501 / 3125000000000 : ℝ)) (b := (81217666481 / 50000000000000 : ℝ)) (q := (56350792917 / 2500000000000 : ℝ))
      (E := (cell12681 ⟨56, by decide⟩).energy) (xi := (83647798849141 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12681 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12681]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12681])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12681) (a := (2567337604501 / 3125000000000 : ℝ)) (b := (81217666481 / 50000000000000 : ℝ)) (q := (56350792917 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12681])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12681])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12681]

theorem cert12681_57 : CellCertificate 12681 (887222109089807 / 10000000000000000 : ℝ) (16563708738093 / 10000000000000000 : ℝ) (83647798849141 / 2500000000000000 : ℝ)
    (cell12681 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · have h := gap_lower (n := 12681) (a := (82121167727821 / 100000000000000 : ℝ)) (b := (81217666481 / 50000000000000 : ℝ)) (q := (1127017846307 / 50000000000000 : ℝ))
      (E := (cell12681 ⟨57, by decide⟩).energy) (xi := (83647798849141 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12681 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12681]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12681])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12681) (a := (82121167727821 / 100000000000000 : ℝ)) (b := (81217666481 / 50000000000000 : ℝ)) (q := (1127017846307 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12681])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12681])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12681]

theorem cert12681_58 : CellCertificate 12681 (887222109089807 / 10000000000000000 : ℝ) (16563708738093 / 10000000000000000 : ℝ) (83647798849141 / 2500000000000000 : ℝ)
    (cell12681 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · have h := gap_lower (n := 12681) (a := (16417511054893 / 20000000000000 : ℝ)) (b := (81217666481 / 50000000000000 : ℝ)) (q := (28175496827 / 1250000000000 : ℝ))
      (E := (cell12681 ⟨58, by decide⟩).energy) (xi := (83647798849141 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12681 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12681]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12681])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12681) (a := (16417511054893 / 20000000000000 : ℝ)) (b := (81217666481 / 50000000000000 : ℝ)) (q := (28175496827 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12681])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12681])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12681]

theorem cert12681_59 : CellCertificate 12681 (887222109089807 / 10000000000000000 : ℝ) (16563708738093 / 10000000000000000 : ℝ) (83647798849141 / 2500000000000000 : ℝ)
    (cell12681 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · have h := gap_lower (n := 12681) (a := (82053965956551 / 100000000000000 : ℝ)) (b := (81217666481 / 50000000000000 : ℝ)) (q := (563510938723 / 25000000000000 : ℝ))
      (E := (cell12681 ⟨59, by decide⟩).energy) (xi := (83647798849141 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12681 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12681]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12681])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12681) (a := (82053965956551 / 100000000000000 : ℝ)) (b := (81217666481 / 50000000000000 : ℝ)) (q := (563510938723 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12681])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12681])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12681]

theorem cert12682_40 : CellCertificate 12682 (13862407719281 / 156250000000000 : ℝ) (1656240222788449 / 1000000000000000000 : ℝ) (66912833297803 / 2000000000000000 : ℝ)
    (cell12682 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · have h := gap_lower (n := 12682) (a := (82696143574237 / 100000000000000 : ℝ)) (b := (162422367877 / 100000000000000 : ℝ)) (q := (90153769363 / 4000000000000 : ℝ))
      (E := (cell12682 ⟨40, by decide⟩).energy) (xi := (66912833297803 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12682 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12682]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12682])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12682) (a := (82696143574237 / 100000000000000 : ℝ)) (b := (162422367877 / 100000000000000 : ℝ)) (q := (90153769363 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12682])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12682])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12682]

theorem cert12682_41 : CellCertificate 12682 (13862407719281 / 156250000000000 : ℝ) (1656240222788449 / 1000000000000000000 : ℝ) (66912833297803 / 2000000000000000 : ℝ)
    (cell12682 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · have h := gap_lower (n := 12682) (a := (10332766726659 / 12500000000000 : ℝ)) (b := (162422367877 / 100000000000000 : ℝ)) (q := (563462070507 / 25000000000000 : ℝ))
      (E := (cell12682 ⟨41, by decide⟩).energy) (xi := (66912833297803 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12682 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12682]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12682])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12682) (a := (10332766726659 / 12500000000000 : ℝ)) (b := (162422367877 / 100000000000000 : ℝ)) (q := (563462070507 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12682])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12682])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12682]

theorem cert12682_42 : CellCertificate 12682 (13862407719281 / 156250000000000 : ℝ) (1656240222788449 / 1000000000000000000 : ℝ) (66912833297803 / 2000000000000000 : ℝ)
    (cell12682 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · have h := gap_lower (n := 12682) (a := (41314073836273 / 50000000000000 : ℝ)) (b := (162422367877 / 100000000000000 : ℝ)) (q := (563463067333 / 25000000000000 : ℝ))
      (E := (cell12682 ⟨42, by decide⟩).energy) (xi := (66912833297803 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12682 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12682]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12682])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12682) (a := (41314073836273 / 50000000000000 : ℝ)) (b := (162422367877 / 100000000000000 : ℝ)) (q := (563463067333 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12682])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12682])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12682]

theorem cert12682_43 : CellCertificate 12682 (13862407719281 / 156250000000000 : ℝ) (1656240222788449 / 1000000000000000000 : ℝ) (66912833297803 / 2000000000000000 : ℝ)
    (cell12682 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · have h := gap_lower (n := 12682) (a := (5162136570147 / 6250000000000 : ℝ)) (b := (162422367877 / 100000000000000 : ℝ)) (q := (2253856253947 / 100000000000000 : ℝ))
      (E := (cell12682 ⟨43, by decide⟩).energy) (xi := (66912833297803 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12682 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12682]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12682])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12682) (a := (5162136570147 / 6250000000000 : ℝ)) (b := (162422367877 / 100000000000000 : ℝ)) (q := (2253856253947 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12682])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12682])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12682]

theorem cert12682_44 : CellCertificate 12682 (13862407719281 / 156250000000000 : ℝ) (1656240222788449 / 1000000000000000000 : ℝ) (66912833297803 / 2000000000000000 : ℝ)
    (cell12682 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · have h := gap_lower (n := 12682) (a := (82560246133137 / 100000000000000 : ℝ)) (b := (162422367877 / 100000000000000 : ℝ)) (q := (1126930146853 / 50000000000000 : ℝ))
      (E := (cell12682 ⟨44, by decide⟩).energy) (xi := (66912833297803 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12682 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12682]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12682])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12682) (a := (82560246133137 / 100000000000000 : ℝ)) (b := (162422367877 / 100000000000000 : ℝ)) (q := (1126930146853 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12682])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12682])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12682]

theorem cert12682_45 : CellCertificate 12682 (13862407719281 / 156250000000000 : ℝ) (1656240222788449 / 1000000000000000000 : ℝ) (66912833297803 / 2000000000000000 : ℝ)
    (cell12682 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · have h := gap_lower (n := 12682) (a := (20631582668873 / 25000000000000 : ℝ)) (b := (162422367877 / 100000000000000 : ℝ)) (q := (563466067433 / 25000000000000 : ℝ))
      (E := (cell12682 ⟨45, by decide⟩).energy) (xi := (66912833297803 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12682 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12682]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12682])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12682) (a := (20631582668873 / 25000000000000 : ℝ)) (b := (162422367877 / 100000000000000 : ℝ)) (q := (563466067433 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12682])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12682])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12682]

theorem cert12682_46 : CellCertificate 12682 (13862407719281 / 156250000000000 : ℝ) (1656240222788449 / 1000000000000000000 : ℝ) (66912833297803 / 2000000000000000 : ℝ)
    (cell12682 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · have h := gap_lower (n := 12682) (a := (41246219360081 / 50000000000000 : ℝ)) (b := (162422367877 / 100000000000000 : ℝ)) (q := (563467074571 / 25000000000000 : ℝ))
      (E := (cell12682 ⟨46, by decide⟩).energy) (xi := (66912833297803 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12682 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12682]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12682])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12682) (a := (41246219360081 / 50000000000000 : ℝ)) (b := (162422367877 / 100000000000000 : ℝ)) (q := (563467074571 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12682])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12682])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12682]

theorem cert12682_47 : CellCertificate 12682 (13862407719281 / 156250000000000 : ℝ) (1656240222788449 / 1000000000000000000 : ℝ) (66912833297803 / 2000000000000000 : ℝ)
    (cell12682 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · have h := gap_lower (n := 12682) (a := (82458570238033 / 100000000000000 : ℝ)) (b := (162422367877 / 100000000000000 : ℝ)) (q := (281734039859 / 12500000000000 : ℝ))
      (E := (cell12682 ⟨47, by decide⟩).energy) (xi := (66912833297803 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12682 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12682]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12682])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12682) (a := (82458570238033 / 100000000000000 : ℝ)) (b := (162422367877 / 100000000000000 : ℝ)) (q := (281734039859 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12682])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12682])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12682]

theorem cert12682_48 : CellCertificate 12682 (13862407719281 / 156250000000000 : ℝ) (1656240222788449 / 1000000000000000000 : ℝ) (66912833297803 / 2000000000000000 : ℝ)
    (cell12682 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · have h := gap_lower (n := 12682) (a := (82424725200141 / 100000000000000 : ℝ)) (b := (162422367877 / 100000000000000 : ℝ)) (q := (70433633459 / 3125000000000 : ℝ))
      (E := (cell12682 ⟨48, by decide⟩).energy) (xi := (66912833297803 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12682 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12682]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12682])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12682) (a := (82424725200141 / 100000000000000 : ℝ)) (b := (162422367877 / 100000000000000 : ℝ)) (q := (70433633459 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12682])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12682])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12682]

theorem cert12682_49 : CellCertificate 12682 (13862407719281 / 156250000000000 : ℝ) (1656240222788449 / 1000000000000000000 : ℝ) (66912833297803 / 2000000000000000 : ℝ)
    (cell12682 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · have h := gap_lower (n := 12682) (a := (82390903577667 / 100000000000000 : ℝ)) (b := (162422367877 / 100000000000000 : ℝ)) (q := (2253880328451 / 100000000000000 : ℝ))
      (E := (cell12682 ⟨49, by decide⟩).energy) (xi := (66912833297803 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12682 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12682]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12682])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12682) (a := (82390903577667 / 100000000000000 : ℝ)) (b := (162422367877 / 100000000000000 : ℝ)) (q := (2253880328451 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12682])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12682])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12682]

theorem cert12682_50 : CellCertificate 12682 (13862407719281 / 156250000000000 : ℝ) (1656240222788449 / 1000000000000000000 : ℝ) (66912833297803 / 2000000000000000 : ℝ)
    (cell12682 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · have h := gap_lower (n := 12682) (a := (16471421068387 / 20000000000000 : ℝ)) (b := (162422367877 / 100000000000000 : ℝ)) (q := (1126942156531 / 50000000000000 : ℝ))
      (E := (cell12682 ⟨50, by decide⟩).energy) (xi := (66912833297803 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12682 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12682]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12682])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12682) (a := (16471421068387 / 20000000000000 : ℝ)) (b := (162422367877 / 100000000000000 : ℝ)) (q := (1126942156531 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12682])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12682])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12682]

theorem cert12682_51 : CellCertificate 12682 (13862407719281 / 156250000000000 : ℝ) (1656240222788449 / 1000000000000000000 : ℝ) (66912833297803 / 2000000000000000 : ℝ)
    (cell12682 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · have h := gap_lower (n := 12682) (a := (16464666092883 / 20000000000000 : ℝ)) (b := (162422367877 / 100000000000000 : ℝ)) (q := (563472084987 / 25000000000000 : ℝ))
      (E := (cell12682 ⟨51, by decide⟩).energy) (xi := (66912833297803 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12682 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12682]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12682])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12682) (a := (16464666092883 / 20000000000000 : ℝ)) (b := (162422367877 / 100000000000000 : ℝ)) (q := (563472084987 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12682])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12682])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12682]

theorem cert12682_52 : CellCertificate 12682 (13862407719281 / 156250000000000 : ℝ) (1656240222788449 / 1000000000000000000 : ℝ) (66912833297803 / 2000000000000000 : ℝ)
    (cell12682 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · have h := gap_lower (n := 12682) (a := (82289578916717 / 100000000000000 : ℝ)) (b := (162422367877 / 100000000000000 : ℝ)) (q := (2253892288403 / 100000000000000 : ℝ))
      (E := (cell12682 ⟨52, by decide⟩).energy) (xi := (66912833297803 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12682 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12682]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12682])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12682) (a := (82289578916717 / 100000000000000 : ℝ)) (b := (162422367877 / 100000000000000 : ℝ)) (q := (2253892288403 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12682])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12682])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12682]

theorem cert12682_53 : CellCertificate 12682 (13862407719281 / 156250000000000 : ℝ) (1656240222788449 / 1000000000000000000 : ℝ) (66912833297803 / 2000000000000000 : ℝ)
    (cell12682 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · have h := gap_lower (n := 12682) (a := (20563962667649 / 25000000000000 : ℝ)) (b := (162422367877 / 100000000000000 : ℝ)) (q := (1126948166289 / 50000000000000 : ℝ))
      (E := (cell12682 ⟨53, by decide⟩).energy) (xi := (66912833297803 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12682 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12682]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12682])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12682) (a := (20563962667649 / 25000000000000 : ℝ)) (b := (162422367877 / 100000000000000 : ℝ)) (q := (1126948166289 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12682])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12682])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12682]

theorem cert12682_54 : CellCertificate 12682 (13862407719281 / 156250000000000 : ℝ) (1656240222788449 / 1000000000000000000 : ℝ) (66912833297803 / 2000000000000000 : ℝ)
    (cell12682 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · have h := gap_lower (n := 12682) (a := (82222145697947 / 100000000000000 : ℝ)) (b := (162422367877 / 100000000000000 : ℝ)) (q := (56347508783 / 2500000000000 : ℝ))
      (E := (cell12682 ⟨54, by decide⟩).energy) (xi := (66912833297803 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12682 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12682]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12682])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12682) (a := (82222145697947 / 100000000000000 : ℝ)) (b := (162422367877 / 100000000000000 : ℝ)) (q := (56347508783 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12682])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12682])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12682]

theorem cert12682_55 : CellCertificate 12682 (13862407719281 / 156250000000000 : ℝ) (1656240222788449 / 1000000000000000000 : ℝ) (66912833297803 / 2000000000000000 : ℝ)
    (cell12682 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · have h := gap_lower (n := 12682) (a := (20547115992701 / 25000000000000 : ℝ)) (b := (162422367877 / 100000000000000 : ℝ)) (q := (2253904341279 / 100000000000000 : ℝ))
      (E := (cell12682 ⟨55, by decide⟩).energy) (xi := (66912833297803 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12682 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12682]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12682])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12682) (a := (20547115992701 / 25000000000000 : ℝ)) (b := (162422367877 / 100000000000000 : ℝ)) (q := (2253904341279 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12682])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12682])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12682]

theorem cert12682_56 : CellCertificate 12682 (13862407719281 / 156250000000000 : ℝ) (1656240222788449 / 1000000000000000000 : ℝ) (66912833297803 / 2000000000000000 : ℝ)
    (cell12682 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · have h := gap_lower (n := 12682) (a := (2567337670667 / 3125000000000 : ℝ)) (b := (162422367877 / 100000000000000 : ℝ)) (q := (1126954179007 / 50000000000000 : ℝ))
      (E := (cell12682 ⟨56, by decide⟩).energy) (xi := (66912833297803 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12682 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12682]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12682])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12682) (a := (2567337670667 / 3125000000000 : ℝ)) (b := (162422367877 / 100000000000000 : ℝ)) (q := (1126954179007 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12682])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12682])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12682]

theorem cert12682_57 : CellCertificate 12682 (13862407719281 / 156250000000000 : ℝ) (1656240222788449 / 1000000000000000000 : ℝ) (66912833297803 / 2000000000000000 : ℝ)
    (cell12682 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · have h := gap_lower (n := 12682) (a := (82121170141879 / 100000000000000 : ℝ)) (b := (162422367877 / 100000000000000 : ℝ)) (q := (2253912338683 / 100000000000000 : ℝ))
      (E := (cell12682 ⟨57, by decide⟩).energy) (xi := (66912833297803 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12682 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12682]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12682])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12682) (a := (82121170141879 / 100000000000000 : ℝ)) (b := (162422367877 / 100000000000000 : ℝ)) (q := (2253912338683 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12682])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12682])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12682]

theorem cert12682_58 : CellCertificate 12682 (13862407719281 / 156250000000000 : ℝ) (1656240222788449 / 1000000000000000000 : ℝ) (66912833297803 / 2000000000000000 : ℝ)
    (cell12682 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · have h := gap_lower (n := 12682) (a := (41043778992431 / 50000000000000 : ℝ)) (b := (162422367877 / 100000000000000 : ℝ)) (q := (1126958169239 / 50000000000000 : ℝ))
      (E := (cell12682 ⟨58, by decide⟩).energy) (xi := (66912833297803 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12682 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12682]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12682])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12682) (a := (41043778992431 / 50000000000000 : ℝ)) (b := (162422367877 / 100000000000000 : ℝ)) (q := (1126958169239 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12682])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12682])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12682]

theorem cert12682_59 : CellCertificate 12682 (13862407719281 / 156250000000000 : ℝ) (1656240222788449 / 1000000000000000000 : ℝ) (66912833297803 / 2000000000000000 : ℝ)
    (cell12682 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · have h := gap_lower (n := 12682) (a := (82053968962881 / 100000000000000 : ℝ)) (b := (162422367877 / 100000000000000 : ℝ)) (q := (281740044161 / 12500000000000 : ℝ))
      (E := (cell12682 ⟨59, by decide⟩).energy) (xi := (66912833297803 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12682 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12682]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12682])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12682) (a := (82053968962881 / 100000000000000 : ℝ)) (b := (162422367877 / 100000000000000 : ℝ)) (q := (281740044161 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12682])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12682])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12682]

theorem cert12683_40 : CellCertificate 12683 (887166083220499 / 10000000000000000 : ℝ) (1656109592376921 / 1000000000000000000 : ℝ) (167268571005051 / 5000000000000000 : ℝ)
    (cell12683 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · have h := gap_lower (n := 12683) (a := (82696140888553 / 100000000000000 : ℝ)) (b := (162409404877 / 100000000000000 : ℝ)) (q := (450744189747 / 20000000000000 : ℝ))
      (E := (cell12683 ⟨40, by decide⟩).energy) (xi := (167268571005051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12683 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12683]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12683])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12683) (a := (82696140888553 / 100000000000000 : ℝ)) (b := (162409404877 / 100000000000000 : ℝ)) (q := (450744189747 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12683])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12683])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12683]

theorem cert12683_41 : CellCertificate 12683 (887166083220499 / 10000000000000000 : ℝ) (1656109592376921 / 1000000000000000000 : ℝ) (167268571005051 / 5000000000000000 : ℝ)
    (cell12683 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · have h := gap_lower (n := 12683) (a := (82662131430907 / 100000000000000 : ℝ)) (b := (162409404877 / 100000000000000 : ℝ)) (q := (563431232921 / 25000000000000 : ℝ))
      (E := (cell12683 ⟨41, by decide⟩).energy) (xi := (167268571005051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12683 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12683]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12683])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12683) (a := (82662131430907 / 100000000000000 : ℝ)) (b := (162409404877 / 100000000000000 : ℝ)) (q := (563431232921 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12683])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12683])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12683]

theorem cert12683_42 : CellCertificate 12683 (887166083220499 / 10000000000000000 : ℝ) (1656109592376921 / 1000000000000000000 : ℝ) (167268571005051 / 5000000000000000 : ℝ)
    (cell12683 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · have h := gap_lower (n := 12683) (a := (82628145593081 / 100000000000000 : ℝ)) (b := (162409404877 / 100000000000000 : ℝ)) (q := (90149156537 / 4000000000000 : ℝ))
      (E := (cell12683 ⟨42, by decide⟩).energy) (xi := (167268571005051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12683 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12683]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12683])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12683) (a := (82628145593081 / 100000000000000 : ℝ)) (b := (162409404877 / 100000000000000 : ℝ)) (q := (90149156537 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12683])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12683])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12683]

theorem cert12683_43 : CellCertificate 12683 (887166083220499 / 10000000000000000 : ℝ) (1656109592376921 / 1000000000000000000 : ℝ) (167268571005051 / 5000000000000000 : ℝ)
    (cell12683 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · have h := gap_lower (n := 12683) (a := (8259418334537 / 10000000000000 : ℝ)) (b := (162409404877 / 100000000000000 : ℝ)) (q := (2253732951987 / 100000000000000 : ℝ))
      (E := (cell12683 ⟨43, by decide⟩).energy) (xi := (167268571005051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12683 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12683]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12683])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12683) (a := (8259418334537 / 10000000000000 : ℝ)) (b := (162409404877 / 100000000000000 : ℝ)) (q := (2253732951987 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12683])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12683])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12683]

theorem cert12683_44 : CellCertificate 12683 (887166083220499 / 10000000000000000 : ℝ) (1656109592376921 / 1000000000000000000 : ℝ) (167268571005051 / 5000000000000000 : ℝ)
    (cell12683 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · have h := gap_lower (n := 12683) (a := (4128012232911 / 5000000000000 : ℝ)) (b := (162409404877 / 100000000000000 : ℝ)) (q := (1126868464377 / 50000000000000 : ℝ))
      (E := (cell12683 ⟨44, by decide⟩).energy) (xi := (167268571005051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12683 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12683]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12683])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12683) (a := (4128012232911 / 5000000000000 : ℝ)) (b := (162409404877 / 100000000000000 : ℝ)) (q := (1126868464377 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12683])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12683])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12683]

theorem cert12683_45 : CellCertificate 12683 (887166083220499 / 10000000000000000 : ℝ) (1656109592376921 / 1000000000000000000 : ℝ) (167268571005051 / 5000000000000000 : ℝ)
    (cell12683 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · have h := gap_lower (n := 12683) (a := (3301053180089 / 4000000000000 : ℝ)) (b := (162409404877 / 100000000000000 : ℝ)) (q := (1126870480079 / 50000000000000 : ℝ))
      (E := (cell12683 ⟨45, by decide⟩).energy) (xi := (167268571005051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12683 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12683]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12683])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12683) (a := (3301053180089 / 4000000000000 : ℝ)) (b := (162409404877 / 100000000000000 : ℝ)) (q := (1126870480079 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12683])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12683])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12683]

theorem cert12683_46 : CellCertificate 12683 (887166083220499 / 10000000000000000 : ℝ) (1656109592376921 / 1000000000000000000 : ℝ) (167268571005051 / 5000000000000000 : ℝ)
    (cell12683 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · have h := gap_lower (n := 12683) (a := (1288944341377 / 1562500000000 : ℝ)) (b := (162409404877 / 100000000000000 : ℝ)) (q := (140859057941 / 6250000000000 : ℝ))
      (E := (cell12683 ⟨46, by decide⟩).energy) (xi := (167268571005051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12683 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12683]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12683])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12683) (a := (1288944341377 / 1562500000000 : ℝ)) (b := (162409404877 / 100000000000000 : ℝ)) (q := (140859057941 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12683])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12683])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12683]

theorem cert12683_47 : CellCertificate 12683 (887166083220499 / 10000000000000000 : ℝ) (1656109592376921 / 1000000000000000000 : ℝ) (167268571005051 / 5000000000000000 : ℝ)
    (cell12683 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · have h := gap_lower (n := 12683) (a := (82458569666817 / 100000000000000 : ℝ)) (b := (162409404877 / 100000000000000 : ℝ)) (q := (2253748945543 / 100000000000000 : ℝ))
      (E := (cell12683 ⟨47, by decide⟩).energy) (xi := (167268571005051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12683 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12683]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12683])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12683) (a := (82458569666817 / 100000000000000 : ℝ)) (b := (162409404877 / 100000000000000 : ℝ)) (q := (2253748945543 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12683])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12683])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12683]

theorem cert12683_48 : CellCertificate 12683 (887166083220499 / 10000000000000000 : ℝ) (1656109592376921 / 1000000000000000000 : ℝ) (167268571005051 / 5000000000000000 : ℝ)
    (cell12683 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · have h := gap_lower (n := 12683) (a := (8242472492933 / 10000000000000 : ℝ)) (b := (162409404877 / 100000000000000 : ℝ)) (q := (1126876477441 / 50000000000000 : ℝ))
      (E := (cell12683 ⟨48, by decide⟩).energy) (xi := (167268571005051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12683 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12683]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12683])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12683) (a := (8242472492933 / 10000000000000 : ℝ)) (b := (162409404877 / 100000000000000 : ℝ)) (q := (1126876477441 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12683])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12683])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12683]

theorem cert12683_49 : CellCertificate 12683 (887166083220499 / 10000000000000000 : ℝ) (1656109592376921 / 1000000000000000000 : ℝ) (167268571005051 / 5000000000000000 : ℝ)
    (cell12683 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · have h := gap_lower (n := 12683) (a := (1287357868857 / 1562500000000 : ℝ)) (b := (162409404877 / 100000000000000 : ℝ)) (q := (2253756952989 / 100000000000000 : ℝ))
      (E := (cell12683 ⟨49, by decide⟩).energy) (xi := (167268571005051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12683 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12683]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12683])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12683) (a := (1287357868857 / 1562500000000 : ℝ)) (b := (162409404877 / 100000000000000 : ℝ)) (q := (2253756952989 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12683])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12683])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12683]

theorem cert12683_50 : CellCertificate 12683 (887166083220499 / 10000000000000000 : ℝ) (1656109592376921 / 1000000000000000000 : ℝ) (167268571005051 / 5000000000000000 : ℝ)
    (cell12683 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · have h := gap_lower (n := 12683) (a := (16471421134139 / 20000000000000 : ℝ)) (b := (162409404877 / 100000000000000 : ℝ)) (q := (563440249137 / 25000000000000 : ℝ))
      (E := (cell12683 ⟨50, by decide⟩).energy) (xi := (167268571005051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12683 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12683]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12683])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12683) (a := (16471421134139 / 20000000000000 : ℝ)) (b := (162409404877 / 100000000000000 : ℝ)) (q := (563440249137 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12683])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12683])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12683]

theorem cert12683_51 : CellCertificate 12683 (887166083220499 / 10000000000000000 : ℝ) (1656109592376921 / 1000000000000000000 : ℝ) (167268571005051 / 5000000000000000 : ℝ)
    (cell12683 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · have h := gap_lower (n := 12683) (a := (82323331092341 / 100000000000000 : ℝ)) (b := (162409404877 / 100000000000000 : ℝ)) (q := (225376496511 / 10000000000000 : ℝ))
      (E := (cell12683 ⟨51, by decide⟩).energy) (xi := (167268571005051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12683 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12683]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12683])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12683) (a := (82323331092341 / 100000000000000 : ℝ)) (b := (162409404877 / 100000000000000 : ℝ)) (q := (225376496511 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12683])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12683])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12683]

theorem cert12683_52 : CellCertificate 12683 (887166083220499 / 10000000000000000 : ℝ) (1656109592376921 / 1000000000000000000 : ℝ) (167268571005051 / 5000000000000000 : ℝ)
    (cell12683 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · have h := gap_lower (n := 12683) (a := (82289579843399 / 100000000000000 : ℝ)) (b := (162409404877 / 100000000000000 : ℝ)) (q := (140860560871 / 6250000000000 : ℝ))
      (E := (cell12683 ⟨52, by decide⟩).energy) (xi := (167268571005051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12683 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12683]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12683])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12683) (a := (82289579843399 / 100000000000000 : ℝ)) (b := (162409404877 / 100000000000000 : ℝ)) (q := (140860560871 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12683])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12683])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12683]

theorem cert12683_53 : CellCertificate 12683 (887166083220499 / 10000000000000000 : ℝ) (1656109592376921 / 1000000000000000000 : ℝ) (167268571005051 / 5000000000000000 : ℝ)
    (cell12683 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · have h := gap_lower (n := 12683) (a := (82255851895623 / 100000000000000 : ℝ)) (b := (162409404877 / 100000000000000 : ℝ)) (q := (1126886480557 / 50000000000000 : ℝ))
      (E := (cell12683 ⟨53, by decide⟩).energy) (xi := (167268571005051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12683 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12683]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12683])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12683) (a := (82255851895623 / 100000000000000 : ℝ)) (b := (162409404877 / 100000000000000 : ℝ)) (q := (1126886480557 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12683])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12683])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12683]

theorem cert12683_54 : CellCertificate 12683 (887166083220499 / 10000000000000000 : ℝ) (1656109592376921 / 1000000000000000000 : ℝ) (167268571005051 / 5000000000000000 : ℝ)
    (cell12683 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · have h := gap_lower (n := 12683) (a := (82222147220909 / 100000000000000 : ℝ)) (b := (162409404877 / 100000000000000 : ℝ)) (q := (2253776982573 / 100000000000000 : ℝ))
      (E := (cell12683 ⟨54, by decide⟩).energy) (xi := (167268571005051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12683 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12683]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12683])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12683) (a := (82222147220909 / 100000000000000 : ℝ)) (b := (162409404877 / 100000000000000 : ℝ)) (q := (2253776982573 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12683])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12683])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12683]

theorem cert12683_55 : CellCertificate 12683 (887166083220499 / 10000000000000000 : ℝ) (1656109592376921 / 1000000000000000000 : ℝ) (167268571005051 / 5000000000000000 : ℝ)
    (cell12683 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · have h := gap_lower (n := 12683) (a := (82188465791293 / 100000000000000 : ℝ)) (b := (162409404877 / 100000000000000 : ℝ)) (q := (1126890487967 / 50000000000000 : ℝ))
      (E := (cell12683 ⟨55, by decide⟩).energy) (xi := (167268571005051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12683 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12683]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12683])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12683) (a := (82188465791293 / 100000000000000 : ℝ)) (b := (162409404877 / 100000000000000 : ℝ)) (q := (1126890487967 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12683])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12683])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12683]

theorem cert12683_56 : CellCertificate 12683 (887166083220499 / 10000000000000000 : ℝ) (1656109592376921 / 1000000000000000000 : ℝ) (167268571005051 / 5000000000000000 : ℝ)
    (cell12683 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · have h := gap_lower (n := 12683) (a := (1643096151579 / 2000000000000 : ℝ)) (b := (162409404877 / 100000000000000 : ℝ)) (q := (2253784996757 / 100000000000000 : ℝ))
      (E := (cell12683 ⟨56, by decide⟩).energy) (xi := (167268571005051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12683 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12683]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12683])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12683) (a := (1643096151579 / 2000000000000 : ℝ)) (b := (162409404877 / 100000000000000 : ℝ)) (q := (2253784996757 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12683])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12683])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12683]

theorem cert12683_57 : CellCertificate 12683 (887166083220499 / 10000000000000000 : ℝ) (1656109592376921 / 1000000000000000000 : ℝ) (167268571005051 / 5000000000000000 : ℝ)
    (cell12683 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · have h := gap_lower (n := 12683) (a := (16424234511239 / 20000000000000 : ℝ)) (b := (162409404877 / 100000000000000 : ℝ)) (q := (2253788982197 / 100000000000000 : ℝ))
      (E := (cell12683 ⟨57, by decide⟩).energy) (xi := (167268571005051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12683 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12683]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12683])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12683) (a := (16424234511239 / 20000000000000 : ℝ)) (b := (162409404877 / 100000000000000 : ℝ)) (q := (2253788982197 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12683])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12683])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12683]

theorem cert12683_58 : CellCertificate 12683 (887166083220499 / 10000000000000000 : ℝ) (1656109592376921 / 1000000000000000000 : ℝ) (167268571005051 / 5000000000000000 : ℝ)
    (cell12683 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · have h := gap_lower (n := 12683) (a := (82087560695481 / 100000000000000 : ℝ)) (b := (162409404877 / 100000000000000 : ℝ)) (q := (2253792987447 / 100000000000000 : ℝ))
      (E := (cell12683 ⟨58, by decide⟩).energy) (xi := (167268571005051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12683 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12683]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12683])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12683) (a := (82087560695481 / 100000000000000 : ℝ)) (b := (162409404877 / 100000000000000 : ℝ)) (q := (2253792987447 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12683])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12683])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12683]

theorem cert12683_59 : CellCertificate 12683 (887166083220499 / 10000000000000000 : ℝ) (1656109592376921 / 1000000000000000000 : ℝ) (167268571005051 / 5000000000000000 : ℝ)
    (cell12683 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · have h := gap_lower (n := 12683) (a := (41026985984699 / 50000000000000 : ℝ)) (b := (162409404877 / 100000000000000 : ℝ)) (q := (1126898504197 / 50000000000000 : ℝ))
      (E := (cell12683 ⟨59, by decide⟩).energy) (xi := (167268571005051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12683 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12683]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12683])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12683) (a := (41026985984699 / 50000000000000 : ℝ)) (b := (162409404877 / 100000000000000 : ℝ)) (q := (1126898504197 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12683])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12683])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12683]

theorem cert12684_40 : CellCertificate 12684 (44356903832417 / 500000000000000 : ℝ) (20699737282123 / 12500000000000000 : ℝ) (334510121958641 / 10000000000000000 : ℝ)
    (cell12684 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · have h := gap_lower (n := 12684) (a := (16539227640749 / 20000000000000 : ℝ)) (b := (162396443961 / 100000000000000 : ℝ)) (q := (1126798800731 / 50000000000000 : ℝ))
      (E := (cell12684 ⟨40, by decide⟩).energy) (xi := (334510121958641 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12684 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12684]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12684])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12684) (a := (16539227640749 / 20000000000000 : ℝ)) (b := (162396443961 / 100000000000000 : ℝ)) (q := (1126798800731 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12684])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12684])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12684]

theorem cert12684_41 : CellCertificate 12684 (44356903832417 / 500000000000000 : ℝ) (20699737282123 / 12500000000000000 : ℝ) (334510121958641 / 10000000000000000 : ℝ)
    (cell12684 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · have h := gap_lower (n := 12684) (a := (41331064524691 / 50000000000000 : ℝ)) (b := (162396443961 / 100000000000000 : ℝ)) (q := (14085010231 / 625000000000 : ℝ))
      (E := (cell12684 ⟨41, by decide⟩).energy) (xi := (334510121958641 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12684 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12684]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12684])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12684) (a := (41331064524691 / 50000000000000 : ℝ)) (b := (162396443961 / 100000000000000 : ℝ)) (q := (14085010231 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12684])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12684])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12684]

theorem cert12684_42 : CellCertificate 12684 (44356903832417 / 500000000000000 : ℝ) (20699737282123 / 12500000000000000 : ℝ) (334510121958641 / 10000000000000000 : ℝ)
    (cell12684 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · have h := gap_lower (n := 12684) (a := (82628143514419 / 100000000000000 : ℝ)) (b := (162396443961 / 100000000000000 : ℝ)) (q := (2253605613199 / 100000000000000 : ℝ))
      (E := (cell12684 ⟨42, by decide⟩).energy) (xi := (334510121958641 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12684 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12684]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12684])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12684) (a := (82628143514419 / 100000000000000 : ℝ)) (b := (162396443961 / 100000000000000 : ℝ)) (q := (2253605613199 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12684])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12684])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12684]

theorem cert12684_43 : CellCertificate 12684 (44356903832417 / 500000000000000 : ℝ) (20699737282123 / 12500000000000000 : ℝ) (334510121958641 / 10000000000000000 : ℝ)
    (cell12684 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · have h := gap_lower (n := 12684) (a := (41297090784577 / 50000000000000 : ℝ)) (b := (162396443961 / 100000000000000 : ℝ)) (q := (2253609646953 / 100000000000000 : ℝ))
      (E := (cell12684 ⟨43, by decide⟩).energy) (xi := (334510121958641 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12684 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12684]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12684])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12684) (a := (41297090784577 / 50000000000000 : ℝ)) (b := (162396443961 / 100000000000000 : ℝ)) (q := (2253609646953 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12684])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12684])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12684]

theorem cert12684_44 : CellCertificate 12684 (44356903832417 / 500000000000000 : ℝ) (20699737282123 / 12500000000000000 : ℝ) (334510121958641 / 10000000000000000 : ℝ)
    (cell12684 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · have h := gap_lower (n := 12684) (a := (82560243184033 / 100000000000000 : ℝ)) (b := (162396443961 / 100000000000000 : ℝ)) (q := (563403404901 / 25000000000000 : ℝ))
      (E := (cell12684 ⟨44, by decide⟩).energy) (xi := (334510121958641 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12684 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12684]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12684])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12684) (a := (82560243184033 / 100000000000000 : ℝ)) (b := (162396443961 / 100000000000000 : ℝ)) (q := (563403404901 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12684])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12684])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12684]

theorem cert12684_45 : CellCertificate 12684 (44356903832417 / 500000000000000 : ℝ) (20699737282123 / 12500000000000000 : ℝ) (334510121958641 / 10000000000000000 : ℝ)
    (cell12684 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · have h := gap_lower (n := 12684) (a := (1650526566593 / 2000000000000 : ℝ)) (b := (162396443961 / 100000000000000 : ℝ)) (q := (1126808823793 / 50000000000000 : ℝ))
      (E := (cell12684 ⟨45, by decide⟩).energy) (xi := (334510121958641 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12684 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12684]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12684])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12684) (a := (1650526566593 / 2000000000000 : ℝ)) (b := (162396443961 / 100000000000000 : ℝ)) (q := (1126808823793 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12684])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12684])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12684]

theorem cert12684_46 : CellCertificate 12684 (44356903832417 / 500000000000000 : ℝ) (20699737282123 / 12500000000000000 : ℝ) (334510121958641 / 10000000000000000 : ℝ)
    (cell12684 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · have h := gap_lower (n := 12684) (a := (329969747907 / 400000000000 : ℝ)) (b := (162396443961 / 100000000000000 : ℝ)) (q := (28170270883 / 1250000000000 : ℝ))
      (E := (cell12684 ⟨46, by decide⟩).energy) (xi := (334510121958641 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12684 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12684]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12684])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12684) (a := (329969747907 / 400000000000 : ℝ)) (b := (162396443961 / 100000000000000 : ℝ)) (q := (28170270883 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12684])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12684])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12684]

theorem cert12684_47 : CellCertificate 12684 (44356903832417 / 500000000000000 : ℝ) (20699737282123 / 12500000000000000 : ℝ) (334510121958641 / 10000000000000000 : ℝ)
    (cell12684 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · have h := gap_lower (n := 12684) (a := (82458569096223 / 100000000000000 : ℝ)) (b := (162396443961 / 100000000000000 : ℝ)) (q := (1126812814099 / 50000000000000 : ℝ))
      (E := (cell12684 ⟨47, by decide⟩).energy) (xi := (334510121958641 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12684 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12684]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12684])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12684) (a := (82458569096223 / 100000000000000 : ℝ)) (b := (162396443961 / 100000000000000 : ℝ)) (q := (1126812814099 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12684])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12684])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12684]

theorem cert12684_48 : CellCertificate 12684 (44356903832417 / 500000000000000 : ℝ) (20699737282123 / 12500000000000000 : ℝ) (334510121958641 / 10000000000000000 : ℝ)
    (cell12684 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · have h := gap_lower (n := 12684) (a := (2575772645597 / 3125000000000 : ℝ)) (b := (162396443961 / 100000000000000 : ℝ)) (q := (2253629636187 / 100000000000000 : ℝ))
      (E := (cell12684 ⟨48, by decide⟩).energy) (xi := (334510121958641 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12684 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12684]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12684])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12684) (a := (2575772645597 / 3125000000000 : ℝ)) (b := (162396443961 / 100000000000000 : ℝ)) (q := (2253629636187 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12684])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12684])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12684]

theorem cert12684_49 : CellCertificate 12684 (44356903832417 / 500000000000000 : ℝ) (20699737282123 / 12500000000000000 : ℝ) (334510121958641 / 10000000000000000 : ℝ)
    (cell12684 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · have h := gap_lower (n := 12684) (a := (2574715738643 / 3125000000000 : ℝ)) (b := (162396443961 / 100000000000000 : ℝ)) (q := (450726726727 / 20000000000000 : ℝ))
      (E := (cell12684 ⟨49, by decide⟩).energy) (xi := (334510121958641 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12684 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12684]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12684])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12684) (a := (2574715738643 / 3125000000000 : ℝ)) (b := (162396443961 / 100000000000000 : ℝ)) (q := (450726726727 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12684])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12684])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12684]

theorem cert12684_50 : CellCertificate 12684 (44356903832417 / 500000000000000 : ℝ) (20699737282123 / 12500000000000000 : ℝ) (334510121958641 / 10000000000000000 : ℝ)
    (cell12684 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · have h := gap_lower (n := 12684) (a := (16471421199993 / 20000000000000 : ℝ)) (b := (162396443961 / 100000000000000 : ℝ)) (q := (2253637677223 / 100000000000000 : ℝ))
      (E := (cell12684 ⟨50, by decide⟩).energy) (xi := (334510121958641 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12684 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12684]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12684])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12684) (a := (16471421199993 / 20000000000000 : ℝ)) (b := (162396443961 / 100000000000000 : ℝ)) (q := (2253637677223 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12684])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12684])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12684]

theorem cert12684_51 : CellCertificate 12684 (44356903832417 / 500000000000000 : ℝ) (20699737282123 / 12500000000000000 : ℝ) (334510121958641 / 10000000000000000 : ℝ)
    (cell12684 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · have h := gap_lower (n := 12684) (a := (41161665860371 / 50000000000000 : ℝ)) (b := (162396443961 / 100000000000000 : ℝ)) (q := (2253641646501 / 100000000000000 : ℝ))
      (E := (cell12684 ⟨51, by decide⟩).energy) (xi := (334510121958641 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12684 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12684]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12684])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12684) (a := (41161665860371 / 50000000000000 : ℝ)) (b := (162396443961 / 100000000000000 : ℝ)) (q := (2253641646501 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12684])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12684])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12684]

theorem cert12684_52 : CellCertificate 12684 (44356903832417 / 500000000000000 : ℝ) (20699737282123 / 12500000000000000 : ℝ) (334510121958641 / 10000000000000000 : ℝ)
    (cell12684 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · have h := gap_lower (n := 12684) (a := (2057239519263 / 2500000000000 : ℝ)) (b := (162396443961 / 100000000000000 : ℝ)) (q := (2253645656731 / 100000000000000 : ℝ))
      (E := (cell12684 ⟨52, by decide⟩).energy) (xi := (334510121958641 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12684 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12684]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12684])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12684) (a := (2057239519263 / 2500000000000 : ℝ)) (b := (162396443961 / 100000000000000 : ℝ)) (q := (2253645656731 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12684])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12684])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12684]

theorem cert12684_53 : CellCertificate 12684 (44356903832417 / 500000000000000 : ℝ) (20699737282123 / 12500000000000000 : ℝ) (334510121958641 / 10000000000000000 : ℝ)
    (cell12684 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · have h := gap_lower (n := 12684) (a := (82255853121053 / 100000000000000 : ℝ)) (b := (162396443961 / 100000000000000 : ℝ)) (q := (45072994101 / 2000000000000 : ℝ))
      (E := (cell12684 ⟨53, by decide⟩).energy) (xi := (334510121958641 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12684 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12684]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12684])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12684) (a := (82255853121053 / 100000000000000 : ℝ)) (b := (162396443961 / 100000000000000 : ℝ)) (q := (45072994101 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12684])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12684])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12684]

theorem cert12684_54 : CellCertificate 12684 (44356903832417 / 500000000000000 : ℝ) (20699737282123 / 12500000000000000 : ℝ) (334510121958641 / 10000000000000000 : ℝ)
    (cell12684 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · have h := gap_lower (n := 12684) (a := (41111074372119 / 50000000000000 : ℝ)) (b := (162396443961 / 100000000000000 : ℝ)) (q := (563413417559 / 25000000000000 : ℝ))
      (E := (cell12684 ⟨54, by decide⟩).energy) (xi := (334510121958641 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12684 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12684]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12684])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12684) (a := (41111074372119 / 50000000000000 : ℝ)) (b := (162396443961 / 100000000000000 : ℝ)) (q := (563413417559 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12684])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12684])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12684]

theorem cert12684_55 : CellCertificate 12684 (44356903832417 / 500000000000000 : ℝ) (20699737282123 / 12500000000000000 : ℝ) (334510121958641 / 10000000000000000 : ℝ)
    (cell12684 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · have h := gap_lower (n := 12684) (a := (5136779225757 / 6250000000000 : ℝ)) (b := (162396443961 / 100000000000000 : ℝ)) (q := (2253657667059 / 100000000000000 : ℝ))
      (E := (cell12684 ⟨55, by decide⟩).energy) (xi := (334510121958641 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12684 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12684]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12684])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12684) (a := (5136779225757 / 6250000000000 : ℝ)) (b := (162396443961 / 100000000000000 : ℝ)) (q := (2253657667059 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12684])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12684])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12684]

theorem cert12684_56 : CellCertificate 12684 (44356903832417 / 500000000000000 : ℝ) (20699737282123 / 12500000000000000 : ℝ) (334510121958641 / 10000000000000000 : ℝ)
    (cell12684 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · have h := gap_lower (n := 12684) (a := (82154809696851 / 100000000000000 : ℝ)) (b := (162396443961 / 100000000000000 : ℝ)) (q := (2253661692029 / 100000000000000 : ℝ))
      (E := (cell12684 ⟨56, by decide⟩).energy) (xi := (334510121958641 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12684 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12684]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12684])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12684) (a := (82154809696851 / 100000000000000 : ℝ)) (b := (162396443961 / 100000000000000 : ℝ)) (q := (2253661692029 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12684])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12684])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12684]

theorem cert12684_57 : CellCertificate 12684 (44356903832417 / 500000000000000 : ℝ) (20699737282123 / 12500000000000000 : ℝ) (334510121958641 / 10000000000000000 : ℝ)
    (cell12684 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · have h := gap_lower (n := 12684) (a := (8212117497077 / 10000000000000 : ℝ)) (b := (162396443961 / 100000000000000 : ℝ)) (q := (1126832841151 / 50000000000000 : ℝ))
      (E := (cell12684 ⟨57, by decide⟩).energy) (xi := (334510121958641 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12684 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12684]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12684])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12684) (a := (8212117497077 / 10000000000000 : ℝ)) (b := (162396443961 / 100000000000000 : ℝ)) (q := (1126832841151 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12684])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12684])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12684]

theorem cert12684_58 : CellCertificate 12684 (44356903832417 / 500000000000000 : ℝ) (20699737282123 / 12500000000000000 : ℝ) (334510121958641 / 10000000000000000 : ℝ)
    (cell12684 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · have h := gap_lower (n := 12684) (a := (20521890851581 / 25000000000000 : ℝ)) (b := (162396443961 / 100000000000000 : ℝ)) (q := (1126834846533 / 50000000000000 : ℝ))
      (E := (cell12684 ⟨58, by decide⟩).energy) (xi := (334510121958641 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12684 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12684]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12684])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12684) (a := (20521890851581 / 25000000000000 : ℝ)) (b := (162396443961 / 100000000000000 : ℝ)) (q := (1126834846533 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12684])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12684])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12684]

theorem cert12684_59 : CellCertificate 12684 (44356903832417 / 500000000000000 : ℝ) (20699737282123 / 12500000000000000 : ℝ) (334510121958641 / 10000000000000000 : ℝ)
    (cell12684 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · have h := gap_lower (n := 12684) (a := (82053974976101 / 100000000000000 : ℝ)) (b := (162396443961 / 100000000000000 : ℝ)) (q := (563418430053 / 25000000000000 : ℝ))
      (E := (cell12684 ⟨59, by decide⟩).energy) (xi := (334510121958641 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12684 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12684]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12684])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12684) (a := (82053974976101 / 100000000000000 : ℝ)) (b := (162396443961 / 100000000000000 : ℝ)) (q := (563418430053 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12684])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12684])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12684]

theorem cert12685_40 : CellCertificate 12685 (887110074316499 / 10000000000000000 : ℝ) (413962098340583 / 250000000000000000 : ℝ) (41810388291681 / 1250000000000000 : ℝ)
    (cell12685 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · have h := gap_lower (n := 12685) (a := (41348067759907 / 50000000000000 : ℝ)) (b := (20297935641 / 12500000000000 : ℝ)) (q := (450694873699 / 20000000000000 : ℝ))
      (E := (cell12685 ⟨40, by decide⟩).energy) (xi := (41810388291681 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12685 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12685]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12685])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12685) (a := (41348067759907 / 50000000000000 : ℝ)) (b := (20297935641 / 12500000000000 : ℝ)) (q := (450694873699 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12685])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12685])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12685]

theorem cert12685_41 : CellCertificate 12685 (887110074316499 / 10000000000000000 : ℝ) (413962098340583 / 250000000000000000 : ℝ) (41810388291681 / 1250000000000000 : ℝ)
    (cell12685 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · have h := gap_lower (n := 12685) (a := (10332765833587 / 12500000000000 : ℝ)) (b := (20297935641 / 12500000000000 : ℝ)) (q := (2253478339087 / 100000000000000 : ℝ))
      (E := (cell12685 ⟨41, by decide⟩).energy) (xi := (41810388291681 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12685 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12685]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12685])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12685) (a := (10332765833587 / 12500000000000 : ℝ)) (b := (20297935641 / 12500000000000 : ℝ)) (q := (2253478339087 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12685])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12685])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12685]

theorem cert12685_42 : CellCertificate 12685 (887110074316499 / 10000000000000000 : ℝ) (413962098340583 / 250000000000000000 : ℝ) (41810388291681 / 1250000000000000 : ℝ)
    (cell12685 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · have h := gap_lower (n := 12685) (a := (1032851767957 / 1250000000000 : ℝ)) (b := (20297935641 / 12500000000000 : ℝ)) (q := (450696473731 / 20000000000000 : ℝ))
      (E := (cell12685 ⟨42, by decide⟩).energy) (xi := (41810388291681 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12685 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12685]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12685])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12685) (a := (1032851767957 / 1250000000000 : ℝ)) (b := (20297935641 / 12500000000000 : ℝ)) (q := (450696473731 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12685])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12685])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12685]

theorem cert12685_43 : CellCertificate 12685 (887110074316499 / 10000000000000000 : ℝ) (413962098340583 / 250000000000000000 : ℝ) (41810388291681 / 1250000000000000 : ℝ)
    (cell12685 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · have h := gap_lower (n := 12685) (a := (16518835958741 / 20000000000000 : ℝ)) (b := (20297935641 / 12500000000000 : ℝ)) (q := (2253486397661 / 100000000000000 : ℝ))
      (E := (cell12685 ⟨43, by decide⟩).energy) (xi := (41810388291681 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12685 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12685]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12685])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12685) (a := (16518835958741 / 20000000000000 : ℝ)) (b := (20297935641 / 12500000000000 : ℝ)) (q := (2253486397661 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12685])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12685])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12685]

theorem cert12685_44 : CellCertificate 12685 (887110074316499 / 10000000000000000 : ℝ) (413962098340583 / 250000000000000000 : ℝ) (41810388291681 / 1250000000000000 : ℝ)
    (cell12685 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · have h := gap_lower (n := 12685) (a := (5160015106911 / 6250000000000 : ℝ)) (b := (20297935641 / 12500000000000 : ℝ)) (q := (1126745183129 / 50000000000000 : ℝ))
      (E := (cell12685 ⟨44, by decide⟩).energy) (xi := (41810388291681 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12685 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12685]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12685])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12685) (a := (5160015106911 / 6250000000000 : ℝ)) (b := (20297935641 / 12500000000000 : ℝ)) (q := (1126745183129 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12685])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12685])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12685]

theorem cert12685_45 : CellCertificate 12685 (887110074316499 / 10000000000000000 : ℝ) (413962098340583 / 250000000000000000 : ℝ) (41810388291681 / 1250000000000000 : ℝ)
    (cell12685 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · have h := gap_lower (n := 12685) (a := (82526327157769 / 100000000000000 : ℝ)) (b := (20297935641 / 12500000000000 : ℝ)) (q := (1126747195439 / 50000000000000 : ℝ))
      (E := (cell12685 ⟨45, by decide⟩).energy) (xi := (41810388291681 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12685 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12685]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12685])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12685) (a := (82526327157769 / 100000000000000 : ℝ)) (b := (20297935641 / 12500000000000 : ℝ)) (q := (1126747195439 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12685])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12685])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12685]

theorem cert12685_46 : CellCertificate 12685 (887110074316499 / 10000000000000000 : ℝ) (413962098340583 / 250000000000000000 : ℝ) (41810388291681 / 1250000000000000 : ℝ)
    (cell12685 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · have h := gap_lower (n := 12685) (a := (8249243610603 / 10000000000000 : ℝ)) (b := (20297935641 / 12500000000000 : ℝ)) (q := (1126749176187 / 50000000000000 : ℝ))
      (E := (cell12685 ⟨46, by decide⟩).energy) (xi := (41810388291681 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12685 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12685]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12685])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12685) (a := (8249243610603 / 10000000000000 : ℝ)) (b := (20297935641 / 12500000000000 : ℝ)) (q := (1126749176187 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12685])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12685])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12685]

theorem cert12685_47 : CellCertificate 12685 (887110074316499 / 10000000000000000 : ℝ) (413962098340583 / 250000000000000000 : ℝ) (41810388291681 / 1250000000000000 : ℝ)
    (cell12685 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · have h := gap_lower (n := 12685) (a := (10307321065781 / 12500000000000 : ℝ)) (b := (20297935641 / 12500000000000 : ℝ)) (q := (56337559171 / 2500000000000 : ℝ))
      (E := (cell12685 ⟨47, by decide⟩).energy) (xi := (41810388291681 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12685 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12685]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12685])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12685) (a := (10307321065781 / 12500000000000 : ℝ)) (b := (20297935641 / 12500000000000 : ℝ)) (q := (56337559171 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12685])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12685])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12685]

theorem cert12685_48 : CellCertificate 12685 (887110074316499 / 10000000000000000 : ℝ) (413962098340583 / 250000000000000000 : ℝ) (41810388291681 / 1250000000000000 : ℝ)
    (cell12685 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · have h := gap_lower (n := 12685) (a := (82424724389461 / 100000000000000 : ℝ)) (b := (20297935641 / 12500000000000 : ℝ)) (q := (2253506373541 / 100000000000000 : ℝ))
      (E := (cell12685 ⟨48, by decide⟩).energy) (xi := (41810388291681 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12685 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12685]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12685])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12685) (a := (82424724389461 / 100000000000000 : ℝ)) (b := (20297935641 / 12500000000000 : ℝ)) (q := (2253506373541 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12685])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12685])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12685]

theorem cert12685_49 : CellCertificate 12685 (887110074316499 / 10000000000000000 : ℝ) (413962098340583 / 250000000000000000 : ℝ) (41810388291681 / 1250000000000000 : ℝ)
    (cell12685 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · have h := gap_lower (n := 12685) (a := (20597725916713 / 25000000000000 : ℝ)) (b := (20297935641 / 12500000000000 : ℝ)) (q := (563377592597 / 25000000000000 : ℝ))
      (E := (cell12685 ⟨49, by decide⟩).energy) (xi := (41810388291681 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12685 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12685]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12685])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12685) (a := (20597725916713 / 25000000000000 : ℝ)) (b := (20297935641 / 12500000000000 : ℝ)) (q := (563377592597 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12685])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12685])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12685]

theorem cert12685_50 : CellCertificate 12685 (887110074316499 / 10000000000000000 : ℝ) (413962098340583 / 250000000000000000 : ℝ) (41810388291681 / 1250000000000000 : ℝ)
    (cell12685 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · have h := gap_lower (n := 12685) (a := (82357106329747 / 100000000000000 : ℝ)) (b := (20297935641 / 12500000000000 : ℝ)) (q := (450702882813 / 20000000000000 : ℝ))
      (E := (cell12685 ⟨50, by decide⟩).energy) (xi := (41810388291681 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12685 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12685]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12685])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12685) (a := (82357106329747 / 100000000000000 : ℝ)) (b := (20297935641 / 12500000000000 : ℝ)) (q := (450702882813 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12685])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12685])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12685]

theorem cert12685_51 : CellCertificate 12685 (887110074316499 / 10000000000000000 : ℝ) (413962098340583 / 250000000000000000 : ℝ) (41810388291681 / 1250000000000000 : ℝ)
    (cell12685 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · have h := gap_lower (n := 12685) (a := (41161666174809 / 50000000000000 : ℝ)) (b := (20297935641 / 12500000000000 : ℝ)) (q := (2253518384121 / 100000000000000 : ℝ))
      (E := (cell12685 ⟨51, by decide⟩).energy) (xi := (41810388291681 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12685 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12685]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12685])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12685) (a := (41161666174809 / 50000000000000 : ℝ)) (b := (20297935641 / 12500000000000 : ℝ)) (q := (2253518384121 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12685])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12685])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12685]

theorem cert12685_52 : CellCertificate 12685 (887110074316499 / 10000000000000000 : ℝ) (413962098340583 / 250000000000000000 : ℝ) (41810388291681 / 1250000000000000 : ℝ)
    (cell12685 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · have h := gap_lower (n := 12685) (a := (82289581698079 / 100000000000000 : ℝ)) (b := (20297935641 / 12500000000000 : ℝ)) (q := (450704479163 / 20000000000000 : ℝ))
      (E := (cell12685 ⟨52, by decide⟩).energy) (xi := (41810388291681 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12685 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12685]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12685])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12685) (a := (82289581698079 / 100000000000000 : ℝ)) (b := (20297935641 / 12500000000000 : ℝ)) (q := (450704479163 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12685])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12685])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12685]

theorem cert12685_53 : CellCertificate 12685 (887110074316499 / 10000000000000000 : ℝ) (413962098340583 / 250000000000000000 : ℝ) (41810388291681 / 1250000000000000 : ℝ)
    (cell12685 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · have h := gap_lower (n := 12685) (a := (16451170869377 / 20000000000000 : ℝ)) (b := (20297935641 / 12500000000000 : ℝ)) (q := (450705277447 / 20000000000000 : ℝ))
      (E := (cell12685 ⟨53, by decide⟩).energy) (xi := (41810388291681 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12685 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12685]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12685])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12685) (a := (16451170869377 / 20000000000000 : ℝ)) (b := (20297935641 / 12500000000000 : ℝ)) (q := (450705277447 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12685])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12685])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12685]

theorem cert12685_54 : CellCertificate 12685 (887110074316499 / 10000000000000000 : ℝ) (413962098340583 / 250000000000000000 : ℝ) (41810388291681 / 1250000000000000 : ℝ)
    (cell12685 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · have h := gap_lower (n := 12685) (a := (82222150267933 / 100000000000000 : ℝ)) (b := (20297935641 / 12500000000000 : ℝ)) (q := (2253530414309 / 100000000000000 : ℝ))
      (E := (cell12685 ⟨54, by decide⟩).energy) (xi := (41810388291681 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12685 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12685]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12685])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12685) (a := (82222150267933 / 100000000000000 : ℝ)) (b := (20297935641 / 12500000000000 : ℝ)) (q := (2253530414309 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12685])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12685])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12685]

theorem cert12685_55 : CellCertificate 12685 (887110074316499 / 10000000000000000 : ℝ) (413962098340583 / 250000000000000000 : ℝ) (41810388291681 / 1250000000000000 : ℝ)
    (cell12685 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · have h := gap_lower (n := 12685) (a := (82188469433261 / 100000000000000 : ℝ)) (b := (20297935641 / 12500000000000 : ℝ)) (q := (35211475229 / 1562500000000 : ℝ))
      (E := (cell12685 ⟨55, by decide⟩).energy) (xi := (41810388291681 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12685 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12685]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12685])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12685) (a := (82188469433261 / 100000000000000 : ℝ)) (b := (20297935641 / 12500000000000 : ℝ)) (q := (35211475229 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12685])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12685])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12685]

theorem cert12685_56 : CellCertificate 12685 (887110074316499 / 10000000000000000 : ℝ) (413962098340583 / 250000000000000000 : ℝ) (41810388291681 / 1250000000000000 : ℝ)
    (cell12685 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · have h := gap_lower (n := 12685) (a := (41077405907523 / 50000000000000 : ℝ)) (b := (20297935641 / 12500000000000 : ℝ)) (q := (1126769221917 / 50000000000000 : ℝ))
      (E := (cell12685 ⟨56, by decide⟩).energy) (xi := (41810388291681 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12685 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12685]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12685])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12685) (a := (41077405907523 / 50000000000000 : ℝ)) (b := (20297935641 / 12500000000000 : ℝ)) (q := (1126769221917 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12685])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12685])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12685]

theorem cert12685_57 : CellCertificate 12685 (887110074316499 / 10000000000000000 : ℝ) (413962098340583 / 250000000000000000 : ℝ) (41810388291681 / 1250000000000000 : ℝ)
    (cell12685 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · have h := gap_lower (n := 12685) (a := (20530294346401 / 25000000000000 : ℝ)) (b := (20297935641 / 12500000000000 : ℝ)) (q := (1126771219499 / 50000000000000 : ℝ))
      (E := (cell12685 ⟨57, by decide⟩).energy) (xi := (41810388291681 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12685 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12685]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12685])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12685) (a := (20530294346401 / 25000000000000 : ℝ)) (b := (20297935641 / 12500000000000 : ℝ)) (q := (1126771219499 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12685])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12685])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12685]

theorem cert12685_58 : CellCertificate 12685 (887110074316499 / 10000000000000000 : ℝ) (413962098340583 / 250000000000000000 : ℝ) (41810388291681 / 1250000000000000 : ℝ)
    (cell12685 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · have h := gap_lower (n := 12685) (a := (20521891529347 / 25000000000000 : ℝ)) (b := (20297935641 / 12500000000000 : ℝ)) (q := (2253546455339 / 100000000000000 : ℝ))
      (E := (cell12685 ⟨58, by decide⟩).energy) (xi := (41810388291681 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12685 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12685]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12685])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12685) (a := (20521891529347 / 25000000000000 : ℝ)) (b := (20297935641 / 12500000000000 : ℝ)) (q := (2253546455339 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12685])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12685])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12685]

theorem cert12685_59 : CellCertificate 12685 (887110074316499 / 10000000000000000 : ℝ) (413962098340583 / 250000000000000000 : ℝ) (41810388291681 / 1250000000000000 : ℝ)
    (cell12685 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · have h := gap_lower (n := 12685) (a := (82053977982991 / 100000000000000 : ℝ)) (b := (20297935641 / 12500000000000 : ℝ)) (q := (45071008591 / 2000000000000 : ℝ))
      (E := (cell12685 ⟨59, by decide⟩).energy) (xi := (41810388291681 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12685 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12685]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12685])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12685) (a := (82053977982991 / 100000000000000 : ℝ)) (b := (20297935641 / 12500000000000 : ℝ)) (q := (45071008591 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12685])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12685])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12685]

theorem cert12686_40 : CellCertificate 12686 (887082076223967 / 10000000000000000 : ℝ) (1655717824749523 / 1000000000000000000 : ℝ) (16722804756667 / 500000000000000 : ℝ)
    (cell12686 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · have h := gap_lower (n := 12686) (a := (2067403320919 / 2500000000000 : ℝ)) (b := (162370528379 / 100000000000000 : ℝ)) (q := (2253351132339 / 100000000000000 : ℝ))
      (E := (cell12686 ⟨40, by decide⟩).energy) (xi := (16722804756667 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12686 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12686]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12686])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12686) (a := (2067403320919 / 2500000000000 : ℝ)) (b := (162370528379 / 100000000000000 : ℝ)) (q := (2253351132339 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12686])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12686])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12686]

theorem cert12686_41 : CellCertificate 12686 (887082076223967 / 10000000000000000 : ℝ) (1655717824749523 / 1000000000000000000 : ℝ) (16722804756667 / 500000000000000 : ℝ)
    (cell12686 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · have h := gap_lower (n := 12686) (a := (1653242485777 / 2000000000000 : ℝ)) (b := (162370528379 / 100000000000000 : ℝ)) (q := (563338788901 / 25000000000000 : ℝ))
      (E := (cell12686 ⟨41, by decide⟩).energy) (xi := (16722804756667 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12686 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12686]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12686])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12686) (a := (1653242485777 / 2000000000000 : ℝ)) (b := (162370528379 / 100000000000000 : ℝ)) (q := (563338788901 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12686])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12686])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12686]

theorem cert12686_42 : CellCertificate 12686 (887082076223967 / 10000000000000000 : ℝ) (1655717824749523 / 1000000000000000000 : ℝ) (16722804756667 / 500000000000000 : ℝ)
    (cell12686 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · have h := gap_lower (n := 12686) (a := (16525627871901 / 20000000000000 : ℝ)) (b := (162370528379 / 100000000000000 : ℝ)) (q := (1126679560499 / 50000000000000 : ℝ))
      (E := (cell12686 ⟨42, by decide⟩).energy) (xi := (16722804756667 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12686 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12686]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12686])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12686) (a := (16525627871901 / 20000000000000 : ℝ)) (b := (162370528379 / 100000000000000 : ℝ)) (q := (1126679560499 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12686])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12686])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12686]

theorem cert12686_43 : CellCertificate 12686 (887082076223967 / 10000000000000000 : ℝ) (1655717824749523 / 1000000000000000000 : ℝ) (16722804756667 / 500000000000000 : ℝ)
    (cell12686 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · have h := gap_lower (n := 12686) (a := (41297089009511 / 50000000000000 : ℝ)) (b := (162370528379 / 100000000000000 : ℝ)) (q := (450672629059 / 20000000000000 : ℝ))
      (E := (cell12686 ⟨43, by decide⟩).energy) (xi := (16722804756667 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12686 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12686]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12686])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12686) (a := (41297089009511 / 50000000000000 : ℝ)) (b := (162370528379 / 100000000000000 : ℝ)) (q := (450672629059 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12686])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12686])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12686]

theorem cert12686_44 : CellCertificate 12686 (887082076223967 / 10000000000000000 : ℝ) (1655717824749523 / 1000000000000000000 : ℝ) (16722804756667 / 500000000000000 : ℝ)
    (cell12686 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · have h := gap_lower (n := 12686) (a := (10320030029731 / 12500000000000 : ℝ)) (b := (162370528379 / 100000000000000 : ℝ)) (q := (563341792179 / 25000000000000 : ℝ))
      (E := (cell12686 ⟨44, by decide⟩).energy) (xi := (16722804756667 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12686 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12686]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12686])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12686) (a := (10320030029731 / 12500000000000 : ℝ)) (b := (162370528379 / 100000000000000 : ℝ)) (q := (563341792179 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12686])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12686])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12686]

theorem cert12686_45 : CellCertificate 12686 (887082076223967 / 10000000000000000 : ℝ) (1655717824749523 / 1000000000000000000 : ℝ) (16722804756667 / 500000000000000 : ℝ)
    (cell12686 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · have h := gap_lower (n := 12686) (a := (82526325986581 / 100000000000000 : ℝ)) (b := (162370528379 / 100000000000000 : ℝ)) (q := (2253371131171 / 100000000000000 : ℝ))
      (E := (cell12686 ⟨45, by decide⟩).energy) (xi := (16722804756667 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12686 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12686]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12686])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12686) (a := (82526325986581 / 100000000000000 : ℝ)) (b := (162370528379 / 100000000000000 : ℝ)) (q := (2253371131171 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12686])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12686])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12686]

theorem cert12686_46 : CellCertificate 12686 (887082076223967 / 10000000000000000 : ℝ) (1655717824749523 / 1000000000000000000 : ℝ) (16722804756667 / 500000000000000 : ℝ)
    (cell12686 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · have h := gap_lower (n := 12686) (a := (41246217617983 / 50000000000000 : ℝ)) (b := (162370528379 / 100000000000000 : ℝ)) (q := (2253375148921 / 100000000000000 : ℝ))
      (E := (cell12686 ⟨46, by decide⟩).energy) (xi := (16722804756667 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12686 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12686]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12686])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12686) (a := (41246217617983 / 50000000000000 : ℝ)) (b := (162370528379 / 100000000000000 : ℝ)) (q := (2253375148921 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12686])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12686])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12686]

theorem cert12686_47 : CellCertificate 12686 (887082076223967 / 10000000000000000 : ℝ) (1655717824749523 / 1000000000000000000 : ℝ) (16722804756667 / 500000000000000 : ℝ)
    (cell12686 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · have h := gap_lower (n := 12686) (a := (82458567956893 / 100000000000000 : ℝ)) (b := (162370528379 / 100000000000000 : ℝ)) (q := (2253379161469 / 100000000000000 : ℝ))
      (E := (cell12686 ⟨47, by decide⟩).energy) (xi := (16722804756667 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12686 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12686]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12686])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12686) (a := (82458567956893 / 100000000000000 : ℝ)) (b := (162370528379 / 100000000000000 : ℝ)) (q := (2253379161469 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12686])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12686])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12686]

theorem cert12686_48 : CellCertificate 12686 (887082076223967 / 10000000000000000 : ℝ) (1655717824749523 / 1000000000000000000 : ℝ) (16722804756667 / 500000000000000 : ℝ)
    (cell12686 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · have h := gap_lower (n := 12686) (a := (41212362060201 / 50000000000000 : ℝ)) (b := (162370528379 / 100000000000000 : ℝ)) (q := (112669158347 / 5000000000000 : ℝ))
      (E := (cell12686 ⟨48, by decide⟩).energy) (xi := (16722804756667 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12686 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12686]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12686])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12686) (a := (41212362060201 / 50000000000000 : ℝ)) (b := (162370528379 / 100000000000000 : ℝ)) (q := (112669158347 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12686])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12686])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12686]

theorem cert12686_49 : CellCertificate 12686 (887082076223967 / 10000000000000000 : ℝ) (1655717824749523 / 1000000000000000000 : ℝ) (16722804756667 / 500000000000000 : ℝ)
    (cell12686 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · have h := gap_lower (n := 12686) (a := (3295636147907 / 4000000000000 : ℝ)) (b := (162370528379 / 100000000000000 : ℝ)) (q := (2253387163249 / 100000000000000 : ℝ))
      (E := (cell12686 ⟨49, by decide⟩).energy) (xi := (16722804756667 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12686 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12686]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12686])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12686) (a := (3295636147907 / 4000000000000 : ℝ)) (b := (162370528379 / 100000000000000 : ℝ)) (q := (2253387163249 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12686])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12686])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12686]

theorem cert12686_50 : CellCertificate 12686 (887082076223967 / 10000000000000000 : ℝ) (1655717824749523 / 1000000000000000000 : ℝ) (16722804756667 / 500000000000000 : ℝ)
    (cell12686 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · have h := gap_lower (n := 12686) (a := (2058927666501 / 2500000000000 : ℝ)) (b := (162370528379 / 100000000000000 : ℝ)) (q := (450678229619 / 20000000000000 : ℝ))
      (E := (cell12686 ⟨50, by decide⟩).energy) (xi := (16722804756667 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12686 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12686]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12686])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12686) (a := (2058927666501 / 2500000000000 : ℝ)) (b := (162370528379 / 100000000000000 : ℝ)) (q := (450678229619 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12686])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12686])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12686]

theorem cert12686_51 : CellCertificate 12686 (887082076223967 / 10000000000000000 : ℝ) (1655717824749523 / 1000000000000000000 : ℝ) (16722804756667 / 500000000000000 : ℝ)
    (cell12686 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · have h := gap_lower (n := 12686) (a := (82323332978969 / 100000000000000 : ℝ)) (b := (162370528379 / 100000000000000 : ℝ)) (q := (2253395177969 / 100000000000000 : ℝ))
      (E := (cell12686 ⟨51, by decide⟩).energy) (xi := (16722804756667 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12686 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12686]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12686])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12686) (a := (82323332978969 / 100000000000000 : ℝ)) (b := (162370528379 / 100000000000000 : ℝ)) (q := (2253395177969 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12686])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12686])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12686]

theorem cert12686_52 : CellCertificate 12686 (887082076223967 / 10000000000000000 : ℝ) (1655717824749523 / 1000000000000000000 : ℝ) (16722804756667 / 500000000000000 : ℝ)
    (cell12686 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · have h := gap_lower (n := 12686) (a := (82289582626077 / 100000000000000 : ℝ)) (b := (162370528379 / 100000000000000 : ℝ)) (q := (2253399191189 / 100000000000000 : ℝ))
      (E := (cell12686 ⟨52, by decide⟩).energy) (xi := (16722804756667 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12686 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12686]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12686])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12686) (a := (82289582626077 / 100000000000000 : ℝ)) (b := (162370528379 / 100000000000000 : ℝ)) (q := (2253399191189 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12686])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12686])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12686]

theorem cert12686_53 : CellCertificate 12686 (887082076223967 / 10000000000000000 : ℝ) (1655717824749523 / 1000000000000000000 : ℝ) (16722804756667 / 500000000000000 : ℝ)
    (cell12686 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · have h := gap_lower (n := 12686) (a := (82255855573119 / 100000000000000 : ℝ)) (b := (162370528379 / 100000000000000 : ℝ)) (q := (2253403184821 / 100000000000000 : ℝ))
      (E := (cell12686 ⟨53, by decide⟩).energy) (xi := (16722804756667 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12686 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12686]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12686])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12686) (a := (82255855573119 / 100000000000000 : ℝ)) (b := (162370528379 / 100000000000000 : ℝ)) (q := (2253403184821 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12686])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12686])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12686]

theorem cert12686_54 : CellCertificate 12686 (887082076223967 / 10000000000000000 : ℝ) (1655717824749523 / 1000000000000000000 : ℝ) (16722804756667 / 500000000000000 : ℝ)
    (cell12686 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · have h := gap_lower (n := 12686) (a := (16444430358399 / 20000000000000 : ℝ)) (b := (162370528379 / 100000000000000 : ℝ)) (q := (2253407214793 / 100000000000000 : ℝ))
      (E := (cell12686 ⟨54, by decide⟩).energy) (xi := (16722804756667 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12686 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12686]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12686])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12686) (a := (16444430358399 / 20000000000000 : ℝ)) (b := (162370528379 / 100000000000000 : ℝ)) (q := (2253407214793 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12686])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12686])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12686]

theorem cert12686_55 : CellCertificate 12686 (887082076223967 / 10000000000000000 : ℝ) (1655717824749523 / 1000000000000000000 : ℝ) (16722804756667 / 500000000000000 : ℝ)
    (cell12686 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · have h := gap_lower (n := 12686) (a := (82188471254741 / 100000000000000 : ℝ)) (b := (162370528379 / 100000000000000 : ℝ)) (q := (2253411218723 / 100000000000000 : ℝ))
      (E := (cell12686 ⟨55, by decide⟩).energy) (xi := (16722804756667 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12686 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12686]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12686])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12686) (a := (82188471254741 / 100000000000000 : ℝ)) (b := (162370528379 / 100000000000000 : ℝ)) (q := (2253411218723 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12686])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12686])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12686]

theorem cert12686_56 : CellCertificate 12686 (887082076223967 / 10000000000000000 : ℝ) (1655717824749523 / 1000000000000000000 : ℝ) (16722804756667 / 500000000000000 : ℝ)
    (cell12686 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · have h := gap_lower (n := 12686) (a := (16430962786707 / 20000000000000 : ℝ)) (b := (162370528379 / 100000000000000 : ℝ)) (q := (281676899131 / 12500000000000 : ℝ))
      (E := (cell12686 ⟨56, by decide⟩).energy) (xi := (16722804756667 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12686 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12686]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12686])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12686) (a := (16430962786707 / 20000000000000 : ℝ)) (b := (162370528379 / 100000000000000 : ℝ)) (q := (281676899131 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12686])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12686])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12686]

theorem cert12686_57 : CellCertificate 12686 (887082076223967 / 10000000000000000 : ℝ) (1655717824749523 / 1000000000000000000 : ℝ) (16722804756667 / 500000000000000 : ℝ)
    (cell12686 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · have h := gap_lower (n := 12686) (a := (10265147475087 / 12500000000000 : ℝ)) (b := (162370528379 / 100000000000000 : ℝ)) (q := (112670959657 / 5000000000000 : ℝ))
      (E := (cell12686 ⟨57, by decide⟩).energy) (xi := (16722804756667 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12686 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12686]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12686])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12686) (a := (10265147475087 / 12500000000000 : ℝ)) (b := (162370528379 / 100000000000000 : ℝ)) (q := (112670959657 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12686])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12686])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12686]

theorem cert12686_58 : CellCertificate 12686 (887082076223967 / 10000000000000000 : ℝ) (1655717824749523 / 1000000000000000000 : ℝ) (16722804756667 / 500000000000000 : ℝ)
    (cell12686 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · have h := gap_lower (n := 12686) (a := (20521892207169 / 25000000000000 : ℝ)) (b := (162370528379 / 100000000000000 : ℝ)) (q := (2253423215093 / 100000000000000 : ℝ))
      (E := (cell12686 ⟨58, by decide⟩).energy) (xi := (16722804756667 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12686 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12686]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12686])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12686) (a := (20521892207169 / 25000000000000 : ℝ)) (b := (162370528379 / 100000000000000 : ℝ)) (q := (2253423215093 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12686])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12686])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12686]

theorem cert12686_59 : CellCertificate 12686 (887082076223967 / 10000000000000000 : ℝ) (1655717824749523 / 1000000000000000000 : ℝ) (16722804756667 / 500000000000000 : ℝ)
    (cell12686 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · have h := gap_lower (n := 12686) (a := (82053980990067 / 100000000000000 : ℝ)) (b := (162370528379 / 100000000000000 : ℝ)) (q := (5633567989 / 250000000000 : ℝ))
      (E := (cell12686 ⟨59, by decide⟩).energy) (xi := (16722804756667 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12686 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12686]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12686])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12686) (a := (82053980990067 / 100000000000000 : ℝ)) (b := (162370528379 / 100000000000000 : ℝ)) (q := (5633567989 / 250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12686])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12686])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12686]

theorem cert12687_40 : CellCertificate 12687 (443527041184867 / 5000000000000000 : ℝ) (1655587276726543 / 1000000000000000000 : ℝ) (334429088357133 / 10000000000000000 : ℝ)
    (cell12687 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · have h := gap_lower (n := 12687) (a := (41348065077291 / 50000000000000 : ℝ)) (b := (162357573713 / 100000000000000 : ℝ)) (q := (450645590349 / 20000000000000 : ℝ))
      (E := (cell12687 ⟨40, by decide⟩).energy) (xi := (334429088357133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12687 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12687]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12687])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12687) (a := (41348065077291 / 50000000000000 : ℝ)) (b := (162357573713 / 100000000000000 : ℝ)) (q := (450645590349 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12687])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12687])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12687]

theorem cert12687_41 : CellCertificate 12687 (443527041184867 / 5000000000000000 : ℝ) (1655587276726543 / 1000000000000000000 : ℝ) (334429088357133 / 10000000000000000 : ℝ)
    (cell12687 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · have h := gap_lower (n := 12687) (a := (20665530477461 / 25000000000000 : ℝ)) (b := (162357573713 / 100000000000000 : ℝ)) (q := (2253231910203 / 100000000000000 : ℝ))
      (E := (cell12687 ⟨41, by decide⟩).energy) (xi := (334429088357133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12687 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12687]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12687])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12687) (a := (20665530477461 / 25000000000000 : ℝ)) (b := (162357573713 / 100000000000000 : ℝ)) (q := (2253231910203 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12687])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12687])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12687]

theorem cert12687_42 : CellCertificate 12687 (443527041184867 / 5000000000000000 : ℝ) (1655587276726543 / 1000000000000000000 : ℝ) (334429088357133 / 10000000000000000 : ℝ)
    (cell12687 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · have h := gap_lower (n := 12687) (a := (20657034320813 / 25000000000000 : ℝ)) (b := (162357573713 / 100000000000000 : ℝ)) (q := (90129437161 / 4000000000000 : ℝ))
      (E := (cell12687 ⟨42, by decide⟩).energy) (xi := (334429088357133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12687 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12687]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12687])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12687) (a := (20657034320813 / 25000000000000 : ℝ)) (b := (162357573713 / 100000000000000 : ℝ)) (q := (90129437161 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12687])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12687])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12687]

theorem cert12687_43 : CellCertificate 12687 (443527041184867 / 5000000000000000 : ℝ) (1655587276726543 / 1000000000000000000 : ℝ) (334429088357133 / 10000000000000000 : ℝ)
    (cell12687 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · have h := gap_lower (n := 12687) (a := (5162136015319 / 6250000000000 : ℝ)) (b := (162357573713 / 100000000000000 : ℝ)) (q := (2253239948673 / 100000000000000 : ℝ))
      (E := (cell12687 ⟨43, by decide⟩).energy) (xi := (334429088357133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12687 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12687]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12687])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12687) (a := (5162136015319 / 6250000000000 : ℝ)) (b := (162357573713 / 100000000000000 : ℝ)) (q := (2253239948673 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12687])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12687])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12687]

theorem cert12687_44 : CellCertificate 12687 (443527041184867 / 5000000000000000 : ℝ) (1655587276726543 / 1000000000000000000 : ℝ) (334429088357133 / 10000000000000000 : ℝ)
    (cell12687 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · have h := gap_lower (n := 12687) (a := (1651204775317 / 2000000000000 : ℝ)) (b := (162357573713 / 100000000000000 : ℝ)) (q := (1126621984069 / 50000000000000 : ℝ))
      (E := (cell12687 ⟨44, by decide⟩).energy) (xi := (334429088357133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12687 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12687]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12687])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12687) (a := (1651204775317 / 2000000000000 : ℝ)) (b := (162357573713 / 100000000000000 : ℝ)) (q := (1126621984069 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12687])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12687])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12687]

theorem cert12687_45 : CellCertificate 12687 (443527041184867 / 5000000000000000 : ℝ) (1655587276726543 / 1000000000000000000 : ℝ) (334429088357133 / 10000000000000000 : ℝ)
    (cell12687 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · have h := gap_lower (n := 12687) (a := (41263162408043 / 50000000000000 : ℝ)) (b := (162357573713 / 100000000000000 : ℝ)) (q := (225324792733 / 10000000000000 : ℝ))
      (E := (cell12687 ⟨45, by decide⟩).energy) (xi := (334429088357133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12687 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12687]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12687])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12687) (a := (41263162408043 / 50000000000000 : ℝ)) (b := (162357573713 / 100000000000000 : ℝ)) (q := (225324792733 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12687])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12687])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12687]

theorem cert12687_46 : CellCertificate 12687 (443527041184867 / 5000000000000000 : ℝ) (1655587276726543 / 1000000000000000000 : ℝ) (334429088357133 / 10000000000000000 : ℝ)
    (cell12687 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · have h := gap_lower (n := 12687) (a := (41246217183279 / 50000000000000 : ℝ)) (b := (162357573713 / 100000000000000 : ℝ)) (q := (563312985627 / 25000000000000 : ℝ))
      (E := (cell12687 ⟨46, by decide⟩).energy) (xi := (334429088357133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12687 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12687]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12687])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12687) (a := (41246217183279 / 50000000000000 : ℝ)) (b := (162357573713 / 100000000000000 : ℝ)) (q := (563312985627 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12687])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12687])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12687]

theorem cert12687_47 : CellCertificate 12687 (443527041184867 / 5000000000000000 : ℝ) (1655587276726543 / 1000000000000000000 : ℝ) (334429088357133 / 10000000000000000 : ℝ)
    (cell12687 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · have h := gap_lower (n := 12687) (a := (82458567388159 / 100000000000000 : ℝ)) (b := (162357573713 / 100000000000000 : ℝ)) (q := (1126627976587 / 50000000000000 : ℝ))
      (E := (cell12687 ⟨47, by decide⟩).energy) (xi := (334429088357133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12687 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12687]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12687])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12687) (a := (82458567388159 / 100000000000000 : ℝ)) (b := (162357573713 / 100000000000000 : ℝ)) (q := (1126627976587 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12687])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12687])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12687]

theorem cert12687_48 : CellCertificate 12687 (443527041184867 / 5000000000000000 : ℝ) (1655587276726543 / 1000000000000000000 : ℝ) (334429088357133 / 10000000000000000 : ℝ)
    (cell12687 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · have h := gap_lower (n := 12687) (a := (41212361925963 / 50000000000000 : ℝ)) (b := (162357573713 / 100000000000000 : ℝ)) (q := (450651991491 / 20000000000000 : ℝ))
      (E := (cell12687 ⟨48, by decide⟩).energy) (xi := (334429088357133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12687 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12687]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12687])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12687) (a := (41212361925963 / 50000000000000 : ℝ)) (b := (162357573713 / 100000000000000 : ℝ)) (q := (450651991491 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12687])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12687])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12687]

theorem cert12687_49 : CellCertificate 12687 (443527041184867 / 5000000000000000 : ℝ) (1655587276726543 / 1000000000000000000 : ℝ) (334429088357133 / 10000000000000000 : ℝ)
    (cell12687 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · have h := gap_lower (n := 12687) (a := (16478180745809 / 20000000000000 : ℝ)) (b := (162357573713 / 100000000000000 : ℝ)) (q := (1126631976631 / 50000000000000 : ℝ))
      (E := (cell12687 ⟨49, by decide⟩).energy) (xi := (334429088357133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12687 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12687]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12687])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12687) (a := (16478180745809 / 20000000000000 : ℝ)) (b := (162357573713 / 100000000000000 : ℝ)) (q := (1126631976631 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12687])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12687])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12687]

theorem cert12687_50 : CellCertificate 12687 (443527041184867 / 5000000000000000 : ℝ) (1655587276726543 / 1000000000000000000 : ℝ) (334429088357133 / 10000000000000000 : ℝ)
    (cell12687 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · have h := gap_lower (n := 12687) (a := (20589276747711 / 25000000000000 : ℝ)) (b := (162357573713 / 100000000000000 : ℝ)) (q := (90130719891 / 4000000000000 : ℝ))
      (E := (cell12687 ⟨50, by decide⟩).energy) (xi := (334429088357133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12687 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12687]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12687])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12687) (a := (20589276747711 / 25000000000000 : ℝ)) (b := (162357573713 / 100000000000000 : ℝ)) (q := (90130719891 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12687])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12687])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12687]

theorem cert12687_51 : CellCertificate 12687 (443527041184867 / 5000000000000000 : ℝ) (1655587276726543 / 1000000000000000000 : ℝ) (334429088357133 / 10000000000000000 : ℝ)
    (cell12687 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · have h := gap_lower (n := 12687) (a := (16464666721759 / 20000000000000 : ℝ)) (b := (162357573713 / 100000000000000 : ℝ)) (q := (2253271969043 / 100000000000000 : ℝ))
      (E := (cell12687 ⟨51, by decide⟩).energy) (xi := (334429088357133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12687 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12687]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12687])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12687) (a := (16464666721759 / 20000000000000 : ℝ)) (b := (162357573713 / 100000000000000 : ℝ)) (q := (2253271969043 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12687])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12687])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12687]

theorem cert12687_52 : CellCertificate 12687 (443527041184867 / 5000000000000000 : ℝ) (1655587276726543 / 1000000000000000000 : ℝ) (334429088357133 / 10000000000000000 : ℝ)
    (cell12687 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · have h := gap_lower (n := 12687) (a := (82289583554513 / 100000000000000 : ℝ)) (b := (162357573713 / 100000000000000 : ℝ)) (q := (1126637991913 / 50000000000000 : ℝ))
      (E := (cell12687 ⟨52, by decide⟩).energy) (xi := (334429088357133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12687 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12687]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12687])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12687) (a := (82289583554513 / 100000000000000 : ℝ)) (b := (162357573713 / 100000000000000 : ℝ)) (q := (1126637991913 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12687])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12687])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12687]

theorem cert12687_53 : CellCertificate 12687 (443527041184867 / 5000000000000000 : ℝ) (1655587276726543 / 1000000000000000000 : ℝ) (334429088357133 / 10000000000000000 : ℝ)
    (cell12687 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · have h := gap_lower (n := 12687) (a := (20563964199939 / 25000000000000 : ℝ)) (b := (162357573713 / 100000000000000 : ℝ)) (q := (2253279979707 / 100000000000000 : ℝ))
      (E := (cell12687 ⟨53, by decide⟩).energy) (xi := (334429088357133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12687 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12687]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12687])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12687) (a := (20563964199939 / 25000000000000 : ℝ)) (b := (162357573713 / 100000000000000 : ℝ)) (q := (2253279979707 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12687])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12687])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12687]

theorem cert12687_54 : CellCertificate 12687 (443527041184867 / 5000000000000000 : ℝ) (1655587276726543 / 1000000000000000000 : ℝ) (334429088357133 / 10000000000000000 : ℝ)
    (cell12687 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · have h := gap_lower (n := 12687) (a := (41111076658211 / 50000000000000 : ℝ)) (b := (162357573713 / 100000000000000 : ℝ)) (q := (450656802523 / 20000000000000 : ℝ))
      (E := (cell12687 ⟨54, by decide⟩).energy) (xi := (334429088357133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12687 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12687]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12687])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12687) (a := (41111076658211 / 50000000000000 : ℝ)) (b := (162357573713 / 100000000000000 : ℝ)) (q := (450656802523 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12687])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12687])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12687]

theorem cert12687_55 : CellCertificate 12687 (443527041184867 / 5000000000000000 : ℝ) (1655587276726543 / 1000000000000000000 : ℝ) (334429088357133 / 10000000000000000 : ℝ)
    (cell12687 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · have h := gap_lower (n := 12687) (a := (1643769461531 / 2000000000000 : ℝ)) (b := (162357573713 / 100000000000000 : ℝ)) (q := (450657604033 / 20000000000000 : ℝ))
      (E := (cell12687 ⟨55, by decide⟩).energy) (xi := (334429088357133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12687 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12687]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12687])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12687) (a := (1643769461531 / 2000000000000 : ℝ)) (b := (162357573713 / 100000000000000 : ℝ)) (q := (450657604033 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12687])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12687])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12687]

theorem cert12687_56 : CellCertificate 12687 (443527041184867 / 5000000000000000 : ℝ) (1655587276726543 / 1000000000000000000 : ℝ) (334429088357133 / 10000000000000000 : ℝ)
    (cell12687 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · have h := gap_lower (n := 12687) (a := (82154816052319 / 100000000000000 : ℝ)) (b := (162357573713 / 100000000000000 : ℝ)) (q := (1126645999397 / 50000000000000 : ℝ))
      (E := (cell12687 ⟨56, by decide⟩).energy) (xi := (334429088357133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12687 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12687]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12687])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12687) (a := (82154816052319 / 100000000000000 : ℝ)) (b := (162357573713 / 100000000000000 : ℝ)) (q := (1126645999397 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12687])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12687])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12687]

theorem cert12687_57 : CellCertificate 12687 (443527041184867 / 5000000000000000 : ℝ) (1655587276726543 / 1000000000000000000 : ℝ) (334429088357133 / 10000000000000000 : ℝ)
    (cell12687 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · have h := gap_lower (n := 12687) (a := (16424236443209 / 20000000000000 : ℝ)) (b := (162357573713 / 100000000000000 : ℝ)) (q := (563324000969 / 25000000000000 : ℝ))
      (E := (cell12687 ⟨57, by decide⟩).energy) (xi := (334429088357133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12687 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12687]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12687])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12687) (a := (16424236443209 / 20000000000000 : ℝ)) (b := (162357573713 / 100000000000000 : ℝ)) (q := (563324000969 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12687])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12687])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12687]

theorem cert12687_58 : CellCertificate 12687 (443527041184867 / 5000000000000000 : ℝ) (1655587276726543 / 1000000000000000000 : ℝ) (334429088357133 / 10000000000000000 : ℝ)
    (cell12687 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · have h := gap_lower (n := 12687) (a := (16417514308037 / 20000000000000 : ℝ)) (b := (162357573713 / 100000000000000 : ℝ)) (q := (1126650015751 / 50000000000000 : ℝ))
      (E := (cell12687 ⟨58, by decide⟩).energy) (xi := (334429088357133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12687 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12687]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12687])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12687) (a := (16417514308037 / 20000000000000 : ℝ)) (b := (162357573713 / 100000000000000 : ℝ)) (q := (1126650015751 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12687])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12687])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12687]

theorem cert12687_59 : CellCertificate 12687 (443527041184867 / 5000000000000000 : ℝ) (1655587276726543 / 1000000000000000000 : ℝ) (334429088357133 / 10000000000000000 : ℝ)
    (cell12687 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · have h := gap_lower (n := 12687) (a := (8205398399733 / 10000000000000 : ℝ)) (b := (162357573713 / 100000000000000 : ℝ)) (q := (2253304018363 / 100000000000000 : ℝ))
      (E := (cell12687 ⟨59, by decide⟩).energy) (xi := (334429088357133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12687 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12687]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12687])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12687) (a := (8205398399733 / 10000000000000 : ℝ)) (b := (162357573713 / 100000000000000 : ℝ)) (q := (2253304018363 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12687])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12687])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12687]

theorem cert12688_40 : CellCertificate 12688 (887026092752791 / 10000000000000000 : ℝ) (41386418732213 / 25000000000000000 : ℝ) (167201043001823 / 5000000000000000 : ℝ)
    (cell12688 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · have h := gap_lower (n := 12688) (a := (129212699177 / 156250000000 : ℝ)) (b := (20293077641 / 12500000000000 : ℝ)) (q := (2253104767967 / 100000000000000 : ℝ))
      (E := (cell12688 ⟨40, by decide⟩).energy) (xi := (167201043001823 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12688 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12688]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12688])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12688) (a := (129212699177 / 156250000000 : ℝ)) (b := (20293077641 / 12500000000000 : ℝ)) (q := (2253104767967 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12688])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12688])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12688]

theorem cert12688_41 : CellCertificate 12688 (887026092752791 / 10000000000000000 : ℝ) (41386418732213 / 25000000000000000 : ℝ) (167201043001823 / 5000000000000000 : ℝ)
    (cell12688 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · have h := gap_lower (n := 12688) (a := (82662119531677 / 100000000000000 : ℝ)) (b := (20293077641 / 12500000000000 : ℝ)) (q := (563277194799 / 25000000000000 : ℝ))
      (E := (cell12688 ⟨41, by decide⟩).energy) (xi := (167201043001823 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12688 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12688]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12688])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12688) (a := (82662119531677 / 100000000000000 : ℝ)) (b := (20293077641 / 12500000000000 : ℝ)) (q := (563277194799 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12688])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12688])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12688]

theorem cert12688_42 : CellCertificate 12688 (887026092752791 / 10000000000000000 : ℝ) (41386418732213 / 25000000000000000 : ℝ) (167201043001823 / 5000000000000000 : ℝ)
    (cell12688 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · have h := gap_lower (n := 12688) (a := (41314067603901 / 50000000000000 : ℝ)) (b := (20293077641 / 12500000000000 : ℝ)) (q := (70409774773 / 3125000000000 : ℝ))
      (E := (cell12688 ⟨42, by decide⟩).energy) (xi := (167201043001823 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12688 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12688]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12688])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12688) (a := (41314067603901 / 50000000000000 : ℝ)) (b := (20293077641 / 12500000000000 : ℝ)) (q := (70409774773 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12688])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12688])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12688]

theorem cert12688_43 : CellCertificate 12688 (887026092752791 / 10000000000000000 : ℝ) (41386418732213 / 25000000000000000 : ℝ) (167201043001823 / 5000000000000000 : ℝ)
    (cell12688 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · have h := gap_lower (n := 12688) (a := (82594174471953 / 100000000000000 : ℝ)) (b := (20293077641 / 12500000000000 : ℝ)) (q := (2253116807797 / 100000000000000 : ℝ))
      (E := (cell12688 ⟨43, by decide⟩).energy) (xi := (167201043001823 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12688 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12688]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12688])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12688) (a := (82594174471953 / 100000000000000 : ℝ)) (b := (20293077641 / 12500000000000 : ℝ)) (q := (2253116807797 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12688])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12688])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12688]

theorem cert12688_44 : CellCertificate 12688 (887026092752791 / 10000000000000000 : ℝ) (41386418732213 / 25000000000000000 : ℝ) (167201043001823 / 5000000000000000 : ℝ)
    (cell12688 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · have h := gap_lower (n := 12688) (a := (82560237294581 / 100000000000000 : ℝ)) (b := (20293077641 / 12500000000000 : ℝ)) (q := (2253120764527 / 100000000000000 : ℝ))
      (E := (cell12688 ⟨44, by decide⟩).energy) (xi := (167201043001823 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12688 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12688]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12688])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12688) (a := (82560237294581 / 100000000000000 : ℝ)) (b := (20293077641 / 12500000000000 : ℝ)) (q := (2253120764527 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12688])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12688])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12688]

theorem cert12688_45 : CellCertificate 12688 (887026092752791 / 10000000000000000 : ℝ) (41386418732213 / 25000000000000000 : ℝ) (167201043001823 / 5000000000000000 : ℝ)
    (cell12688 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · have h := gap_lower (n := 12688) (a := (20631580911571 / 25000000000000 : ℝ)) (b := (20293077641 / 12500000000000 : ℝ)) (q := (563281194839 / 25000000000000 : ℝ))
      (E := (cell12688 ⟨45, by decide⟩).energy) (xi := (167201043001823 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12688 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12688]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12688])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12688) (a := (20631580911571 / 25000000000000 : ℝ)) (b := (20293077641 / 12500000000000 : ℝ)) (q := (563281194839 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12688])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12688])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12688]

theorem cert12688_46 : CellCertificate 12688 (887026092752791 / 10000000000000000 : ℝ) (41386418732213 / 25000000000000000 : ℝ) (167201043001823 / 5000000000000000 : ℝ)
    (cell12688 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · have h := gap_lower (n := 12688) (a := (82492433497807 / 100000000000000 : ℝ)) (b := (20293077641 / 12500000000000 : ℝ)) (q := (2253128792023 / 100000000000000 : ℝ))
      (E := (cell12688 ⟨46, by decide⟩).energy) (xi := (167201043001823 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12688 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12688]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12688])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12688) (a := (82492433497807 / 100000000000000 : ℝ)) (b := (20293077641 / 12500000000000 : ℝ)) (q := (2253128792023 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12688])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12688])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12688]

theorem cert12688_47 : CellCertificate 12688 (887026092752791 / 10000000000000000 : ℝ) (41386418732213 / 25000000000000000 : ℝ) (167201043001823 / 5000000000000000 : ℝ)
    (cell12688 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · have h := gap_lower (n := 12688) (a := (82458566820043 / 100000000000000 : ℝ)) (b := (20293077641 / 12500000000000 : ℝ)) (q := (225313280087 / 10000000000000 : ℝ))
      (E := (cell12688 ⟨47, by decide⟩).energy) (xi := (167201043001823 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12688 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12688]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12688])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12688) (a := (82458566820043 / 100000000000000 : ℝ)) (b := (20293077641 / 12500000000000 : ℝ)) (q := (225313280087 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12688])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12688])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12688]

theorem cert12688_48 : CellCertificate 12688 (887026092752791 / 10000000000000000 : ℝ) (41386418732213 / 25000000000000000 : ℝ) (167201043001823 / 5000000000000000 : ℝ)
    (cell12688 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · have h := gap_lower (n := 12688) (a := (41212361792017 / 50000000000000 : ℝ)) (b := (20293077641 / 12500000000000 : ℝ)) (q := (2253136804019 / 100000000000000 : ℝ))
      (E := (cell12688 ⟨48, by decide⟩).energy) (xi := (167201043001823 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12688 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12688]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12688])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12688) (a := (41212361792017 / 50000000000000 : ℝ)) (b := (20293077641 / 12500000000000 : ℝ)) (q := (2253136804019 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12688])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12688])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12688]

theorem cert12688_49 : CellCertificate 12688 (887026092752791 / 10000000000000000 : ℝ) (41386418732213 / 25000000000000000 : ℝ) (167201043001823 / 5000000000000000 : ℝ)
    (cell12688 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · have h := gap_lower (n := 12688) (a := (41195451880481 / 50000000000000 : ℝ)) (b := (20293077641 / 12500000000000 : ℝ)) (q := (1126570399693 / 50000000000000 : ℝ))
      (E := (cell12688 ⟨49, by decide⟩).energy) (xi := (167201043001823 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12688 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12688]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12688])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12688) (a := (41195451880481 / 50000000000000 : ℝ)) (b := (20293077641 / 12500000000000 : ℝ)) (q := (1126570399693 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12688])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12688])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12688]

theorem cert12688_50 : CellCertificate 12688 (887026092752791 / 10000000000000000 : ℝ) (41386418732213 / 25000000000000000 : ℝ) (167201043001823 / 5000000000000000 : ℝ)
    (cell12688 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · have h := gap_lower (n := 12688) (a := (41178553661079 / 50000000000000 : ℝ)) (b := (20293077641 / 12500000000000 : ℝ)) (q := (1126572392333 / 50000000000000 : ℝ))
      (E := (cell12688 ⟨50, by decide⟩).energy) (xi := (167201043001823 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12688 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12688]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12688])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12688) (a := (41178553661079 / 50000000000000 : ℝ)) (b := (20293077641 / 12500000000000 : ℝ)) (q := (1126572392333 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12688])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12688])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12688]

theorem cert12688_51 : CellCertificate 12688 (887026092752791 / 10000000000000000 : ℝ) (41386418732213 / 25000000000000000 : ℝ) (167201043001823 / 5000000000000000 : ℝ)
    (cell12688 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · have h := gap_lower (n := 12688) (a := (41161667119547 / 50000000000000 : ℝ)) (b := (20293077641 / 12500000000000 : ℝ)) (q := (2253148816351 / 100000000000000 : ℝ))
      (E := (cell12688 ⟨51, by decide⟩).energy) (xi := (167201043001823 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12688 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12688]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12688])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12688) (a := (41161667119547 / 50000000000000 : ℝ)) (b := (20293077641 / 12500000000000 : ℝ)) (q := (2253148816351 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12688])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12688])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12688]

theorem cert12688_52 : CellCertificate 12688 (887026092752791 / 10000000000000000 : ℝ) (41386418732213 / 25000000000000000 : ℝ) (167201043001823 / 5000000000000000 : ℝ)
    (cell12688 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · have h := gap_lower (n := 12688) (a := (82289584483387 / 100000000000000 : ℝ)) (b := (20293077641 / 12500000000000 : ℝ)) (q := (2253152832757 / 100000000000000 : ℝ))
      (E := (cell12688 ⟨52, by decide⟩).energy) (xi := (167201043001823 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12688 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12688]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12688])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12688) (a := (82289584483387 / 100000000000000 : ℝ)) (b := (20293077641 / 12500000000000 : ℝ)) (q := (2253152832757 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12688])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12688])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12688]

theorem cert12688_53 : CellCertificate 12688 (887026092752791 / 10000000000000000 : ℝ) (41386418732213 / 25000000000000000 : ℝ) (167201043001823 / 5000000000000000 : ℝ)
    (cell12688 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · have h := gap_lower (n := 12688) (a := (41127929013397 / 50000000000000 : ℝ)) (b := (20293077641 / 12500000000000 : ℝ)) (q := (2253156830947 / 100000000000000 : ℝ))
      (E := (cell12688 ⟨53, by decide⟩).energy) (xi := (167201043001823 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12688 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12688]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12688])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12688) (a := (41127929013397 / 50000000000000 : ℝ)) (b := (20293077641 / 12500000000000 : ℝ)) (q := (2253156830947 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12688])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12688])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12688]

theorem cert12688_54 : CellCertificate 12688 (887026092752791 / 10000000000000000 : ℝ) (41386418732213 / 25000000000000000 : ℝ) (167201043001823 / 5000000000000000 : ℝ)
    (cell12688 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · have h := gap_lower (n := 12688) (a := (16444430968243 / 20000000000000 : ℝ)) (b := (20293077641 / 12500000000000 : ℝ)) (q := (90126432311 / 4000000000000 : ℝ))
      (E := (cell12688 ⟨54, by decide⟩).energy) (xi := (167201043001823 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12688 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12688]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12688])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12688) (a := (16444430968243 / 20000000000000 : ℝ)) (b := (20293077641 / 12500000000000 : ℝ)) (q := (90126432311 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12688])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12688])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12688]

theorem cert12688_55 : CellCertificate 12688 (887026092752791 / 10000000000000000 : ℝ) (41386418732213 / 25000000000000000 : ℝ) (167201043001823 / 5000000000000000 : ℝ)
    (cell12688 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · have h := gap_lower (n := 12688) (a := (8218847489869 / 10000000000000 : ℝ)) (b := (20293077641 / 12500000000000 : ℝ)) (q := (1126582409491 / 50000000000000 : ℝ))
      (E := (cell12688 ⟨55, by decide⟩).energy) (xi := (167201043001823 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12688 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12688]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12688])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12688) (a := (8218847489869 / 10000000000000 : ℝ)) (b := (20293077641 / 12500000000000 : ℝ)) (q := (1126582409491 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12688])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12688])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12688]

theorem cert12688_56 : CellCertificate 12688 (887026092752791 / 10000000000000000 : ℝ) (41386418732213 / 25000000000000000 : ℝ) (167201043001823 / 5000000000000000 : ℝ)
    (cell12688 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · have h := gap_lower (n := 12688) (a := (20538704542849 / 25000000000000 : ℝ)) (b := (20293077641 / 12500000000000 : ℝ)) (q := (563292215269 / 25000000000000 : ℝ))
      (E := (cell12688 ⟨56, by decide⟩).energy) (xi := (167201043001823 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12688 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12688]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12688])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12688) (a := (20538704542849 / 25000000000000 : ℝ)) (b := (20293077641 / 12500000000000 : ℝ)) (q := (563292215269 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12688])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12688])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12688]

theorem cert12688_57 : CellCertificate 12688 (887026092752791 / 10000000000000000 : ℝ) (41386418732213 / 25000000000000000 : ℝ) (167201043001823 / 5000000000000000 : ℝ)
    (cell12688 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · have h := gap_lower (n := 12688) (a := (82121184631653 / 100000000000000 : ℝ)) (b := (20293077641 / 12500000000000 : ℝ)) (q := (2253172871207 / 100000000000000 : ℝ))
      (E := (cell12688 ⟨57, by decide⟩).energy) (xi := (167201043001823 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12688 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12688]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12688])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12688) (a := (82121184631653 / 100000000000000 : ℝ)) (b := (20293077641 / 12500000000000 : ℝ)) (q := (2253172871207 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12688])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12688])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12688]

theorem cert12688_58 : CellCertificate 12688 (887026092752791 / 10000000000000000 : ℝ) (41386418732213 / 25000000000000000 : ℝ) (167201043001823 / 5000000000000000 : ℝ)
    (cell12688 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · have h := gap_lower (n := 12688) (a := (20521893562979 / 25000000000000 : ℝ)) (b := (20293077641 / 12500000000000 : ℝ)) (q := (563294211349 / 25000000000000 : ℝ))
      (E := (cell12688 ⟨58, by decide⟩).energy) (xi := (167201043001823 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12688 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12688]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12688])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12688) (a := (20521893562979 / 25000000000000 : ℝ)) (b := (20293077641 / 12500000000000 : ℝ)) (q := (563294211349 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12688])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12688])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12688]

theorem cert12688_59 : CellCertificate 12688 (887026092752791 / 10000000000000000 : ℝ) (41386418732213 / 25000000000000000 : ℝ) (167201043001823 / 5000000000000000 : ℝ)
    (cell12688 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · have h := gap_lower (n := 12688) (a := (82053987004779 / 100000000000000 : ℝ)) (b := (20293077641 / 12500000000000 : ℝ)) (q := (45063616773 / 2000000000000 : ℝ))
      (E := (cell12688 ⟨59, by decide⟩).energy) (xi := (167201043001823 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12688 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12688]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12688])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12688) (a := (82053987004779 / 100000000000000 : ℝ)) (b := (20293077641 / 12500000000000 : ℝ)) (q := (45063616773 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12688])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12688])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12688]

theorem cert12689_40 : CellCertificate 12689 (886998107372131 / 10000000000000000 : ℝ) (1655326242430587 / 1000000000000000000 : ℝ) (167187544035849 / 5000000000000000 : ℝ)
    (cell12689 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · have h := gap_lower (n := 12689) (a := (82696124792853 / 100000000000000 : ℝ)) (b := (259730673 / 160000000000 : ℝ)) (q := (281622704969 / 12500000000000 : ℝ))
      (E := (cell12689 ⟨40, by decide⟩).energy) (xi := (167187544035849 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12689 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12689]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12689])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12689) (a := (82696124792853 / 100000000000000 : ℝ)) (b := (259730673 / 160000000000 : ℝ)) (q := (281622704969 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12689])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12689])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12689]

theorem cert12689_41 : CellCertificate 12689 (886998107372131 / 10000000000000000 : ℝ) (1655326242430587 / 1000000000000000000 : ℝ) (167187544035849 / 5000000000000000 : ℝ)
    (cell12689 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · have h := gap_lower (n := 12689) (a := (82662117154349 / 100000000000000 : ℝ)) (b := (259730673 / 160000000000 : ℝ)) (q := (1126492822521 / 50000000000000 : ℝ))
      (E := (cell12689 ⟨41, by decide⟩).energy) (xi := (167187544035849 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12689 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12689]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12689])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12689) (a := (82662117154349 / 100000000000000 : ℝ)) (b := (259730673 / 160000000000 : ℝ)) (q := (1126492822521 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12689])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12689])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12689]

theorem cert12689_42 : CellCertificate 12689 (886998107372131 / 10000000000000000 : ℝ) (1655326242430587 / 1000000000000000000 : ℝ) (167187544035849 / 5000000000000000 : ℝ)
    (cell12689 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · have h := gap_lower (n := 12689) (a := (82628133133153 / 100000000000000 : ℝ)) (b := (259730673 / 160000000000 : ℝ)) (q := (112649482667 / 5000000000000 : ℝ))
      (E := (cell12689 ⟨42, by decide⟩).energy) (xi := (167187544035849 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12689 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12689]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12689])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12689) (a := (82628133133153 / 100000000000000 : ℝ)) (b := (259730673 / 160000000000 : ℝ)) (q := (112649482667 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12689])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12689])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12689]

theorem cert12689_43 : CellCertificate 12689 (886998107372131 / 10000000000000000 : ℝ) (1655326242430587 / 1000000000000000000 : ℝ) (167187544035849 / 5000000000000000 : ℝ)
    (cell12689 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · have h := gap_lower (n := 12689) (a := (82594172699567 / 100000000000000 : ℝ)) (b := (259730673 / 160000000000 : ℝ)) (q := (2252993663851 / 100000000000000 : ℝ))
      (E := (cell12689 ⟨43, by decide⟩).energy) (xi := (167187544035849 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12689 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12689]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12689])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12689) (a := (82594172699567 / 100000000000000 : ℝ)) (b := (259730673 / 160000000000 : ℝ)) (q := (2252993663851 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12689])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12689])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12689]

theorem cert12689_44 : CellCertificate 12689 (886998107372131 / 10000000000000000 : ℝ) (1655326242430587 / 1000000000000000000 : ℝ) (167187544035849 / 5000000000000000 : ℝ)
    (cell12689 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · have h := gap_lower (n := 12689) (a := (82560235824041 / 100000000000000 : ℝ)) (b := (259730673 / 160000000000 : ℝ)) (q := (2252997675563 / 100000000000000 : ℝ))
      (E := (cell12689 ⟨44, by decide⟩).energy) (xi := (167187544035849 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12689 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12689]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12689])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12689) (a := (82560235824041 / 100000000000000 : ℝ)) (b := (259730673 / 160000000000 : ℝ)) (q := (2252997675563 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12689])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12689])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12689]

theorem cert12689_45 : CellCertificate 12689 (886998107372131 / 10000000000000000 : ℝ) (1655326242430587 / 1000000000000000000 : ℝ) (167187544035849 / 5000000000000000 : ℝ)
    (cell12689 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · have h := gap_lower (n := 12689) (a := (82526322477173 / 100000000000000 : ℝ)) (b := (259730673 / 160000000000 : ℝ)) (q := (2253001687251 / 100000000000000 : ℝ))
      (E := (cell12689 ⟨45, by decide⟩).energy) (xi := (167187544035849 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12689 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12689]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12689])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12689) (a := (82526322477173 / 100000000000000 : ℝ)) (b := (259730673 / 160000000000 : ℝ)) (q := (2253001687251 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12689])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12689])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12689]

theorem cert12689_46 : CellCertificate 12689 (886998107372131 / 10000000000000000 : ℝ) (1655326242430587 / 1000000000000000000 : ℝ) (167187544035849 / 5000000000000000 : ℝ)
    (cell12689 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · have h := gap_lower (n := 12689) (a := (82492432629711 / 100000000000000 : ℝ)) (b := (259730673 / 160000000000 : ℝ)) (q := (563251424367 / 25000000000000 : ℝ))
      (E := (cell12689 ⟨46, by decide⟩).energy) (xi := (167187544035849 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12689 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12689]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12689])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12689) (a := (82492432629711 / 100000000000000 : ℝ)) (b := (259730673 / 160000000000 : ℝ)) (q := (563251424367 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12689])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12689])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12689]

theorem cert12689_47 : CellCertificate 12689 (886998107372131 / 10000000000000000 : ℝ) (1655326242430587 / 1000000000000000000 : ℝ) (167187544035849 / 5000000000000000 : ℝ)
    (cell12689 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · have h := gap_lower (n := 12689) (a := (20614641563137 / 25000000000000 : ℝ)) (b := (259730673 / 160000000000 : ℝ)) (q := (2253009645643 / 100000000000000 : ℝ))
      (E := (cell12689 ⟨47, by decide⟩).energy) (xi := (167187544035849 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12689 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12689]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12689])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12689) (a := (20614641563137 / 25000000000000 : ℝ)) (b := (259730673 / 160000000000 : ℝ)) (q := (2253009645643 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12689])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12689])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12689]

theorem cert12689_48 : CellCertificate 12689 (886998107372131 / 10000000000000000 : ℝ) (1655326242430587 / 1000000000000000000 : ℝ) (167187544035849 / 5000000000000000 : ℝ)
    (cell12689 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · have h := gap_lower (n := 12689) (a := (20606180829181 / 25000000000000 : ℝ)) (b := (259730673 / 160000000000 : ℝ)) (q := (450602741327 / 20000000000000 : ℝ))
      (E := (cell12689 ⟨48, by decide⟩).energy) (xi := (167187544035849 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12689 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12689]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12689])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12689) (a := (20606180829181 / 25000000000000 : ℝ)) (b := (259730673 / 160000000000 : ℝ)) (q := (450602741327 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12689])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12689])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12689]

theorem cert12689_49 : CellCertificate 12689 (886998107372131 / 10000000000000000 : ℝ) (1655326242430587 / 1000000000000000000 : ℝ) (167187544035849 / 5000000000000000 : ℝ)
    (cell12689 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · have h := gap_lower (n := 12689) (a := (41195451896713 / 50000000000000 : ℝ)) (b := (259730673 / 160000000000 : ℝ)) (q := (112650885081 / 5000000000000 : ℝ))
      (E := (cell12689 ⟨49, by decide⟩).energy) (xi := (167187544035849 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12689 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12689]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12689])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12689) (a := (41195451896713 / 50000000000000 : ℝ)) (b := (259730673 / 160000000000 : ℝ)) (q := (112650885081 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12689])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12689])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12689]

theorem cert12689_50 : CellCertificate 12689 (886998107372131 / 10000000000000000 : ℝ) (1655326242430587 / 1000000000000000000 : ℝ) (167187544035849 / 5000000000000000 : ℝ)
    (cell12689 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · have h := gap_lower (n := 12689) (a := (41178553826991 / 50000000000000 : ℝ)) (b := (259730673 / 160000000000 : ℝ)) (q := (2253021687209 / 100000000000000 : ℝ))
      (E := (cell12689 ⟨50, by decide⟩).energy) (xi := (167187544035849 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12689 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12689]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12689])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12689) (a := (41178553826991 / 50000000000000 : ℝ)) (b := (259730673 / 160000000000 : ℝ)) (q := (2253021687209 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12689])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12689])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12689]

theorem cert12689_51 : CellCertificate 12689 (886998107372131 / 10000000000000000 : ℝ) (1655326242430587 / 1000000000000000000 : ℝ) (167187544035849 / 5000000000000000 : ℝ)
    (cell12689 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · have h := gap_lower (n := 12689) (a := (20580833717467 / 25000000000000 : ℝ)) (b := (259730673 / 160000000000 : ℝ)) (q := (225302571989 / 10000000000000 : ℝ))
      (E := (cell12689 ⟨51, by decide⟩).energy) (xi := (167187544035849 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12689 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12689]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12689])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12689) (a := (20580833717467 / 25000000000000 : ℝ)) (b := (259730673 / 160000000000 : ℝ)) (q := (225302571989 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12689])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12689])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12689]

theorem cert12689_52 : CellCertificate 12689 (886998107372131 / 10000000000000000 : ℝ) (1655326242430587 / 1000000000000000000 : ℝ) (167187544035849 / 5000000000000000 : ℝ)
    (cell12689 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · have h := gap_lower (n := 12689) (a := (82289585412699 / 100000000000000 : ℝ)) (b := (259730673 / 160000000000 : ℝ)) (q := (2253029678951 / 100000000000000 : ℝ))
      (E := (cell12689 ⟨52, by decide⟩).energy) (xi := (167187544035849 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12689 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12689]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12689])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12689) (a := (82289585412699 / 100000000000000 : ℝ)) (b := (259730673 / 160000000000 : ℝ)) (q := (2253029678951 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12689])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12689])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12689]

theorem cert12689_53 : CellCertificate 12689 (886998107372131 / 10000000000000000 : ℝ) (1655326242430587 / 1000000000000000000 : ℝ) (167187544035849 / 5000000000000000 : ℝ)
    (cell12689 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · have h := gap_lower (n := 12689) (a := (16451171850847 / 20000000000000 : ℝ)) (b := (259730673 / 160000000000 : ℝ)) (q := (17601825621 / 781250000000 : ℝ))
      (E := (cell12689 ⟨53, by decide⟩).energy) (xi := (167187544035849 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12689 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12689]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12689])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12689) (a := (16451171850847 / 20000000000000 : ℝ)) (b := (259730673 / 160000000000 : ℝ)) (q := (17601825621 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12689])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12689])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12689]

theorem cert12689_54 : CellCertificate 12689 (886998107372131 / 10000000000000000 : ℝ) (1655326242430587 / 1000000000000000000 : ℝ) (167187544035849 / 5000000000000000 : ℝ)
    (cell12689 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · have h := gap_lower (n := 12689) (a := (41111078183187 / 50000000000000 : ℝ)) (b := (259730673 / 160000000000 : ℝ)) (q := (281629714803 / 12500000000000 : ℝ))
      (E := (cell12689 ⟨54, by decide⟩).energy) (xi := (167187544035849 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12689 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12689]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12689])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12689) (a := (41111078183187 / 50000000000000 : ℝ)) (b := (259730673 / 160000000000 : ℝ)) (q := (281629714803 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12689])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12689])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12689]

theorem cert12689_55 : CellCertificate 12689 (886998107372131 / 10000000000000000 : ℝ) (1655326242430587 / 1000000000000000000 : ℝ) (167187544035849 / 5000000000000000 : ℝ)
    (cell12689 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · have h := gap_lower (n := 12689) (a := (82188476721159 / 100000000000000 : ℝ)) (b := (259730673 / 160000000000 : ℝ)) (q := (563260433343 / 25000000000000 : ℝ))
      (E := (cell12689 ⟨55, by decide⟩).energy) (xi := (167187544035849 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12689 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12689]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12689])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12689) (a := (82188476721159 / 100000000000000 : ℝ)) (b := (259730673 / 160000000000 : ℝ)) (q := (563260433343 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12689])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12689])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12689]

theorem cert12689_56 : CellCertificate 12689 (886998107372131 / 10000000000000000 : ℝ) (1655326242430587 / 1000000000000000000 : ℝ) (167187544035849 / 5000000000000000 : ℝ)
    (cell12689 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · have h := gap_lower (n := 12689) (a := (82154820290767 / 100000000000000 : ℝ)) (b := (259730673 / 160000000000 : ℝ)) (q := (225304572077 / 10000000000000 : ℝ))
      (E := (cell12689 ⟨56, by decide⟩).energy) (xi := (167187544035849 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12689 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12689]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12689])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12689) (a := (82154820290767 / 100000000000000 : ℝ)) (b := (259730673 / 160000000000 : ℝ)) (q := (225304572077 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12689])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12689])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12689]

theorem cert12689_57 : CellCertificate 12689 (886998107372131 / 10000000000000000 : ℝ) (1655326242430587 / 1000000000000000000 : ℝ) (167187544035849 / 5000000000000000 : ℝ)
    (cell12689 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · have h := gap_lower (n := 12689) (a := (82121187047519 / 100000000000000 : ℝ)) (b := (259730673 / 160000000000 : ℝ)) (q := (2253049735987 / 100000000000000 : ℝ))
      (E := (cell12689 ⟨57, by decide⟩).energy) (xi := (167187544035849 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12689 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12689]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12689])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12689) (a := (82121187047519 / 100000000000000 : ℝ)) (b := (259730673 / 160000000000 : ℝ)) (q := (2253049735987 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12689])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12689])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12689]

theorem cert12689_58 : CellCertificate 12689 (886998107372131 / 10000000000000000 : ℝ) (1655326242430587 / 1000000000000000000 : ℝ) (167187544035849 / 5000000000000000 : ℝ)
    (cell12689 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · have h := gap_lower (n := 12689) (a := (8208757696387 / 10000000000000 : ℝ)) (b := (259730673 / 160000000000 : ℝ)) (q := (450610743189 / 20000000000000 : ℝ))
      (E := (cell12689 ⟨58, by decide⟩).energy) (xi := (167187544035849 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12689 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12689]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12689])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12689) (a := (8208757696387 / 10000000000000 : ℝ)) (b := (259730673 / 160000000000 : ℝ)) (q := (450610743189 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12689])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12689])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12689]

theorem cert12689_59 : CellCertificate 12689 (886998107372131 / 10000000000000000 : ℝ) (1655326242430587 / 1000000000000000000 : ℝ) (167187544035849 / 5000000000000000 : ℝ)
    (cell12689 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · have h := gap_lower (n := 12689) (a := (16410798002483 / 20000000000000 : ℝ)) (b := (259730673 / 160000000000 : ℝ)) (q := (45061154313 / 2000000000000 : ℝ))
      (E := (cell12689 ⟨59, by decide⟩).energy) (xi := (167187544035849 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12689 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12689]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12689])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12689) (a := (16410798002483 / 20000000000000 : ℝ)) (b := (259730673 / 160000000000 : ℝ)) (q := (45061154313 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12689])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12689])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12689]

theorem cert12690_40 : CellCertificate 12690 (177394025245349 / 2000000000000000 : ℝ) (1655195756147877 / 1000000000000000000 : ℝ) (167174047280053 / 5000000000000000 : ℝ)
    (cell12690 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · have h := gap_lower (n := 12690) (a := (41348061056651 / 50000000000000 : ℝ)) (b := (40579680551 / 25000000000000 : ℝ)) (q := (2252858567099 / 100000000000000 : ℝ))
      (E := (cell12690 ⟨40, by decide⟩).energy) (xi := (167174047280053 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12690 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12690]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12690])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12690) (a := (41348061056651 / 50000000000000 : ℝ)) (b := (40579680551 / 25000000000000 : ℝ)) (q := (2252858567099 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12690])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12690])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12690]

theorem cert12690_41 : CellCertificate 12690 (177394025245349 / 2000000000000000 : ℝ) (1655195756147877 / 1000000000000000000 : ℝ) (167174047280053 / 5000000000000000 : ℝ)
    (cell12690 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · have h := gap_lower (n := 12690) (a := (82662114777859 / 100000000000000 : ℝ)) (b := (40579680551 / 25000000000000 : ℝ)) (q := (1126431283257 / 50000000000000 : ℝ))
      (E := (cell12690 ⟨41, by decide⟩).energy) (xi := (167174047280053 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12690 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12690]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12690])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12690) (a := (82662114777859 / 100000000000000 : ℝ)) (b := (40579680551 / 25000000000000 : ℝ)) (q := (1126431283257 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12690])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12690])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12690]

theorem cert12690_42 : CellCertificate 12690 (177394025245349 / 2000000000000000 : ℝ) (1655195756147877 / 1000000000000000000 : ℝ) (167174047280053 / 5000000000000000 : ℝ)
    (cell12690 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · have h := gap_lower (n := 12690) (a := (82628131059307 / 100000000000000 : ℝ)) (b := (40579680551 / 25000000000000 : ℝ)) (q := (563216642407 / 25000000000000 : ℝ))
      (E := (cell12690 ⟨42, by decide⟩).energy) (xi := (167174047280053 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12690 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12690]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12690])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12690) (a := (82628131059307 / 100000000000000 : ℝ)) (b := (40579680551 / 25000000000000 : ℝ)) (q := (563216642407 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12690])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12690])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12690]

theorem cert12690_43 : CellCertificate 12690 (177394025245349 / 2000000000000000 : ℝ) (1655195756147877 / 1000000000000000000 : ℝ) (167174047280053 / 5000000000000000 : ℝ)
    (cell12690 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · have h := gap_lower (n := 12690) (a := (82594170927947 / 100000000000000 : ℝ)) (b := (40579680551 / 25000000000000 : ℝ)) (q := (45057411513 / 2000000000000 : ℝ))
      (E := (cell12690 ⟨43, by decide⟩).energy) (xi := (167174047280053 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12690 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12690]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12690])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12690) (a := (82594170927947 / 100000000000000 : ℝ)) (b := (40579680551 / 25000000000000 : ℝ)) (q := (45057411513 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12690])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12690])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12690]

theorem cert12690_44 : CellCertificate 12690 (177394025245349 / 2000000000000000 : ℝ) (1655195756147877 / 1000000000000000000 : ℝ) (167174047280053 / 5000000000000000 : ℝ)
    (cell12690 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · have h := gap_lower (n := 12690) (a := (8256023435423 / 10000000000000 : ℝ)) (b := (40579680551 / 25000000000000 : ℝ)) (q := (1126437291783 / 50000000000000 : ℝ))
      (E := (cell12690 ⟨44, by decide⟩).energy) (xi := (167174047280053 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12690 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12690]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12690])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12690) (a := (8256023435423 / 10000000000000 : ℝ)) (b := (40579680551 / 25000000000000 : ℝ)) (q := (1126437291783 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12690])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12690])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12690]

theorem cert12690_45 : CellCertificate 12690 (177394025245349 / 2000000000000000 : ℝ) (1655195756147877 / 1000000000000000000 : ℝ) (167174047280053 / 5000000000000000 : ℝ)
    (cell12690 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · have h := gap_lower (n := 12690) (a := (16505264261751 / 20000000000000 : ℝ)) (b := (40579680551 / 25000000000000 : ℝ)) (q := (45057571843 / 2000000000000 : ℝ))
      (E := (cell12690 ⟨45, by decide⟩).energy) (xi := (167174047280053 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12690 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12690]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12690])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12690) (a := (16505264261751 / 20000000000000 : ℝ)) (b := (40579680551 / 25000000000000 : ℝ)) (q := (45057571843 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12690])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12690])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12690]

theorem cert12690_46 : CellCertificate 12690 (177394025245349 / 2000000000000000 : ℝ) (1655195756147877 / 1000000000000000000 : ℝ) (167174047280053 / 5000000000000000 : ℝ)
    (cell12690 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · have h := gap_lower (n := 12690) (a := (82492431762271 / 100000000000000 : ℝ)) (b := (40579680551 / 25000000000000 : ℝ)) (q := (2252882599953 / 100000000000000 : ℝ))
      (E := (cell12690 ⟨46, by decide⟩).energy) (xi := (167174047280053 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12690 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12690]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12690])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12690) (a := (82492431762271 / 100000000000000 : ℝ)) (b := (40579680551 / 25000000000000 : ℝ)) (q := (2252882599953 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12690])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12690])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12690]

theorem cert12690_47 : CellCertificate 12690 (177394025245349 / 2000000000000000 : ℝ) (1655195756147877 / 1000000000000000000 : ℝ) (167174047280053 / 5000000000000000 : ℝ)
    (cell12690 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · have h := gap_lower (n := 12690) (a := (82458565685671 / 100000000000000 : ℝ)) (b := (40579680551 / 25000000000000 : ℝ)) (q := (1126443302659 / 50000000000000 : ℝ))
      (E := (cell12690 ⟨47, by decide⟩).energy) (xi := (167174047280053 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12690 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12690]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12690])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12690) (a := (82458565685671 / 100000000000000 : ℝ)) (b := (40579680551 / 25000000000000 : ℝ)) (q := (1126443302659 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12690])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12690])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12690]

theorem cert12690_48 : CellCertificate 12690 (177394025245349 / 2000000000000000 : ℝ) (1655195756147877 / 1000000000000000000 : ℝ) (167174047280053 / 5000000000000000 : ℝ)
    (cell12690 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · have h := gap_lower (n := 12690) (a := (82424723049997 / 100000000000000 : ℝ)) (b := (40579680551 / 25000000000000 : ℝ)) (q := (2252890606367 / 100000000000000 : ℝ))
      (E := (cell12690 ⟨48, by decide⟩).energy) (xi := (167174047280053 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12690 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12690]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12690])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12690) (a := (82424723049997 / 100000000000000 : ℝ)) (b := (40579680551 / 25000000000000 : ℝ)) (q := (2252890606367 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12690])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12690])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12690]

theorem cert12690_49 : CellCertificate 12690 (177394025245349 / 2000000000000000 : ℝ) (1655195756147877 / 1000000000000000000 : ℝ) (167174047280053 / 5000000000000000 : ℝ)
    (cell12690 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · have h := gap_lower (n := 12690) (a := (20597725956609 / 25000000000000 : ℝ)) (b := (40579680551 / 25000000000000 : ℝ)) (q := (2252894601009 / 100000000000000 : ℝ))
      (E := (cell12690 ⟨49, by decide⟩).energy) (xi := (167174047280053 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12690 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12690]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12690])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12690) (a := (20597725956609 / 25000000000000 : ℝ)) (b := (40579680551 / 25000000000000 : ℝ)) (q := (2252894601009 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12690])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12690])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12690]

theorem cert12690_50 : CellCertificate 12690 (177394025245349 / 2000000000000000 : ℝ) (1655195756147877 / 1000000000000000000 : ℝ) (167174047280053 / 5000000000000000 : ℝ)
    (cell12690 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · have h := gap_lower (n := 12690) (a := (82357107986317 / 100000000000000 : ℝ)) (b := (40579680551 / 25000000000000 : ℝ)) (q := (2252898586943 / 100000000000000 : ℝ))
      (E := (cell12690 ⟨50, by decide⟩).energy) (xi := (167174047280053 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12690 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12690]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12690])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12690) (a := (82357107986317 / 100000000000000 : ℝ)) (b := (40579680551 / 25000000000000 : ℝ)) (q := (2252898586943 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12690])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12690])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12690]

theorem cert12690_51 : CellCertificate 12690 (177394025245349 / 2000000000000000 : ℝ) (1655195756147877 / 1000000000000000000 : ℝ) (167174047280053 / 5000000000000000 : ℝ)
    (cell12690 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · have h := gap_lower (n := 12690) (a := (20580833875279 / 25000000000000 : ℝ)) (b := (40579680551 / 25000000000000 : ℝ)) (q := (2252902620657 / 100000000000000 : ℝ))
      (E := (cell12690 ⟨51, by decide⟩).energy) (xi := (167174047280053 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12690 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12690]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12690])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12690) (a := (20580833875279 / 25000000000000 : ℝ)) (b := (40579680551 / 25000000000000 : ℝ)) (q := (2252902620657 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12690])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12690])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12690]

theorem cert12690_52 : CellCertificate 12690 (177394025245349 / 2000000000000000 : ℝ) (1655195756147877 / 1000000000000000000 : ℝ) (167174047280053 / 5000000000000000 : ℝ)
    (cell12690 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · have h := gap_lower (n := 12690) (a := (82289586342449 / 100000000000000 : ℝ)) (b := (40579680551 / 25000000000000 : ℝ)) (q := (2252906581439 / 100000000000000 : ℝ))
      (E := (cell12690 ⟨52, by decide⟩).energy) (xi := (167174047280053 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12690 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12690]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12690])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12690) (a := (82289586342449 / 100000000000000 : ℝ)) (b := (40579680551 / 25000000000000 : ℝ)) (q := (2252906581439 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12690])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12690])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12690]

theorem cert12690_53 : CellCertificate 12690 (177394025245349 / 2000000000000000 : ℝ) (1655195756147877 / 1000000000000000000 : ℝ) (167174047280053 / 5000000000000000 : ℝ)
    (cell12690 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · have h := gap_lower (n := 12690) (a := (82255860482077 / 100000000000000 : ℝ)) (b := (40579680551 / 25000000000000 : ℝ)) (q := (1126455292191 / 50000000000000 : ℝ))
      (E := (cell12690 ⟨53, by decide⟩).energy) (xi := (167174047280053 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12690 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12690]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12690])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12690) (a := (82255860482077 / 100000000000000 : ℝ)) (b := (40579680551 / 25000000000000 : ℝ)) (q := (1126455292191 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12690])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12690])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12690]

theorem cert12690_54 : CellCertificate 12690 (177394025245349 / 2000000000000000 : ℝ) (1655195756147877 / 1000000000000000000 : ℝ) (167174047280053 / 5000000000000000 : ℝ)
    (cell12690 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · have h := gap_lower (n := 12690) (a := (82222157891899 / 100000000000000 : ℝ)) (b := (40579680551 / 25000000000000 : ℝ)) (q := (2252914626411 / 100000000000000 : ℝ))
      (E := (cell12690 ⟨54, by decide⟩).energy) (xi := (167174047280053 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12690 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12690]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12690])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12690) (a := (82222157891899 / 100000000000000 : ℝ)) (b := (40579680551 / 25000000000000 : ℝ)) (q := (2252914626411 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12690])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12690])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12690]

theorem cert12690_55 : CellCertificate 12690 (177394025245349 / 2000000000000000 : ℝ) (1655195756147877 / 1000000000000000000 : ℝ) (167174047280053 / 5000000000000000 : ℝ)
    (cell12690 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · have h := gap_lower (n := 12690) (a := (82188478543957 / 100000000000000 : ℝ)) (b := (40579680551 / 25000000000000 : ℝ)) (q := (2252918645139 / 100000000000000 : ℝ))
      (E := (cell12690 ⟨55, by decide⟩).energy) (xi := (167174047280053 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12690 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12690]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12690])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12690) (a := (82188478543957 / 100000000000000 : ℝ)) (b := (40579680551 / 25000000000000 : ℝ)) (q := (2252918645139 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12690])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12690])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12690]

theorem cert12690_56 : CellCertificate 12690 (177394025245349 / 2000000000000000 : ℝ) (1655195756147877 / 1000000000000000000 : ℝ) (167174047280053 / 5000000000000000 : ℝ)
    (cell12690 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · have h := gap_lower (n := 12690) (a := (1283669100163 / 1562500000000 : ℝ)) (b := (40579680551 / 25000000000000 : ℝ)) (q := (1126461318499 / 50000000000000 : ℝ))
      (E := (cell12690 ⟨56, by decide⟩).energy) (xi := (167174047280053 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12690 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12690]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12690])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12690) (a := (1283669100163 / 1562500000000 : ℝ)) (b := (40579680551 / 25000000000000 : ℝ)) (q := (1126461318499 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12690])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12690])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12690]

theorem cert12690_57 : CellCertificate 12690 (177394025245349 / 2000000000000000 : ℝ) (1655195756147877 / 1000000000000000000 : ℝ) (167174047280053 / 5000000000000000 : ℝ)
    (cell12690 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · have h := gap_lower (n := 12690) (a := (41060594731821 / 50000000000000 : ℝ)) (b := (40579680551 / 25000000000000 : ℝ)) (q := (1126463328681 / 50000000000000 : ℝ))
      (E := (cell12690 ⟨57, by decide⟩).energy) (xi := (167174047280053 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12690 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12690]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12690])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12690) (a := (41060594731821 / 50000000000000 : ℝ)) (b := (40579680551 / 25000000000000 : ℝ)) (q := (1126463328681 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12690])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12690])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12690]

theorem cert12690_58 : CellCertificate 12690 (177394025245349 / 2000000000000000 : ℝ) (1655195756147877 / 1000000000000000000 : ℝ) (167174047280053 / 5000000000000000 : ℝ)
    (cell12690 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · have h := gap_lower (n := 12690) (a := (16417515935209 / 20000000000000 : ℝ)) (b := (40579680551 / 25000000000000 : ℝ)) (q := (45058612863 / 2000000000000 : ℝ))
      (E := (cell12690 ⟨58, by decide⟩).energy) (xi := (167174047280053 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12690 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12690]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12690])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12690) (a := (16417515935209 / 20000000000000 : ℝ)) (b := (40579680551 / 25000000000000 : ℝ)) (q := (45058612863 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12690])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12690])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12690]

theorem cert12690_59 : CellCertificate 12690 (177394025245349 / 2000000000000000 : ℝ) (1655195756147877 / 1000000000000000000 : ℝ) (167174047280053 / 5000000000000000 : ℝ)
    (cell12690 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · have h := gap_lower (n := 12690) (a := (20513498255059 / 25000000000000 : ℝ)) (b := (40579680551 / 25000000000000 : ℝ)) (q := (281616831171 / 12500000000000 : ℝ))
      (E := (cell12690 ⟨59, by decide⟩).energy) (xi := (167174047280053 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12690 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12690]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12690])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12690) (a := (20513498255059 / 25000000000000 : ℝ)) (b := (40579680551 / 25000000000000 : ℝ)) (q := (281616831171 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12690])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12690])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12690]

theorem cert12691_40 : CellCertificate 12691 (443471074657813 / 5000000000000000 : ℝ) (66202611617421 / 40000000000000000 : ℝ) (33432110546769 / 1000000000000000 : ℝ)
    (cell12691 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · have h := gap_lower (n := 12691) (a := (41348059717313 / 50000000000000 : ℝ)) (b := (81152887931 / 50000000000000 : ℝ)) (q := (2252735491267 / 100000000000000 : ℝ))
      (E := (cell12691 ⟨40, by decide⟩).energy) (xi := (33432110546769 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12691 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12691]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12691])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12691) (a := (41348059717313 / 50000000000000 : ℝ)) (b := (81152887931 / 50000000000000 : ℝ)) (q := (2252735491267 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12691])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12691])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12691]

theorem cert12691_41 : CellCertificate 12691 (443471074657813 / 5000000000000000 : ℝ) (66202611617421 / 40000000000000000 : ℝ) (33432110546769 / 1000000000000000 : ℝ)
    (cell12691 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · have h := gap_lower (n := 12691) (a := (2583191012569 / 3125000000000 : ℝ)) (b := (81152887931 / 50000000000000 : ℝ)) (q := (1126369742421 / 50000000000000 : ℝ))
      (E := (cell12691 ⟨41, by decide⟩).energy) (xi := (33432110546769 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12691 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12691]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12691])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12691) (a := (2583191012569 / 3125000000000 : ℝ)) (b := (81152887931 / 50000000000000 : ℝ)) (q := (1126369742421 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12691])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12691])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12691]

theorem cert12691_42 : CellCertificate 12691 (443471074657813 / 5000000000000000 : ℝ) (66202611617421 / 40000000000000000 : ℝ) (33432110546769 / 1000000000000000 : ℝ)
    (cell12691 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · have h := gap_lower (n := 12691) (a := (41314064493131 / 50000000000000 : ℝ)) (b := (81152887931 / 50000000000000 : ℝ)) (q := (563185870703 / 25000000000000 : ℝ))
      (E := (cell12691 ⟨42, by decide⟩).energy) (xi := (33432110546769 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12691 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12691]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12691])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12691) (a := (41314064493131 / 50000000000000 : ℝ)) (b := (81152887931 / 50000000000000 : ℝ)) (q := (563185870703 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12691])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12691])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12691]

theorem cert12691_43 : CellCertificate 12691 (443471074657813 / 5000000000000000 : ℝ) (66202611617421 / 40000000000000000 : ℝ) (33432110546769 / 1000000000000000 : ℝ)
    (cell12691 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · have h := gap_lower (n := 12691) (a := (82594169157091 / 100000000000000 : ℝ)) (b := (81152887931 / 50000000000000 : ℝ)) (q := (1126373742191 / 50000000000000 : ℝ))
      (E := (cell12691 ⟨43, by decide⟩).energy) (xi := (33432110546769 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12691 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12691]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12691])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12691) (a := (82594169157091 / 100000000000000 : ℝ)) (b := (81152887931 / 50000000000000 : ℝ)) (q := (1126373742191 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12691])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12691])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12691]

theorem cert12691_44 : CellCertificate 12691 (443471074657813 / 5000000000000000 : ℝ) (66202611617421 / 40000000000000000 : ℝ) (33432110546769 / 1000000000000000 : ℝ)
    (cell12691 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · have h := gap_lower (n := 12691) (a := (82560232885147 / 100000000000000 : ℝ)) (b := (81152887931 / 50000000000000 : ℝ)) (q := (2252751488539 / 100000000000000 : ℝ))
      (E := (cell12691 ⟨44, by decide⟩).energy) (xi := (33432110546769 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12691 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12691]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12691])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12691) (a := (82560232885147 / 100000000000000 : ℝ)) (b := (81152887931 / 50000000000000 : ℝ)) (q := (2252751488539 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12691])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12691])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12691]

theorem cert12691_45 : CellCertificate 12691 (443471074657813 / 5000000000000000 : ℝ) (66202611617421 / 40000000000000000 : ℝ) (33432110546769 / 1000000000000000 : ℝ)
    (cell12691 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · have h := gap_lower (n := 12691) (a := (82526320141029 / 100000000000000 : ℝ)) (b := (81152887931 / 50000000000000 : ℝ)) (q := (281594436757 / 12500000000000 : ℝ))
      (E := (cell12691 ⟨45, by decide⟩).energy) (xi := (33432110546769 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12691 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12691]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12691])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12691) (a := (82526320141029 / 100000000000000 : ℝ)) (b := (81152887931 / 50000000000000 : ℝ)) (q := (281594436757 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12691])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12691])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12691]

theorem cert12691_46 : CellCertificate 12691 (443471074657813 / 5000000000000000 : ℝ) (66202611617421 / 40000000000000000 : ℝ) (33432110546769 / 1000000000000000 : ℝ)
    (cell12691 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · have h := gap_lower (n := 12691) (a := (41246215447743 / 50000000000000 : ℝ)) (b := (81152887931 / 50000000000000 : ℝ)) (q := (563189874871 / 25000000000000 : ℝ))
      (E := (cell12691 ⟨46, by decide⟩).energy) (xi := (33432110546769 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12691 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12691]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12691])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12691) (a := (41246215447743 / 50000000000000 : ℝ)) (b := (81152887931 / 50000000000000 : ℝ)) (q := (563189874871 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12691])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12691])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12691]

theorem cert12691_47 : CellCertificate 12691 (443471074657813 / 5000000000000000 : ℝ) (66202611617421 / 40000000000000000 : ℝ) (33432110546769 / 1000000000000000 : ℝ)
    (cell12691 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · have h := gap_lower (n := 12691) (a := (82458565119413 / 100000000000000 : ℝ)) (b := (81152887931 / 50000000000000 : ℝ)) (q := (563190875791 / 25000000000000 : ℝ))
      (E := (cell12691 ⟨47, by decide⟩).energy) (xi := (33432110546769 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12691 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12691]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12691])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12691) (a := (82458565119413 / 100000000000000 : ℝ)) (b := (81152887931 / 50000000000000 : ℝ)) (q := (563190875791 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12691])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12691])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12691]

theorem cert12691_48 : CellCertificate 12691 (443471074657813 / 5000000000000000 : ℝ) (66202611617421 / 40000000000000000 : ℝ) (33432110546769 / 1000000000000000 : ℝ)
    (cell12691 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · have h := gap_lower (n := 12691) (a := (82424722783853 / 100000000000000 : ℝ)) (b := (81152887931 / 50000000000000 : ℝ)) (q := (2252767503217 / 100000000000000 : ℝ))
      (E := (cell12691 ⟨48, by decide⟩).energy) (xi := (33432110546769 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12691 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12691]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12691])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12691) (a := (82424722783853 / 100000000000000 : ℝ)) (b := (81152887931 / 50000000000000 : ℝ)) (q := (2252767503217 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12691])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12691])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12691]

theorem cert12691_49 : CellCertificate 12691 (443471074657813 / 5000000000000000 : ℝ) (66202611617421 / 40000000000000000 : ℝ) (33432110546769 / 1000000000000000 : ℝ)
    (cell12691 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · have h := gap_lower (n := 12691) (a := (10298862982499 / 12500000000000 : ℝ)) (b := (81152887931 / 50000000000000 : ℝ)) (q := (70399111141 / 3125000000000 : ℝ))
      (E := (cell12691 ⟨49, by decide⟩).energy) (xi := (33432110546769 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12691 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12691]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12691])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12691) (a := (10298862982499 / 12500000000000 : ℝ)) (b := (81152887931 / 50000000000000 : ℝ)) (q := (70399111141 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12691])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12691])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12691]

theorem cert12691_50 : CellCertificate 12691 (443471074657813 / 5000000000000000 : ℝ) (66202611617421 / 40000000000000000 : ℝ) (33432110546769 / 1000000000000000 : ℝ)
    (cell12691 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · have h := gap_lower (n := 12691) (a := (41178554159581 / 50000000000000 : ℝ)) (b := (81152887931 / 50000000000000 : ℝ)) (q := (2252775542851 / 100000000000000 : ℝ))
      (E := (cell12691 ⟨50, by decide⟩).energy) (xi := (33432110546769 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12691 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12691]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12691])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12691) (a := (41178554159581 / 50000000000000 : ℝ)) (b := (81152887931 / 50000000000000 : ℝ)) (q := (2252775542851 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12691])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12691])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12691]

theorem cert12691_51 : CellCertificate 12691 (443471074657813 / 5000000000000000 : ℝ) (66202611617421 / 40000000000000000 : ℝ) (33432110546769 / 1000000000000000 : ℝ)
    (cell12691 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · have h := gap_lower (n := 12691) (a := (82323336132837 / 100000000000000 : ℝ)) (b := (81152887931 / 50000000000000 : ℝ)) (q := (450555903731 / 20000000000000 : ℝ))
      (E := (cell12691 ⟨51, by decide⟩).energy) (xi := (33432110546769 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12691 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12691]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12691])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12691) (a := (82323336132837 / 100000000000000 : ℝ)) (b := (81152887931 / 50000000000000 : ℝ)) (q := (450555903731 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12691])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12691])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12691]

theorem cert12691_52 : CellCertificate 12691 (443471074657813 / 5000000000000000 : ℝ) (66202611617421 / 40000000000000000 : ℝ) (33432110546769 / 1000000000000000 : ℝ)
    (cell12691 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · have h := gap_lower (n := 12691) (a := (82289587272637 / 100000000000000 : ℝ)) (b := (81152887931 / 50000000000000 : ℝ)) (q := (2252783540223 / 100000000000000 : ℝ))
      (E := (cell12691 ⟨52, by decide⟩).energy) (xi := (33432110546769 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12691 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12691]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12691])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12691) (a := (82289587272637 / 100000000000000 : ℝ)) (b := (81152887931 / 50000000000000 : ℝ)) (q := (2252783540223 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12691])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12691])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12691]

theorem cert12691_53 : CellCertificate 12691 (443471074657813 / 5000000000000000 : ℝ) (66202611617421 / 40000000000000000 : ℝ) (33432110546769 / 1000000000000000 : ℝ)
    (cell12691 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · have h := gap_lower (n := 12691) (a := (1028198271379 / 1250000000000 : ℝ)) (b := (81152887931 / 50000000000000 : ℝ)) (q := (450557509127 / 20000000000000 : ℝ))
      (E := (cell12691 ⟨53, by decide⟩).energy) (xi := (33432110546769 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12691 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12691]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12691])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12691) (a := (1028198271379 / 1250000000000 : ℝ)) (b := (81152887931 / 50000000000000 : ℝ)) (q := (450557509127 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12691])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12691])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12691]

theorem cert12691_54 : CellCertificate 12691 (443471074657813 / 5000000000000000 : ℝ) (66202611617421 / 40000000000000000 : ℝ) (33432110546769 / 1000000000000000 : ℝ)
    (cell12691 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · have h := gap_lower (n := 12691) (a := (82222159417789 / 100000000000000 : ℝ)) (b := (81152887931 / 50000000000000 : ℝ)) (q := (2252791590817 / 100000000000000 : ℝ))
      (E := (cell12691 ⟨54, by decide⟩).energy) (xi := (33432110546769 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12691 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12691]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12691])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12691) (a := (82222159417789 / 100000000000000 : ℝ)) (b := (81152887931 / 50000000000000 : ℝ)) (q := (2252791590817 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12691])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12691])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12691]

theorem cert12691_55 : CellCertificate 12691 (443471074657813 / 5000000000000000 : ℝ) (66202611617421 / 40000000000000000 : ℝ) (33432110546769 / 1000000000000000 : ℝ)
    (cell12691 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · have h := gap_lower (n := 12691) (a := (16437696073417 / 20000000000000 : ℝ)) (b := (81152887931 / 50000000000000 : ℝ)) (q := (2252795554283 / 100000000000000 : ℝ))
      (E := (cell12691 ⟨55, by decide⟩).energy) (xi := (33432110546769 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12691 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12691]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12691])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12691) (a := (16437696073417 / 20000000000000 : ℝ)) (b := (81152887931 / 50000000000000 : ℝ)) (q := (2252795554283 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12691])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12691])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12691]

theorem cert12691_56 : CellCertificate 12691 (443471074657813 / 5000000000000000 : ℝ) (66202611617421 / 40000000000000000 : ℝ) (33432110546769 / 1000000000000000 : ℝ)
    (cell12691 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · have h := gap_lower (n := 12691) (a := (8215482453039 / 10000000000000 : ℝ)) (b := (81152887931 / 50000000000000 : ℝ)) (q := (1126399775321 / 50000000000000 : ℝ))
      (E := (cell12691 ⟨56, by decide⟩).energy) (xi := (33432110546769 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12691 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12691]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12691])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12691) (a := (8215482453039 / 10000000000000 : ℝ)) (b := (81152887931 / 50000000000000 : ℝ)) (q := (1126399775321 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12691])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12691])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12691]

theorem cert12691_57 : CellCertificate 12691 (443471074657813 / 5000000000000000 : ℝ) (66202611617421 / 40000000000000000 : ℝ) (33432110546769 / 1000000000000000 : ℝ)
    (cell12691 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · have h := gap_lower (n := 12691) (a := (82121191880023 / 100000000000000 : ℝ)) (b := (81152887931 / 50000000000000 : ℝ)) (q := (2252803576189 / 100000000000000 : ℝ))
      (E := (cell12691 ⟨57, by decide⟩).energy) (xi := (33432110546769 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12691 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12691]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12691])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12691) (a := (82121191880023 / 100000000000000 : ℝ)) (b := (81152887931 / 50000000000000 : ℝ)) (q := (2252803576189 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12691])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12691])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12691]

theorem cert12691_58 : CellCertificate 12691 (443471074657813 / 5000000000000000 : ℝ) (66202611617421 / 40000000000000000 : ℝ) (33432110546769 / 1000000000000000 : ℝ)
    (cell12691 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · have h := gap_lower (n := 12691) (a := (41043791194221 / 50000000000000 : ℝ)) (b := (81152887931 / 50000000000000 : ℝ)) (q := (563201891961 / 25000000000000 : ℝ))
      (E := (cell12691 ⟨58, by decide⟩).energy) (xi := (33432110546769 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12691 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12691]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12691])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12691) (a := (41043791194221 / 50000000000000 : ℝ)) (b := (81152887931 / 50000000000000 : ℝ)) (q := (563201891961 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12691])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12691])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12691]

theorem cert12691_59 : CellCertificate 12691 (443471074657813 / 5000000000000000 : ℝ) (66202611617421 / 40000000000000000 : ℝ) (33432110546769 / 1000000000000000 : ℝ)
    (cell12691 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · have h := gap_lower (n := 12691) (a := (82053996028243 / 100000000000000 : ℝ)) (b := (81152887931 / 50000000000000 : ℝ)) (q := (225281158061 / 10000000000000 : ℝ))
      (E := (cell12691 ⟨59, by decide⟩).energy) (xi := (33432110546769 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12691 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12691]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12691])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12691) (a := (82053996028243 / 100000000000000 : ℝ)) (b := (81152887931 / 50000000000000 : ℝ)) (q := (225281158061 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12691])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12691])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12691]

theorem cert12692_40 : CellCertificate 12692 (886914176637767 / 10000000000000000 : ℝ) (1654934845288667 / 1000000000000000000 : ℝ) (33429412079327 / 1000000000000000 : ℝ)
    (cell12692 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · have h := gap_lower (n := 12692) (a := (3307844670273 / 4000000000000 : ℝ)) (b := (162292831601 / 100000000000000 : ℝ)) (q := (2252612470999 / 100000000000000 : ℝ))
      (E := (cell12692 ⟨40, by decide⟩).energy) (xi := (33429412079327 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12692 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12692]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12692])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12692) (a := (3307844670273 / 4000000000000 : ℝ)) (b := (162292831601 / 100000000000000 : ℝ)) (q := (2252612470999 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12692])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12692])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12692]

theorem cert12692_41 : CellCertificate 12692 (886914176637767 / 10000000000000000 : ℝ) (1654934845288667 / 1000000000000000000 : ℝ) (33429412079327 / 1000000000000000 : ℝ)
    (cell12692 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · have h := gap_lower (n := 12692) (a := (16532422005479 / 20000000000000 : ℝ)) (b := (162292831601 / 100000000000000 : ℝ)) (q := (563154114699 / 25000000000000 : ℝ))
      (E := (cell12692 ⟨41, by decide⟩).energy) (xi := (33429412079327 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12692 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12692]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12692])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12692) (a := (16532422005479 / 20000000000000 : ℝ)) (b := (162292831601 / 100000000000000 : ℝ)) (q := (563154114699 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12692])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12692])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12692]

theorem cert12692_42 : CellCertificate 12692 (886914176637767 / 10000000000000000 : ℝ) (1654934845288667 / 1000000000000000000 : ℝ) (33429412079327 / 1000000000000000 : ℝ)
    (cell12692 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · have h := gap_lower (n := 12692) (a := (82628126914019 / 100000000000000 : ℝ)) (b := (162292831601 / 100000000000000 : ℝ)) (q := (563155127619 / 25000000000000 : ℝ))
      (E := (cell12692 ⟨42, by decide⟩).energy) (xi := (33429412079327 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12692 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12692]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12692])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12692) (a := (82628126914019 / 100000000000000 : ℝ)) (b := (162292831601 / 100000000000000 : ℝ)) (q := (563155127619 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12692])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12692])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12692]

theorem cert12692_43 : CellCertificate 12692 (886914176637767 / 10000000000000000 : ℝ) (1654934845288667 / 1000000000000000000 : ℝ) (33429412079327 / 1000000000000000 : ℝ)
    (cell12692 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · have h := gap_lower (n := 12692) (a := (82594167387001 / 100000000000000 : ℝ)) (b := (162292831601 / 100000000000000 : ℝ)) (q := (1126312253839 / 50000000000000 : ℝ))
      (E := (cell12692 ⟨43, by decide⟩).energy) (xi := (33429412079327 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12692 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12692]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12692])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12692) (a := (82594167387001 / 100000000000000 : ℝ)) (b := (162292831601 / 100000000000000 : ℝ)) (q := (1126312253839 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12692])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12692])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12692]

theorem cert12692_44 : CellCertificate 12692 (886914176637767 / 10000000000000000 : ℝ) (1654934845288667 / 1000000000000000000 : ℝ) (33429412079327 / 1000000000000000 : ℝ)
    (cell12692 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · have h := gap_lower (n := 12692) (a := (10320028927099 / 12500000000000 : ℝ)) (b := (162292831601 / 100000000000000 : ℝ)) (q := (1126314254081 / 50000000000000 : ℝ))
      (E := (cell12692 ⟨44, by decide⟩).energy) (xi := (33429412079327 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12692 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12692]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12692])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12692) (a := (10320028927099 / 12500000000000 : ℝ)) (b := (162292831601 / 100000000000000 : ℝ)) (q := (1126314254081 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12692])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12692])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12692]

theorem cert12692_45 : CellCertificate 12692 (886914176637767 / 10000000000000000 : ℝ) (1654934845288667 / 1000000000000000000 : ℝ) (33429412079327 / 1000000000000000 : ℝ)
    (cell12692 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · have h := gap_lower (n := 12692) (a := (41263159486997 / 50000000000000 : ℝ)) (b := (162292831601 / 100000000000000 : ℝ)) (q := (281579063837 / 12500000000000 : ℝ))
      (E := (cell12692 ⟨45, by decide⟩).energy) (xi := (33429412079327 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12692 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12692]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12692])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12692) (a := (41263159486997 / 50000000000000 : ℝ)) (b := (162292831601 / 100000000000000 : ℝ)) (q := (281579063837 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12692])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12692])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12692]

theorem cert12692_46 : CellCertificate 12692 (886914176637767 / 10000000000000000 : ℝ) (1654934845288667 / 1000000000000000000 : ℝ) (33429412079327 / 1000000000000000 : ℝ)
    (cell12692 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · have h := gap_lower (n := 12692) (a := (20623107507339 / 25000000000000 : ℝ)) (b := (162292831601 / 100000000000000 : ℝ)) (q := (1126318256917 / 50000000000000 : ℝ))
      (E := (cell12692 ⟨46, by decide⟩).energy) (xi := (33429412079327 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12692 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12692]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12692])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12692) (a := (20623107507339 / 25000000000000 : ℝ)) (b := (162292831601 / 100000000000000 : ℝ)) (q := (1126318256917 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12692])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12692])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12692]

theorem cert12692_47 : CellCertificate 12692 (886914176637767 / 10000000000000000 : ℝ) (1654934845288667 / 1000000000000000000 : ℝ) (33429412079327 / 1000000000000000 : ℝ)
    (cell12692 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · have h := gap_lower (n := 12692) (a := (3298342582151 / 4000000000000 : ℝ)) (b := (162292831601 / 100000000000000 : ℝ)) (q := (281580064489 / 12500000000000 : ℝ))
      (E := (cell12692 ⟨47, by decide⟩).energy) (xi := (33429412079327 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12692 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12692]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12692])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12692) (a := (3298342582151 / 4000000000000 : ℝ)) (b := (162292831601 / 100000000000000 : ℝ)) (q := (281580064489 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12692])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12692])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12692]

theorem cert12692_48 : CellCertificate 12692 (886914176637767 / 10000000000000000 : ℝ) (1654934845288667 / 1000000000000000000 : ℝ) (33429412079327 / 1000000000000000 : ℝ)
    (cell12692 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · have h := gap_lower (n := 12692) (a := (82424722518291 / 100000000000000 : ℝ)) (b := (162292831601 / 100000000000000 : ℝ)) (q := (450528903011 / 20000000000000 : ℝ))
      (E := (cell12692 ⟨48, by decide⟩).energy) (xi := (33429412079327 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12692 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12692]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12692])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12692) (a := (82424722518291 / 100000000000000 : ℝ)) (b := (162292831601 / 100000000000000 : ℝ)) (q := (450528903011 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12692])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12692])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12692]

theorem cert12692_49 : CellCertificate 12692 (886914176637767 / 10000000000000000 : ℝ) (1654934845288667 / 1000000000000000000 : ℝ) (33429412079327 / 1000000000000000 : ℝ)
    (cell12692 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · have h := gap_lower (n := 12692) (a := (41195451947047 / 50000000000000 : ℝ)) (b := (162292831601 / 100000000000000 : ℝ)) (q := (225264850917 / 10000000000000 : ℝ))
      (E := (cell12692 ⟨49, by decide⟩).energy) (xi := (33429412079327 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12692 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12692]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12692])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12692) (a := (41195451947047 / 50000000000000 : ℝ)) (b := (162292831601 / 100000000000000 : ℝ)) (q := (225264850917 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12692])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12692])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12692]

theorem cert12692_50 : CellCertificate 12692 (886914176637767 / 10000000000000000 : ℝ) (1654934845288667 / 1000000000000000000 : ℝ) (33429412079327 / 1000000000000000 : ℝ)
    (cell12692 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · have h := gap_lower (n := 12692) (a := (20589277163129 / 25000000000000 : ℝ)) (b := (162292831601 / 100000000000000 : ℝ)) (q := (2252652495953 / 100000000000000 : ℝ))
      (E := (cell12692 ⟨50, by decide⟩).energy) (xi := (33429412079327 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12692 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12692]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12692])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12692) (a := (20589277163129 / 25000000000000 : ℝ)) (b := (162292831601 / 100000000000000 : ℝ)) (q := (2252652495953 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12692])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12692])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12692]

theorem cert12692_51 : CellCertificate 12692 (886914176637767 / 10000000000000000 : ℝ) (1654934845288667 / 1000000000000000000 : ℝ) (33429412079327 / 1000000000000000 : ℝ)
    (cell12692 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · have h := gap_lower (n := 12692) (a := (10290417095629 / 12500000000000 : ℝ)) (b := (162292831601 / 100000000000000 : ℝ)) (q := (2252656531893 / 100000000000000 : ℝ))
      (E := (cell12692 ⟨51, by decide⟩).energy) (xi := (33429412079327 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12692 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12692]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12692])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12692) (a := (10290417095629 / 12500000000000 : ℝ)) (b := (162292831601 / 100000000000000 : ℝ)) (q := (2252656531893 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12692])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12692])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12692]

theorem cert12692_52 : CellCertificate 12692 (886914176637767 / 10000000000000000 : ℝ) (1654934845288667 / 1000000000000000000 : ℝ) (33429412079327 / 1000000000000000 : ℝ)
    (cell12692 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · have h := gap_lower (n := 12692) (a := (41144794101631 / 50000000000000 : ℝ)) (b := (162292831601 / 100000000000000 : ℝ)) (q := (1126330277651 / 50000000000000 : ℝ))
      (E := (cell12692 ⟨52, by decide⟩).energy) (xi := (33429412079327 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12692 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12692]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12692])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12692) (a := (41144794101631 / 50000000000000 : ℝ)) (b := (162292831601 / 100000000000000 : ℝ)) (q := (1126330277651 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12692])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12692])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12692]

theorem cert12692_53 : CellCertificate 12692 (886914176637767 / 10000000000000000 : ℝ) (1654934845288667 / 1000000000000000000 : ℝ) (33429412079327 / 1000000000000000 : ℝ)
    (cell12692 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · have h := gap_lower (n := 12692) (a := (16451172587793 / 20000000000000 : ℝ)) (b := (162292831601 / 100000000000000 : ℝ)) (q := (1126332281621 / 50000000000000 : ℝ))
      (E := (cell12692 ⟨53, by decide⟩).energy) (xi := (33429412079327 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12692 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12692]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12692])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12692) (a := (16451172587793 / 20000000000000 : ℝ)) (b := (162292831601 / 100000000000000 : ℝ)) (q := (1126332281621 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12692])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12692])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12692]

theorem cert12692_54 : CellCertificate 12692 (886914176637767 / 10000000000000000 : ℝ) (1654934845288667 / 1000000000000000000 : ℝ) (33429412079327 / 1000000000000000 : ℝ)
    (cell12692 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · have h := gap_lower (n := 12692) (a := (16444432188809 / 20000000000000 : ℝ)) (b := (162292831601 / 100000000000000 : ℝ)) (q := (2252668552561 / 100000000000000 : ℝ))
      (E := (cell12692 ⟨54, by decide⟩).energy) (xi := (33429412079327 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12692 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12692]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12692])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12692) (a := (16444432188809 / 20000000000000 : ℝ)) (b := (162292831601 / 100000000000000 : ℝ)) (q := (2252668552561 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12692])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12692])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12692]

theorem cert12692_55 : CellCertificate 12692 (886914176637767 / 10000000000000000 : ℝ) (1654934845288667 / 1000000000000000000 : ℝ) (33429412079327 / 1000000000000000 : ℝ)
    (cell12692 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · have h := gap_lower (n := 12692) (a := (82188482190543 / 100000000000000 : ℝ)) (b := (162292831601 / 100000000000000 : ℝ)) (q := (1126336289501 / 50000000000000 : ℝ))
      (E := (cell12692 ⟨55, by decide⟩).energy) (xi := (33429412079327 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12692 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12692]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12692])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12692) (a := (82188482190543 / 100000000000000 : ℝ)) (b := (162292831601 / 100000000000000 : ℝ)) (q := (1126336289501 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12692])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12692])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12692]

theorem cert12692_56 : CellCertificate 12692 (886914176637767 / 10000000000000000 : ℝ) (1654934845288667 / 1000000000000000000 : ℝ) (33429412079327 / 1000000000000000 : ℝ)
    (cell12692 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · have h := gap_lower (n := 12692) (a := (82154826650641 / 100000000000000 : ℝ)) (b := (162292831601 / 100000000000000 : ℝ)) (q := (450535315989 / 20000000000000 : ℝ))
      (E := (cell12692 ⟨56, by decide⟩).energy) (xi := (33429412079327 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12692 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12692]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12692])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12692) (a := (82154826650641 / 100000000000000 : ℝ)) (b := (162292831601 / 100000000000000 : ℝ)) (q := (450535315989 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12692])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12692])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12692]

theorem cert12692_57 : CellCertificate 12692 (886914176637767 / 10000000000000000 : ℝ) (1654934845288667 / 1000000000000000000 : ℝ) (33429412079327 / 1000000000000000 : ℝ)
    (cell12692 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · have h := gap_lower (n := 12692) (a := (82121194296661 / 100000000000000 : ℝ)) (b := (162292831601 / 100000000000000 : ℝ)) (q := (2252680551613 / 100000000000000 : ℝ))
      (E := (cell12692 ⟨57, by decide⟩).energy) (xi := (33429412079327 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12692 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12692]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12692])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12692) (a := (82121194296661 / 100000000000000 : ℝ)) (b := (162292831601 / 100000000000000 : ℝ)) (q := (2252680551613 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12692])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12692])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12692]

theorem cert12692_58 : CellCertificate 12692 (886914176637767 / 10000000000000000 : ℝ) (1654934845288667 / 1000000000000000000 : ℝ) (33429412079327 / 1000000000000000 : ℝ)
    (cell12692 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · have h := gap_lower (n := 12692) (a := (82087585101061 / 100000000000000 : ℝ)) (b := (162292831601 / 100000000000000 : ℝ)) (q := (1126342274597 / 50000000000000 : ℝ))
      (E := (cell12692 ⟨58, by decide⟩).energy) (xi := (33429412079327 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12692 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12692]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12692])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12692) (a := (82087585101061 / 100000000000000 : ℝ)) (b := (162292831601 / 100000000000000 : ℝ)) (q := (1126342274597 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12692])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12692])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12692]

theorem cert12692_59 : CellCertificate 12692 (886914176637767 / 10000000000000000 : ℝ) (1654934845288667 / 1000000000000000000 : ℝ) (33429412079327 / 1000000000000000 : ℝ)
    (cell12692 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · have h := gap_lower (n := 12692) (a := (20513499759109 / 25000000000000 : ℝ)) (b := (162292831601 / 100000000000000 : ℝ)) (q := (225268856857 / 10000000000000 : ℝ))
      (E := (cell12692 ⟨59, by decide⟩).energy) (xi := (33429412079327 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12692 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12692]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12692])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12692) (a := (20513499759109 / 25000000000000 : ℝ)) (b := (162292831601 / 100000000000000 : ℝ)) (q := (225268856857 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12692])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12692])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12692]

theorem cert12693_40 : CellCertificate 12693 (886886208192159 / 10000000000000000 : ℝ) (1654804420702439 / 1000000000000000000 : ℝ) (334267140535667 / 10000000000000000 : ℝ)
    (cell12693 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · have h := gap_lower (n := 12693) (a := (41348057039949 / 50000000000000 : ℝ)) (b := (162279889419 / 100000000000000 : ℝ)) (q := (2252489506299 / 100000000000000 : ℝ))
      (E := (cell12693 ⟨40, by decide⟩).energy) (xi := (334267140535667 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12693 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12693]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12693])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12693) (a := (41348057039949 / 50000000000000 : ℝ)) (b := (162279889419 / 100000000000000 : ℝ)) (q := (2252489506299 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12693])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12693])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12693]

theorem cert12693_41 : CellCertificate 12693 (886886208192159 / 10000000000000000 : ℝ) (1654804420702439 / 1000000000000000000 : ℝ) (334267140535667 / 10000000000000000 : ℝ)
    (cell12693 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · have h := gap_lower (n := 12693) (a := (82662107653419 / 100000000000000 : ℝ)) (b := (162279889419 / 100000000000000 : ℝ)) (q := (2252493488379 / 100000000000000 : ℝ))
      (E := (cell12693 ⟨41, by decide⟩).energy) (xi := (334267140535667 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12693 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12693]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12693])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12693) (a := (82662107653419 / 100000000000000 : ℝ)) (b := (162279889419 / 100000000000000 : ℝ)) (q := (2252493488379 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12693])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12693])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12693]

theorem cert12693_42 : CellCertificate 12693 (886886208192159 / 10000000000000000 : ℝ) (1654804420702439 / 1000000000000000000 : ℝ) (334267140535667 / 10000000000000000 : ℝ)
    (cell12693 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · have h := gap_lower (n := 12693) (a := (82628124842577 / 100000000000000 : ℝ)) (b := (162279889419 / 100000000000000 : ℝ)) (q := (1126248738121 / 50000000000000 : ℝ))
      (E := (cell12693 ⟨42, by decide⟩).energy) (xi := (334267140535667 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12693 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12693]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12693])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12693) (a := (82628124842577 / 100000000000000 : ℝ)) (b := (162279889419 / 100000000000000 : ℝ)) (q := (1126248738121 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12693])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12693])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12693]

theorem cert12693_43 : CellCertificate 12693 (886886208192159 / 10000000000000000 : ℝ) (1654804420702439 / 1000000000000000000 : ℝ) (334267140535667 / 10000000000000000 : ℝ)
    (cell12693 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · have h := gap_lower (n := 12693) (a := (3303766624707 / 4000000000000 : ℝ)) (b := (162279889419 / 100000000000000 : ℝ)) (q := (2252501527909 / 100000000000000 : ℝ))
      (E := (cell12693 ⟨43, by decide⟩).energy) (xi := (334267140535667 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12693 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12693]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12693])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12693) (a := (3303766624707 / 4000000000000 : ℝ)) (b := (162279889419 / 100000000000000 : ℝ)) (q := (2252501527909 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12693])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12693])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12693]

theorem cert12693_44 : CellCertificate 12693 (886886208192159 / 10000000000000000 : ℝ) (1654804420702439 / 1000000000000000000 : ℝ) (334267140535667 / 10000000000000000 : ℝ)
    (cell12693 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · have h := gap_lower (n := 12693) (a := (16512045989833 / 20000000000000 : ℝ)) (b := (162279889419 / 100000000000000 : ℝ)) (q := (563126381189 / 25000000000000 : ℝ))
      (E := (cell12693 ⟨44, by decide⟩).energy) (xi := (334267140535667 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12693 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12693]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12693])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12693) (a := (16512045989833 / 20000000000000 : ℝ)) (b := (162279889419 / 100000000000000 : ℝ)) (q := (563126381189 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12693])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12693])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12693]

theorem cert12693_45 : CellCertificate 12693 (886886208192159 / 10000000000000000 : ℝ) (1654804420702439 / 1000000000000000000 : ℝ) (334267140535667 / 10000000000000000 : ℝ)
    (cell12693 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · have h := gap_lower (n := 12693) (a := (82526317807651 / 100000000000000 : ℝ)) (b := (162279889419 / 100000000000000 : ℝ)) (q := (450501904869 / 20000000000000 : ℝ))
      (E := (cell12693 ⟨45, by decide⟩).energy) (xi := (334267140535667 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12693 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12693]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12693])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12693) (a := (82526317807651 / 100000000000000 : ℝ)) (b := (162279889419 / 100000000000000 : ℝ)) (q := (450501904869 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12693])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12693])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12693]

theorem cert12693_46 : CellCertificate 12693 (886886208192159 / 10000000000000000 : ℝ) (1654804420702439 / 1000000000000000000 : ℝ) (334267140535667 / 10000000000000000 : ℝ)
    (cell12693 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · have h := gap_lower (n := 12693) (a := (41246214581941 / 50000000000000 : ℝ)) (b := (162279889419 / 100000000000000 : ℝ)) (q := (563128381307 / 25000000000000 : ℝ))
      (E := (cell12693 ⟨46, by decide⟩).energy) (xi := (334267140535667 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12693 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12693]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12693])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12693) (a := (41246214581941 / 50000000000000 : ℝ)) (b := (162279889419 / 100000000000000 : ℝ)) (q := (563128381307 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12693])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12693])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12693]

theorem cert12693_47 : CellCertificate 12693 (886886208192159 / 10000000000000000 : ℝ) (1654804420702439 / 1000000000000000000 : ℝ) (334267140535667 / 10000000000000000 : ℝ)
    (cell12693 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · have h := gap_lower (n := 12693) (a := (41229281994377 / 50000000000000 : ℝ)) (b := (162279889419 / 100000000000000 : ℝ)) (q := (140782345359 / 6250000000000 : ℝ))
      (E := (cell12693 ⟨47, by decide⟩).energy) (xi := (334267140535667 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12693 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12693]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12693])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12693) (a := (41229281994377 / 50000000000000 : ℝ)) (b := (162279889419 / 100000000000000 : ℝ)) (q := (140782345359 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12693])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12693])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12693]

theorem cert12693_48 : CellCertificate 12693 (886886208192159 / 10000000000000000 : ℝ) (1654804420702439 / 1000000000000000000 : ℝ) (334267140535667 / 10000000000000000 : ℝ)
    (cell12693 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · have h := gap_lower (n := 12693) (a := (160985785651 / 195312500000 : ℝ)) (b := (162279889419 / 100000000000000 : ℝ)) (q := (563130381003 / 25000000000000 : ℝ))
      (E := (cell12693 ⟨48, by decide⟩).energy) (xi := (334267140535667 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12693 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12693]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12693])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12693) (a := (160985785651 / 195312500000 : ℝ)) (b := (162279889419 / 100000000000000 : ℝ)) (q := (563130381003 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12693])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12693])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12693]

theorem cert12693_49 : CellCertificate 12693 (886886208192159 / 10000000000000000 : ℝ) (1654804420702439 / 1000000000000000000 : ℝ) (334267140535667 / 10000000000000000 : ℝ)
    (cell12693 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · have h := gap_lower (n := 12693) (a := (82390903928743 / 100000000000000 : ℝ)) (b := (162279889419 / 100000000000000 : ℝ)) (q := (2252525517943 / 100000000000000 : ℝ))
      (E := (cell12693 ⟨49, by decide⟩).energy) (xi := (334267140535667 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12693 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12693]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12693])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12693) (a := (82390903928743 / 100000000000000 : ℝ)) (b := (162279889419 / 100000000000000 : ℝ)) (q := (2252525517943 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12693])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12693])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12693]

theorem cert12693_50 : CellCertificate 12693 (886886208192159 / 10000000000000000 : ℝ) (1654804420702439 / 1000000000000000000 : ℝ) (334267140535667 / 10000000000000000 : ℝ)
    (cell12693 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · have h := gap_lower (n := 12693) (a := (4117855449319 / 5000000000000 : ℝ)) (b := (162279889419 / 100000000000000 : ℝ)) (q := (563132391053 / 25000000000000 : ℝ))
      (E := (cell12693 ⟨50, by decide⟩).energy) (xi := (334267140535667 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12693 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12693]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12693])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12693) (a := (4117855449319 / 5000000000000 : ℝ)) (b := (162279889419 / 100000000000000 : ℝ)) (q := (563132391053 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12693])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12693])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12693]

theorem cert12693_51 : CellCertificate 12693 (886886208192159 / 10000000000000000 : ℝ) (1654804420702439 / 1000000000000000000 : ℝ) (334267140535667 / 10000000000000000 : ℝ)
    (cell12693 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · have h := gap_lower (n := 12693) (a := (82323337397701 / 100000000000000 : ℝ)) (b := (162279889419 / 100000000000000 : ℝ)) (q := (2252533542361 / 100000000000000 : ℝ))
      (E := (cell12693 ⟨51, by decide⟩).energy) (xi := (334267140535667 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12693 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12693]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12693])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12693) (a := (82323337397701 / 100000000000000 : ℝ)) (b := (162279889419 / 100000000000000 : ℝ)) (q := (2252533542361 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12693])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12693])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12693]

theorem cert12693_52 : CellCertificate 12693 (886886208192159 / 10000000000000000 : ℝ) (1654804420702439 / 1000000000000000000 : ℝ) (334267140535667 / 10000000000000000 : ℝ)
    (cell12693 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · have h := gap_lower (n := 12693) (a := (20572397283581 / 25000000000000 : ℝ)) (b := (162279889419 / 100000000000000 : ℝ)) (q := (2252537567649 / 100000000000000 : ℝ))
      (E := (cell12693 ⟨52, by decide⟩).energy) (xi := (334267140535667 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12693 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12693]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12693])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12693) (a := (20572397283581 / 25000000000000 : ℝ)) (b := (162279889419 / 100000000000000 : ℝ)) (q := (2252537567649 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12693])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12693])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12693]

theorem cert12693_53 : CellCertificate 12693 (886886208192159 / 10000000000000000 : ℝ) (1654804420702439 / 1000000000000000000 : ℝ) (334267140535667 / 10000000000000000 : ℝ)
    (cell12693 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · have h := gap_lower (n := 12693) (a := (82255864168011 / 100000000000000 : ℝ)) (b := (162279889419 / 100000000000000 : ℝ)) (q := (1126270789077 / 50000000000000 : ℝ))
      (E := (cell12693 ⟨53, by decide⟩).energy) (xi := (334267140535667 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12693 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12693]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12693])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12693) (a := (82255864168011 / 100000000000000 : ℝ)) (b := (162279889419 / 100000000000000 : ℝ)) (q := (1126270789077 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12693])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12693])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12693]

theorem cert12693_54 : CellCertificate 12693 (886886208192159 / 10000000000000000 : ℝ) (1654804420702439 / 1000000000000000000 : ℝ) (334267140535667 / 10000000000000000 : ℝ)
    (cell12693 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · have h := gap_lower (n := 12693) (a := (16444432494133 / 20000000000000 : ℝ)) (b := (162279889419 / 100000000000000 : ℝ)) (q := (90101822829 / 4000000000000 : ℝ))
      (E := (cell12693 ⟨54, by decide⟩).energy) (xi := (334267140535667 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12693 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12693]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12693])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12693) (a := (16444432494133 / 20000000000000 : ℝ)) (b := (162279889419 / 100000000000000 : ℝ)) (q := (90101822829 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12693])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12693])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12693]

theorem cert12693_55 : CellCertificate 12693 (886886208192159 / 10000000000000000 : ℝ) (1654804420702439 / 1000000000000000000 : ℝ) (334267140535667 / 10000000000000000 : ℝ)
    (cell12693 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · have h := gap_lower (n := 12693) (a := (82188484014329 / 100000000000000 : ℝ)) (b := (162279889419 / 100000000000000 : ℝ)) (q := (2252549542003 / 100000000000000 : ℝ))
      (E := (cell12693 ⟨55, by decide⟩).energy) (xi := (334267140535667 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12693 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12693]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12693])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12693) (a := (82188484014329 / 100000000000000 : ℝ)) (b := (162279889419 / 100000000000000 : ℝ)) (q := (2252549542003 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12693])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12693])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12693]

theorem cert12693_56 : CellCertificate 12693 (886886208192159 / 10000000000000000 : ℝ) (1654804420702439 / 1000000000000000000 : ℝ) (334267140535667 / 10000000000000000 : ℝ)
    (cell12693 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · have h := gap_lower (n := 12693) (a := (41077414385593 / 50000000000000 : ℝ)) (b := (162279889419 / 100000000000000 : ℝ)) (q := (2252553547541 / 100000000000000 : ℝ))
      (E := (cell12693 ⟨56, by decide⟩).energy) (xi := (334267140535667 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12693 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12693]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12693])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12693) (a := (41077414385593 / 50000000000000 : ℝ)) (b := (162279889419 / 100000000000000 : ℝ)) (q := (2252553547541 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12693])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12693])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12693]

theorem cert12693_57 : CellCertificate 12693 (886886208192159 / 10000000000000000 : ℝ) (1654804420702439 / 1000000000000000000 : ℝ) (334267140535667 / 10000000000000000 : ℝ)
    (cell12693 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · have h := gap_lower (n := 12693) (a := (82121196713557 / 100000000000000 : ℝ)) (b := (162279889419 / 100000000000000 : ℝ)) (q := (450511516727 / 20000000000000 : ℝ))
      (E := (cell12693 ⟨57, by decide⟩).energy) (xi := (334267140535667 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12693 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12693]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12693])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12693) (a := (82121196713557 / 100000000000000 : ℝ)) (b := (162279889419 / 100000000000000 : ℝ)) (q := (450511516727 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12693])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12693])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12693]

theorem cert12693_58 : CellCertificate 12693 (886886208192159 / 10000000000000000 : ℝ) (1654804420702439 / 1000000000000000000 : ℝ) (334267140535667 / 10000000000000000 : ℝ)
    (cell12693 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · have h := gap_lower (n := 12693) (a := (82087587813901 / 100000000000000 : ℝ)) (b := (162279889419 / 100000000000000 : ℝ)) (q := (2252561587203 / 100000000000000 : ℝ))
      (E := (cell12693 ⟨58, by decide⟩).energy) (xi := (334267140535667 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12693 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12693]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12693])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12693) (a := (82087587813901 / 100000000000000 : ℝ)) (b := (162279889419 / 100000000000000 : ℝ)) (q := (2252561587203 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12693])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12693])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12693]

theorem cert12693_59 : CellCertificate 12693 (886886208192159 / 10000000000000000 : ℝ) (1654804420702439 / 1000000000000000000 : ℝ) (334267140535667 / 10000000000000000 : ℝ)
    (cell12693 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · have h := gap_lower (n := 12693) (a := (16410800408963 / 20000000000000 : ℝ)) (b := (162279889419 / 100000000000000 : ℝ)) (q := (2252565613249 / 100000000000000 : ℝ))
      (E := (cell12693 ⟨59, by decide⟩).energy) (xi := (334267140535667 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12693 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12693]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12693])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12693) (a := (16410800408963 / 20000000000000 : ℝ)) (b := (162279889419 / 100000000000000 : ℝ)) (q := (2252565613249 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12693])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12693])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12693]

theorem cert12694_40 : CellCertificate 12694 (443429121988899 / 5000000000000000 : ℝ) (1654674016671983 / 1000000000000000000 : ℝ) (167120082346851 / 5000000000000000 : ℝ)
    (cell12694 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · have h := gap_lower (n := 12694) (a := (41348055701923 / 50000000000000 : ℝ)) (b := (40566737329 / 25000000000000 : ℝ)) (q := (112618326921 / 5000000000000 : ℝ))
      (E := (cell12694 ⟨40, by decide⟩).energy) (xi := (167120082346851 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12694 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12694]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12694])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12694) (a := (41348055701923 / 50000000000000 : ℝ)) (b := (40566737329 / 25000000000000 : ℝ)) (q := (112618326921 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12694])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12694])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12694]

theorem cert12694_41 : CellCertificate 12694 (443429121988899 / 5000000000000000 : ℝ) (1654674016671983 / 1000000000000000000 : ℝ) (167120082346851 / 5000000000000000 : ℝ)
    (cell12694 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · have h := gap_lower (n := 12694) (a := (41331052640141 / 50000000000000 : ℝ)) (b := (40566737329 / 25000000000000 : ℝ)) (q := (2252370573591 / 100000000000000 : ℝ))
      (E := (cell12694 ⟨41, by decide⟩).energy) (xi := (167120082346851 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12694 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12694]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12694])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12694) (a := (41331052640141 / 50000000000000 : ℝ)) (b := (40566737329 / 25000000000000 : ℝ)) (q := (2252370573591 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12694])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12694])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12694]

theorem cert12694_42 : CellCertificate 12694 (443429121988899 / 5000000000000000 : ℝ) (1654674016671983 / 1000000000000000000 : ℝ) (167120082346851 / 5000000000000000 : ℝ)
    (cell12694 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · have h := gap_lower (n := 12694) (a := (2582128836623 / 3125000000000 : ℝ)) (b := (40566737329 / 25000000000000 : ℝ)) (q := (563093639123 / 25000000000000 : ℝ))
      (E := (cell12694 ⟨42, by decide⟩).energy) (xi := (167120082346851 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12694 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12694]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12694])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12694) (a := (2582128836623 / 3125000000000 : ℝ)) (b := (40566737329 / 25000000000000 : ℝ)) (q := (563093639123 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12694])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12694])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12694]

theorem cert12694_43 : CellCertificate 12694 (443429121988899 / 5000000000000000 : ℝ) (1654674016671983 / 1000000000000000000 : ℝ) (167120082346851 / 5000000000000000 : ℝ)
    (cell12694 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · have h := gap_lower (n := 12694) (a := (82594163849113 / 100000000000000 : ℝ)) (b := (40566737329 / 25000000000000 : ℝ)) (q := (2252378545073 / 100000000000000 : ℝ))
      (E := (cell12694 ⟨43, by decide⟩).energy) (xi := (167120082346851 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12694 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12694]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12694])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12694) (a := (82594163849113 / 100000000000000 : ℝ)) (b := (40566737329 / 25000000000000 : ℝ)) (q := (2252378545073 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12694])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12694])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12694]

theorem cert12694_44 : CellCertificate 12694 (443429121988899 / 5000000000000000 : ℝ) (1654674016671983 / 1000000000000000000 : ℝ) (167120082346851 / 5000000000000000 : ℝ)
    (cell12694 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · have h := gap_lower (n := 12694) (a := (41280114241133 / 50000000000000 : ℝ)) (b := (40566737329 / 25000000000000 : ℝ)) (q := (2252382538321 / 100000000000000 : ℝ))
      (E := (cell12694 ⟨44, by decide⟩).energy) (xi := (167120082346851 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12694 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12694]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12694])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12694) (a := (41280114241133 / 50000000000000 : ℝ)) (b := (40566737329 / 25000000000000 : ℝ)) (q := (2252382538321 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12694])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12694])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12694]

theorem cert12694_45 : CellCertificate 12694 (443429121988899 / 5000000000000000 : ℝ) (1654674016671983 / 1000000000000000000 : ℝ) (167120082346851 / 5000000000000000 : ℝ)
    (cell12694 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · have h := gap_lower (n := 12694) (a := (82526316641999 / 100000000000000 : ℝ)) (b := (40566737329 / 25000000000000 : ℝ)) (q := (1126193267501 / 50000000000000 : ℝ))
      (E := (cell12694 ⟨45, by decide⟩).energy) (xi := (167120082346851 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12694 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12694]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12694])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12694) (a := (82526316641999 / 100000000000000 : ℝ)) (b := (40566737329 / 25000000000000 : ℝ)) (q := (1126193267501 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12694])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12694])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12694]

theorem cert12694_46 : CellCertificate 12694 (443429121988899 / 5000000000000000 : ℝ) (1654674016671983 / 1000000000000000000 : ℝ) (167120082346851 / 5000000000000000 : ℝ)
    (cell12694 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · have h := gap_lower (n := 12694) (a := (41246214149531 / 50000000000000 : ℝ)) (b := (40566737329 / 25000000000000 : ℝ)) (q := (2252390592557 / 100000000000000 : ℝ))
      (E := (cell12694 ⟨46, by decide⟩).energy) (xi := (167120082346851 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12694 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12694]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12694])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12694) (a := (41246214149531 / 50000000000000 : ℝ)) (b := (40566737329 / 25000000000000 : ℝ)) (q := (2252390592557 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12694])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12694])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12694]

theorem cert12694_47 : CellCertificate 12694 (443429121988899 / 5000000000000000 : ℝ) (1654674016671983 / 1000000000000000000 : ℝ) (167120082346851 / 5000000000000000 : ℝ)
    (cell12694 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · have h := gap_lower (n := 12694) (a := (2576830107011 / 3125000000000 : ℝ)) (b := (40566737329 / 25000000000000 : ℝ)) (q := (225239459157 / 10000000000000 : ℝ))
      (E := (cell12694 ⟨47, by decide⟩).energy) (xi := (167120082346851 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12694 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12694]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12694])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12694) (a := (2576830107011 / 3125000000000 : ℝ)) (b := (40566737329 / 25000000000000 : ℝ)) (q := (225239459157 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12694])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12694])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12694]

theorem cert12694_48 : CellCertificate 12694 (443429121988899 / 5000000000000000 : ℝ) (1654674016671983 / 1000000000000000000 : ℝ) (167120082346851 / 5000000000000000 : ℝ)
    (cell12694 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · have h := gap_lower (n := 12694) (a := (41212360994457 / 50000000000000 : ℝ)) (b := (40566737329 / 25000000000000 : ℝ)) (q := (1126199294513 / 50000000000000 : ℝ))
      (E := (cell12694 ⟨48, by decide⟩).energy) (xi := (167120082346851 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12694 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12694]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12694])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12694) (a := (41212360994457 / 50000000000000 : ℝ)) (b := (40566737329 / 25000000000000 : ℝ)) (q := (1126199294513 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12694])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12694])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12694]

theorem cert12694_49 : CellCertificate 12694 (443429121988899 / 5000000000000000 : ℝ) (1654674016671983 / 1000000000000000000 : ℝ) (167120082346851 / 5000000000000000 : ℝ)
    (cell12694 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · have h := gap_lower (n := 12694) (a := (82390903963937 / 100000000000000 : ℝ)) (b := (40566737329 / 25000000000000 : ℝ)) (q := (140775161427 / 6250000000000 : ℝ))
      (E := (cell12694 ⟨49, by decide⟩).energy) (xi := (167120082346851 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12694 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12694]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12694])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12694) (a := (82390903963937 / 100000000000000 : ℝ)) (b := (40566737329 / 25000000000000 : ℝ)) (q := (140775161427 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12694])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12694])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12694]

theorem cert12694_50 : CellCertificate 12694 (443429121988899 / 5000000000000000 : ℝ) (1654674016671983 / 1000000000000000000 : ℝ) (167120082346851 / 5000000000000000 : ℝ)
    (cell12694 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · have h := gap_lower (n := 12694) (a := (41178554660377 / 50000000000000 : ℝ)) (b := (40566737329 / 25000000000000 : ℝ)) (q := (563101642671 / 25000000000000 : ℝ))
      (E := (cell12694 ⟨50, by decide⟩).energy) (xi := (167120082346851 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12694 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12694]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12694])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12694) (a := (41178554660377 / 50000000000000 : ℝ)) (b := (40566737329 / 25000000000000 : ℝ)) (q := (563101642671 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12694])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12694])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12694]

theorem cert12694_51 : CellCertificate 12694 (443429121988899 / 5000000000000000 : ℝ) (1654674016671983 / 1000000000000000000 : ℝ) (167120082346851 / 5000000000000000 : ℝ)
    (cell12694 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · have h := gap_lower (n := 12694) (a := (41161669015421 / 50000000000000 : ℝ)) (b := (40566737329 / 25000000000000 : ℝ)) (q := (563102652267 / 25000000000000 : ℝ))
      (E := (cell12694 ⟨51, by decide⟩).energy) (xi := (167120082346851 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12694 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12694]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12694])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12694) (a := (41161669015421 / 50000000000000 : ℝ)) (b := (40566737329 / 25000000000000 : ℝ)) (q := (563102652267 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12694])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12694])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12694]

theorem cert12694_52 : CellCertificate 12694 (443429121988899 / 5000000000000000 : ℝ) (1654674016671983 / 1000000000000000000 : ℝ) (167120082346851 / 5000000000000000 : ℝ)
    (cell12694 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · have h := gap_lower (n := 12694) (a := (82289590065823 / 100000000000000 : ℝ)) (b := (40566737329 / 25000000000000 : ℝ)) (q := (1126207288633 / 50000000000000 : ℝ))
      (E := (cell12694 ⟨52, by decide⟩).energy) (xi := (167120082346851 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12694 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12694]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12694])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12694) (a := (82289590065823 / 100000000000000 : ℝ)) (b := (40566737329 / 25000000000000 : ℝ)) (q := (1126207288633 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12694])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12694])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12694]

theorem cert12694_53 : CellCertificate 12694 (443429121988899 / 5000000000000000 : ℝ) (1654674016671983 / 1000000000000000000 : ℝ) (167120082346851 / 5000000000000000 : ℝ)
    (cell12694 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · have h := gap_lower (n := 12694) (a := (41127932698729 / 50000000000000 : ℝ)) (b := (40566737329 / 25000000000000 : ℝ)) (q := (563104647593 / 25000000000000 : ℝ))
      (E := (cell12694 ⟨53, by decide⟩).energy) (xi := (167120082346851 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12694 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12694]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12694])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12694) (a := (41127932698729 / 50000000000000 : ℝ)) (b := (40566737329 / 25000000000000 : ℝ)) (q := (563104647593 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12694])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12694])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12694]

theorem cert12694_54 : CellCertificate 12694 (443429121988899 / 5000000000000000 : ℝ) (1654674016671983 / 1000000000000000000 : ℝ) (167120082346851 / 5000000000000000 : ℝ)
    (cell12694 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · have h := gap_lower (n := 12694) (a := (82222163997651 / 100000000000000 : ℝ)) (b := (40566737329 / 25000000000000 : ℝ)) (q := (225242258623 / 10000000000000 : ℝ))
      (E := (cell12694 ⟨54, by decide⟩).energy) (xi := (167120082346851 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12694 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12694]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12694])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12694) (a := (82222163997651 / 100000000000000 : ℝ)) (b := (40566737329 / 25000000000000 : ℝ)) (q := (225242258623 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12694])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12694])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12694]

theorem cert12694_55 : CellCertificate 12694 (443429121988899 / 5000000000000000 : ℝ) (1654674016671983 / 1000000000000000000 : ℝ) (167120082346851 / 5000000000000000 : ℝ)
    (cell12694 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · have h := gap_lower (n := 12694) (a := (16437697167689 / 20000000000000 : ℝ)) (b := (40566737329 / 25000000000000 : ℝ)) (q := (112621331029 / 5000000000000 : ℝ))
      (E := (cell12694 ⟨55, by decide⟩).energy) (xi := (167120082346851 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12694 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12694]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12694])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12694) (a := (16437697167689 / 20000000000000 : ℝ)) (b := (40566737329 / 25000000000000 : ℝ)) (q := (112621331029 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12694])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12694])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12694]

theorem cert12694_56 : CellCertificate 12694 (443429121988899 / 5000000000000000 : ℝ) (1654674016671983 / 1000000000000000000 : ℝ) (167120082346851 / 5000000000000000 : ℝ)
    (cell12694 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · have h := gap_lower (n := 12694) (a := (10269353861503 / 12500000000000 : ℝ)) (b := (40566737329 / 25000000000000 : ℝ)) (q := (2252430630799 / 100000000000000 : ℝ))
      (E := (cell12694 ⟨56, by decide⟩).energy) (xi := (167120082346851 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12694 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12694]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12694])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12694) (a := (10269353861503 / 12500000000000 : ℝ)) (b := (40566737329 / 25000000000000 : ℝ)) (q := (2252430630799 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12694])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12694])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12694]

theorem cert12694_57 : CellCertificate 12694 (443429121988899 / 5000000000000000 : ℝ) (1654674016671983 / 1000000000000000000 : ℝ) (167120082346851 / 5000000000000000 : ℝ)
    (cell12694 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · have h := gap_lower (n := 12694) (a := (82121199130709 / 100000000000000 : ℝ)) (b := (40566737329 / 25000000000000 : ℝ)) (q := (281554326639 / 12500000000000 : ℝ))
      (E := (cell12694 ⟨57, by decide⟩).energy) (xi := (167120082346851 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12694 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12694]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12694])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12694) (a := (82121199130709 / 100000000000000 : ℝ)) (b := (40566737329 / 25000000000000 : ℝ)) (q := (281554326639 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12694])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12694])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12694]

theorem cert12694_58 : CellCertificate 12694 (443429121988899 / 5000000000000000 : ℝ) (1654674016671983 / 1000000000000000000 : ℝ) (167120082346851 / 5000000000000000 : ℝ)
    (cell12694 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · have h := gap_lower (n := 12694) (a := (41043795263481 / 50000000000000 : ℝ)) (b := (40566737329 / 25000000000000 : ℝ)) (q := (2252438622703 / 100000000000000 : ℝ))
      (E := (cell12694 ⟨58, by decide⟩).energy) (xi := (167120082346851 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12694 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12694]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12694])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12694) (a := (41043795263481 / 50000000000000 : ℝ)) (b := (40566737329 / 25000000000000 : ℝ)) (q := (2252438622703 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12694])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12694])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12694]

theorem cert12694_59 : CellCertificate 12694 (443429121988899 / 5000000000000000 : ℝ) (1654674016671983 / 1000000000000000000 : ℝ) (167120082346851 / 5000000000000000 : ℝ)
    (cell12694 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · have h := gap_lower (n := 12694) (a := (82054005053379 / 100000000000000 : ℝ)) (b := (40566737329 / 25000000000000 : ℝ)) (q := (450488531091 / 20000000000000 : ℝ))
      (E := (cell12694 ⟨59, by decide⟩).energy) (xi := (167120082346851 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12694 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12694]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12694])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12694) (a := (82054005053379 / 100000000000000 : ℝ)) (b := (40566737329 / 25000000000000 : ℝ)) (q := (450488531091 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12694])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12694])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12694]

theorem cert12695_40 : CellCertificate 12695 (221707570998419 / 2500000000000000 : ℝ) (827271816596219 / 500000000000000000 : ℝ) (83553298316549 / 2500000000000000 : ℝ)
    (cell12695 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · have h := gap_lower (n := 12695) (a := (20674027182167 / 25000000000000 : ℝ)) (b := (40563502823 / 25000000000000 : ℝ)) (q := (2252243626109 / 100000000000000 : ℝ))
      (E := (cell12695 ⟨40, by decide⟩).energy) (xi := (83553298316549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12695 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12695]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12695])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12695) (a := (20674027182167 / 25000000000000 : ℝ)) (b := (40563502823 / 25000000000000 : ℝ)) (q := (2252243626109 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12695])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12695])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12695]

theorem cert12695_41 : CellCertificate 12695 (221707570998419 / 2500000000000000 : ℝ) (827271816596219 / 500000000000000000 : ℝ) (83553298316549 / 2500000000000000 : ℝ)
    (cell12695 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · have h := gap_lower (n := 12695) (a := (82662102907981 / 100000000000000 : ℝ)) (b := (40563502823 / 25000000000000 : ℝ)) (q := (1126123827831 / 50000000000000 : ℝ))
      (E := (cell12695 ⟨41, by decide⟩).energy) (xi := (83553298316549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12695 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12695]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12695])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12695) (a := (82662102907981 / 100000000000000 : ℝ)) (b := (40563502823 / 25000000000000 : ℝ)) (q := (1126123827831 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12695])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12695])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12695]

theorem cert12695_42 : CellCertificate 12695 (221707570998419 / 2500000000000000 : ℝ) (827271816596219 / 500000000000000000 : ℝ) (83553298316549 / 2500000000000000 : ℝ)
    (cell12695 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · have h := gap_lower (n := 12695) (a := (16525624140419 / 20000000000000 : ℝ)) (b := (40563502823 / 25000000000000 : ℝ)) (q := (2252251633639 / 100000000000000 : ℝ))
      (E := (cell12695 ⟨42, by decide⟩).energy) (xi := (83553298316549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12695 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12695]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12695])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12695) (a := (16525624140419 / 20000000000000 : ℝ)) (b := (40563502823 / 25000000000000 : ℝ)) (q := (2252251633639 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12695])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12695])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12695]

theorem cert12695_43 : CellCertificate 12695 (221707570998419 / 2500000000000000 : ℝ) (827271816596219 / 500000000000000000 : ℝ) (83553298316549 / 2500000000000000 : ℝ)
    (cell12695 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · have h := gap_lower (n := 12695) (a := (16518832416263 / 20000000000000 : ℝ)) (b := (40563502823 / 25000000000000 : ℝ)) (q := (2252255617989 / 100000000000000 : ℝ))
      (E := (cell12695 ⟨43, by decide⟩).energy) (xi := (83553298316549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12695 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12695]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12695])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12695) (a := (16518832416263 / 20000000000000 : ℝ)) (b := (40563502823 / 25000000000000 : ℝ)) (q := (2252255617989 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12695])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12695])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12695]

theorem cert12695_44 : CellCertificate 12695 (221707570998419 / 2500000000000000 : ℝ) (827271816596219 / 500000000000000000 : ℝ) (83553298316549 / 2500000000000000 : ℝ)
    (cell12695 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · have h := gap_lower (n := 12695) (a := (16512045403219 / 20000000000000 : ℝ)) (b := (40563502823 / 25000000000000 : ℝ)) (q := (2252259666539 / 100000000000000 : ℝ))
      (E := (cell12695 ⟨44, by decide⟩).energy) (xi := (83553298316549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12695 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12695]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12695])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12695) (a := (16512045403219 / 20000000000000 : ℝ)) (b := (40563502823 / 25000000000000 : ℝ)) (q := (2252259666539 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12695])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12695])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12695]

theorem cert12695_45 : CellCertificate 12695 (221707570998419 / 2500000000000000 : ℝ) (827271816596219 / 500000000000000000 : ℝ) (83553298316549 / 2500000000000000 : ℝ)
    (cell12695 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · have h := gap_lower (n := 12695) (a := (41263157738519 / 50000000000000 : ℝ)) (b := (40563502823 / 25000000000000 : ℝ)) (q := (2252263660397 / 100000000000000 : ℝ))
      (E := (cell12695 ⟨45, by decide⟩).energy) (xi := (83553298316549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12695 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12695]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12695])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12695) (a := (41263157738519 / 50000000000000 : ℝ)) (b := (40563502823 / 25000000000000 : ℝ)) (q := (2252263660397 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12695])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12695])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12695]

theorem cert12695_46 : CellCertificate 12695 (221707570998419 / 2500000000000000 : ℝ) (827271816596219 / 500000000000000000 : ℝ) (83553298316549 / 2500000000000000 : ℝ)
    (cell12695 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · have h := gap_lower (n := 12695) (a := (82492427434897 / 100000000000000 : ℝ)) (b := (40563502823 / 25000000000000 : ℝ)) (q := (563066914233 / 25000000000000 : ℝ))
      (E := (cell12695 ⟨46, by decide⟩).energy) (xi := (83553298316549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12695 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12695]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12695])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12695) (a := (82492427434897 / 100000000000000 : ℝ)) (b := (40563502823 / 25000000000000 : ℝ)) (q := (563066914233 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12695])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12695])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12695]

theorem cert12695_47 : CellCertificate 12695 (221707570998419 / 2500000000000000 : ℝ) (827271816596219 / 500000000000000000 : ℝ) (83553298316549 / 2500000000000000 : ℝ)
    (cell12695 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · have h := gap_lower (n := 12695) (a := (82458562860569 / 100000000000000 : ℝ)) (b := (40563502823 / 25000000000000 : ℝ)) (q := (2252271654479 / 100000000000000 : ℝ))
      (E := (cell12695 ⟨47, by decide⟩).energy) (xi := (83553298316549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12695 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12695]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12695])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12695) (a := (82458562860569 / 100000000000000 : ℝ)) (b := (40563502823 / 25000000000000 : ℝ)) (q := (2252271654479 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12695])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12695])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12695]

theorem cert12695_48 : CellCertificate 12695 (221707570998419 / 2500000000000000 : ℝ) (827271816596219 / 500000000000000000 : ℝ) (83553298316549 / 2500000000000000 : ℝ)
    (cell12695 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · have h := gap_lower (n := 12695) (a := (41212360862549 / 50000000000000 : ℝ)) (b := (40563502823 / 25000000000000 : ℝ)) (q := (56306891279 / 2500000000000 : ℝ))
      (E := (cell12695 ⟨48, by decide⟩).energy) (xi := (83553298316549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12695 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12695]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12695])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12695) (a := (41212360862549 / 50000000000000 : ℝ)) (b := (40563502823 / 25000000000000 : ℝ)) (q := (56306891279 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12695])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12695])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12695]

theorem cert12695_49 : CellCertificate 12695 (221707570998419 / 2500000000000000 : ℝ) (827271816596219 / 500000000000000000 : ℝ) (83553298316549 / 2500000000000000 : ℝ)
    (cell12695 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · have h := gap_lower (n := 12695) (a := (20597725999919 / 25000000000000 : ℝ)) (b := (40563502823 / 25000000000000 : ℝ)) (q := (28153495561 / 1250000000000 : ℝ))
      (E := (cell12695 ⟨49, by decide⟩).energy) (xi := (83553298316549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12695 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12695]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12695])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12695) (a := (20597725999919 / 25000000000000 : ℝ)) (b := (40563502823 / 25000000000000 : ℝ)) (q := (28153495561 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12695])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12695])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12695]

theorem cert12695_50 : CellCertificate 12695 (221707570998419 / 2500000000000000 : ℝ) (827271816596219 / 500000000000000000 : ℝ) (83553298316549 / 2500000000000000 : ℝ)
    (cell12695 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · have h := gap_lower (n := 12695) (a := (20589277413909 / 25000000000000 : ℝ)) (b := (40563502823 / 25000000000000 : ℝ)) (q := (450456738463 / 20000000000000 : ℝ))
      (E := (cell12695 ⟨50, by decide⟩).energy) (xi := (83553298316549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12695 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12695]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12695])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12695) (a := (20589277413909 / 25000000000000 : ℝ)) (b := (40563502823 / 25000000000000 : ℝ)) (q := (450456738463 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12695])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12695])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12695]

theorem cert12695_51 : CellCertificate 12695 (221707570998419 / 2500000000000000 : ℝ) (827271816596219 / 500000000000000000 : ℝ) (83553298316549 / 2500000000000000 : ℝ)
    (cell12695 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · have h := gap_lower (n := 12695) (a := (82323338664457 / 100000000000000 : ℝ)) (b := (40563502823 / 25000000000000 : ℝ)) (q := (1126143836503 / 50000000000000 : ℝ))
      (E := (cell12695 ⟨51, by decide⟩).energy) (xi := (83553298316549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12695 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12695]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12695])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12695) (a := (82323338664457 / 100000000000000 : ℝ)) (b := (40563502823 / 25000000000000 : ℝ)) (q := (1126143836503 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12695])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12695])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12695]

theorem cert12695_52 : CellCertificate 12695 (221707570998419 / 2500000000000000 : ℝ) (827271816596219 / 500000000000000000 : ℝ) (83553298316549 / 2500000000000000 : ℝ)
    (cell12695 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · have h := gap_lower (n := 12695) (a := (82289590997759 / 100000000000000 : ℝ)) (b := (40563502823 / 25000000000000 : ℝ)) (q := (225229170221 / 10000000000000 : ℝ))
      (E := (cell12695 ⟨52, by decide⟩).energy) (xi := (83553298316549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12695 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12695]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12695])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12695) (a := (82289590997759 / 100000000000000 : ℝ)) (b := (40563502823 / 25000000000000 : ℝ)) (q := (225229170221 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12695])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12695])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12695]

theorem cert12695_53 : CellCertificate 12695 (221707570998419 / 2500000000000000 : ℝ) (827271816596219 / 500000000000000000 : ℝ) (83553298316549 / 2500000000000000 : ℝ)
    (cell12695 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · have h := gap_lower (n := 12695) (a := (41127933313653 / 50000000000000 : ℝ)) (b := (40563502823 / 25000000000000 : ℝ)) (q := (2252295658949 / 100000000000000 : ℝ))
      (E := (cell12695 ⟨53, by decide⟩).energy) (xi := (83553298316549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12695 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12695]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12695])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12695) (a := (41127933313653 / 50000000000000 : ℝ)) (b := (40563502823 / 25000000000000 : ℝ)) (q := (2252295658949 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12695])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12695])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12695]

theorem cert12695_54 : CellCertificate 12695 (221707570998419 / 2500000000000000 : ℝ) (827271816596219 / 500000000000000000 : ℝ) (83553298316549 / 2500000000000000 : ℝ)
    (cell12695 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · have h := gap_lower (n := 12695) (a := (82222165525001 / 100000000000000 : ℝ)) (b := (40563502823 / 25000000000000 : ℝ)) (q := (2252299717231 / 100000000000000 : ℝ))
      (E := (cell12695 ⟨54, by decide⟩).energy) (xi := (83553298316549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12695 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12695]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12695])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12695) (a := (82222165525001 / 100000000000000 : ℝ)) (b := (40563502823 / 25000000000000 : ℝ)) (q := (2252299717231 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12695])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12695])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12695]

theorem cert12695_55 : CellCertificate 12695 (221707570998419 / 2500000000000000 : ℝ) (827271816596219 / 500000000000000000 : ℝ) (83553298316549 / 2500000000000000 : ℝ)
    (cell12695 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · have h := gap_lower (n := 12695) (a := (82188487662889 / 100000000000000 : ℝ)) (b := (40563502823 / 25000000000000 : ℝ)) (q := (1126151848269 / 50000000000000 : ℝ))
      (E := (cell12695 ⟨55, by decide⟩).energy) (xi := (83553298316549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12695 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12695]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12695])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12695) (a := (82188487662889 / 100000000000000 : ℝ)) (b := (40563502823 / 25000000000000 : ℝ)) (q := (1126151848269 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12695])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12695])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12695]

theorem cert12695_56 : CellCertificate 12695 (221707570998419 / 2500000000000000 : ℝ) (827271816596219 / 500000000000000000 : ℝ) (83553298316549 / 2500000000000000 : ℝ)
    (cell12695 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · have h := gap_lower (n := 12695) (a := (41077416506577 / 50000000000000 : ℝ)) (b := (40563502823 / 25000000000000 : ℝ)) (q := (1126153855737 / 50000000000000 : ℝ))
      (E := (cell12695 ⟨56, by decide⟩).energy) (xi := (83553298316549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12695 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12695]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12695])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12695) (a := (41077416506577 / 50000000000000 : ℝ)) (b := (40563502823 / 25000000000000 : ℝ)) (q := (1126153855737 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12695])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12695])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12695]

theorem cert12695_57 : CellCertificate 12695 (221707570998419 / 2500000000000000 : ℝ) (827271816596219 / 500000000000000000 : ℝ) (83553298316549 / 2500000000000000 : ℝ)
    (cell12695 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · have h := gap_lower (n := 12695) (a := (82121201548119 / 100000000000000 : ℝ)) (b := (40563502823 / 25000000000000 : ℝ)) (q := (2252311699187 / 100000000000000 : ℝ))
      (E := (cell12695 ⟨57, by decide⟩).energy) (xi := (83553298316549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12695 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12695]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12695])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12695) (a := (82121201548119 / 100000000000000 : ℝ)) (b := (40563502823 / 25000000000000 : ℝ)) (q := (2252311699187 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12695])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12695])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12695]

theorem cert12695_58 : CellCertificate 12695 (221707570998419 / 2500000000000000 : ℝ) (827271816596219 / 500000000000000000 : ℝ) (83553298316549 / 2500000000000000 : ℝ)
    (cell12695 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · have h := gap_lower (n := 12695) (a := (16417518648049 / 20000000000000 : ℝ)) (b := (40563502823 / 25000000000000 : ℝ)) (q := (1126157857431 / 50000000000000 : ℝ))
      (E := (cell12695 ⟨58, by decide⟩).energy) (xi := (83553298316549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12695 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12695]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12695])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12695) (a := (16417518648049 / 20000000000000 : ℝ)) (b := (40563502823 / 25000000000000 : ℝ)) (q := (1126157857431 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12695])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12695])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12695]

theorem cert12695_59 : CellCertificate 12695 (221707570998419 / 2500000000000000 : ℝ) (827271816596219 / 500000000000000000 : ℝ) (83553298316549 / 2500000000000000 : ℝ)
    (cell12695 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · have h := gap_lower (n := 12695) (a := (82054008062129 / 100000000000000 : ℝ)) (b := (40563502823 / 25000000000000 : ℝ)) (q := (1126159847593 / 50000000000000 : ℝ))
      (E := (cell12695 ⟨59, by decide⟩).energy) (xi := (83553298316549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12695 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12695]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12695])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12695) (a := (82054008062129 / 100000000000000 : ℝ)) (b := (40563502823 / 25000000000000 : ℝ)) (q := (1126159847593 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12695])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12695])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12695]

theorem cert12696_40 : CellCertificate 12696 (886802328238787 / 10000000000000000 : ℝ) (1654413270258947 / 1000000000000000000 : ℝ) (334186226251971 / 10000000000000000 : ℝ)
    (cell12696 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · have h := gap_lower (n := 12696) (a := (20674026513591 / 25000000000000 : ℝ)) (b := (32448215069 / 20000000000000 : ℝ)) (q := (2252120769369 / 100000000000000 : ℝ))
      (E := (cell12696 ⟨40, by decide⟩).energy) (xi := (334186226251971 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12696 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12696]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12696])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12696) (a := (20674026513591 / 25000000000000 : ℝ)) (b := (32448215069 / 20000000000000 : ℝ)) (q := (2252120769369 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12696])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12696])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12696]

theorem cert12696_41 : CellCertificate 12696 (886802328238787 / 10000000000000000 : ℝ) (1654413270258947 / 1000000000000000000 : ℝ) (334186226251971 / 10000000000000000 : ℝ)
    (cell12696 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · have h := gap_lower (n := 12696) (a := (41331050268259 / 50000000000000 : ℝ)) (b := (32448215069 / 20000000000000 : ℝ)) (q := (1126062367297 / 50000000000000 : ℝ))
      (E := (cell12696 ⟨41, by decide⟩).energy) (xi := (334186226251971 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12696 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12696]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12696])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12696) (a := (41331050268259 / 50000000000000 : ℝ)) (b := (32448215069 / 20000000000000 : ℝ)) (q := (1126062367297 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12696])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12696])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12696]

theorem cert12696_42 : CellCertificate 12696 (886802328238787 / 10000000000000000 : ℝ) (1654413270258947 / 1000000000000000000 : ℝ) (334186226251971 / 10000000000000000 : ℝ)
    (cell12696 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · have h := gap_lower (n := 12696) (a := (2582128707283 / 3125000000000 : ℝ)) (b := (32448215069 / 20000000000000 : ℝ)) (q := (1126064383239 / 50000000000000 : ℝ))
      (E := (cell12696 ⟨42, by decide⟩).energy) (xi := (334186226251971 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12696 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12696]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12696])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12696) (a := (2582128707283 / 3125000000000 : ℝ)) (b := (32448215069 / 20000000000000 : ℝ)) (q := (1126064383239 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12696])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12696])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12696]

theorem cert12696_43 : CellCertificate 12696 (886802328238787 / 10000000000000000 : ℝ) (1654413270258947 / 1000000000000000000 : ℝ) (334186226251971 / 10000000000000000 : ℝ)
    (cell12696 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · have h := gap_lower (n := 12696) (a := (82594160314281 / 100000000000000 : ℝ)) (b := (32448215069 / 20000000000000 : ℝ)) (q := (2252132746659 / 100000000000000 : ℝ))
      (E := (cell12696 ⟨43, by decide⟩).energy) (xi := (334186226251971 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12696 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12696]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12696])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12696) (a := (82594160314281 / 100000000000000 : ℝ)) (b := (32448215069 / 20000000000000 : ℝ)) (q := (2252132746659 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12696])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12696])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12696]

theorem cert12696_44 : CellCertificate 12696 (886802328238787 / 10000000000000000 : ℝ) (1654413270258947 / 1000000000000000000 : ℝ) (334186226251971 / 10000000000000000 : ℝ)
    (cell12696 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · have h := gap_lower (n := 12696) (a := (82560225550651 / 100000000000000 : ℝ)) (b := (32448215069 / 20000000000000 : ℝ)) (q := (225213673289 / 10000000000000 : ℝ))
      (E := (cell12696 ⟨44, by decide⟩).energy) (xi := (334186226251971 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12696 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12696]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12696])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12696) (a := (82560225550651 / 100000000000000 : ℝ)) (b := (32448215069 / 20000000000000 : ℝ)) (q := (225213673289 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12696])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12696])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12696]

theorem cert12696_45 : CellCertificate 12696 (886802328238787 / 10000000000000000 : ℝ) (1654413270258947 / 1000000000000000000 : ℝ) (334186226251971 / 10000000000000000 : ℝ)
    (cell12696 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · have h := gap_lower (n := 12696) (a := (1289473661137 / 1562500000000 : ℝ)) (b := (32448215069 / 20000000000000 : ℝ)) (q := (2252140782803 / 100000000000000 : ℝ))
      (E := (cell12696 ⟨45, by decide⟩).energy) (xi := (334186226251971 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12696 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12696]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12696])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12696) (a := (1289473661137 / 1562500000000 : ℝ)) (b := (32448215069 / 20000000000000 : ℝ)) (q := (2252140782803 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12696])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12696])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12696]

theorem cert12696_46 : CellCertificate 12696 (886802328238787 / 10000000000000000 : ℝ) (1654413270258947 / 1000000000000000000 : ℝ) (334186226251971 / 10000000000000000 : ℝ)
    (cell12696 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · have h := gap_lower (n := 12696) (a := (41246213285693 / 50000000000000 : ℝ)) (b := (32448215069 / 20000000000000 : ℝ)) (q := (2252144777243 / 100000000000000 : ℝ))
      (E := (cell12696 ⟨46, by decide⟩).energy) (xi := (334186226251971 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12696 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12696]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12696])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12696) (a := (41246213285693 / 50000000000000 : ℝ)) (b := (32448215069 / 20000000000000 : ℝ)) (q := (2252144777243 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12696])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12696])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12696]

theorem cert12696_47 : CellCertificate 12696 (886802328238787 / 10000000000000000 : ℝ) (1654413270258947 / 1000000000000000000 : ℝ) (334186226251971 / 10000000000000000 : ℝ)
    (cell12696 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · have h := gap_lower (n := 12696) (a := (82458562297403 / 100000000000000 : ℝ)) (b := (32448215069 / 20000000000000 : ℝ)) (q := (1126074386693 / 50000000000000 : ℝ))
      (E := (cell12696 ⟨47, by decide⟩).energy) (xi := (334186226251971 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12696 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12696]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12696])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12696) (a := (82458562297403 / 100000000000000 : ℝ)) (b := (32448215069 / 20000000000000 : ℝ)) (q := (1126074386693 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12696])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12696])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12696]

theorem cert12696_48 : CellCertificate 12696 (886802328238787 / 10000000000000000 : ℝ) (1654413270258947 / 1000000000000000000 : ℝ) (334186226251971 / 10000000000000000 : ℝ)
    (cell12696 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · have h := gap_lower (n := 12696) (a := (10303090182733 / 12500000000000 : ℝ)) (b := (32448215069 / 20000000000000 : ℝ)) (q := (281519096169 / 12500000000000 : ℝ))
      (E := (cell12696 ⟨48, by decide⟩).energy) (xi := (334186226251971 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12696 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12696]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12696])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12696) (a := (10303090182733 / 12500000000000 : ℝ)) (b := (32448215069 / 20000000000000 : ℝ)) (q := (281519096169 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12696])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12696])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12696]

theorem cert12696_49 : CellCertificate 12696 (886802328238787 / 10000000000000000 : ℝ) (1654413270258947 / 1000000000000000000 : ℝ) (334186226251971 / 10000000000000000 : ℝ)
    (cell12696 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · have h := gap_lower (n := 12696) (a := (82390904035961 / 100000000000000 : ℝ)) (b := (32448215069 / 20000000000000 : ℝ)) (q := (1126078381523 / 50000000000000 : ℝ))
      (E := (cell12696 ⟨49, by decide⟩).energy) (xi := (334186226251971 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12696 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12696]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12696])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12696) (a := (82390904035961 / 100000000000000 : ℝ)) (b := (32448215069 / 20000000000000 : ℝ)) (q := (1126078381523 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12696])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12696])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12696]

theorem cert12696_50 : CellCertificate 12696 (886802328238787 / 10000000000000000 : ℝ) (1654413270258947 / 1000000000000000000 : ℝ) (334186226251971 / 10000000000000000 : ℝ)
    (cell12696 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · have h := gap_lower (n := 12696) (a := (20589277497757 / 25000000000000 : ℝ)) (b := (32448215069 / 20000000000000 : ℝ)) (q := (2252160811143 / 100000000000000 : ℝ))
      (E := (cell12696 ⟨50, by decide⟩).energy) (xi := (334186226251971 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12696 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12696]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12696])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12696) (a := (20589277497757 / 25000000000000 : ℝ)) (b := (32448215069 / 20000000000000 : ℝ)) (q := (2252160811143 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12696])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12696])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12696]

theorem cert12696_51 : CellCertificate 12696 (886802328238787 / 10000000000000000 : ℝ) (1654413270258947 / 1000000000000000000 : ℝ) (334186226251971 / 10000000000000000 : ℝ)
    (cell12696 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · have h := gap_lower (n := 12696) (a := (16464667859709 / 20000000000000 : ℝ)) (b := (32448215069 / 20000000000000 : ℝ)) (q := (70380149787 / 3125000000000 : ℝ))
      (E := (cell12696 ⟨51, by decide⟩).energy) (xi := (334186226251971 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12696 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12696]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12696])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12696) (a := (16464667859709 / 20000000000000 : ℝ)) (b := (32448215069 / 20000000000000 : ℝ)) (q := (70380149787 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12696])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12696])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12696]

theorem cert12696_52 : CellCertificate 12696 (886802328238787 / 10000000000000000 : ℝ) (1654413270258947 / 1000000000000000000 : ℝ) (334186226251971 / 10000000000000000 : ℝ)
    (cell12696 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · have h := gap_lower (n := 12696) (a := (20572397982533 / 25000000000000 : ℝ)) (b := (32448215069 / 20000000000000 : ℝ)) (q := (281521103053 / 12500000000000 : ℝ))
      (E := (cell12696 ⟨52, by decide⟩).energy) (xi := (334186226251971 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12696 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12696]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12696])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12696) (a := (20572397982533 / 25000000000000 : ℝ)) (b := (32448215069 / 20000000000000 : ℝ)) (q := (281521103053 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12696])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12696])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12696]

theorem cert12696_53 : CellCertificate 12696 (886802328238787 / 10000000000000000 : ℝ) (1654413270258947 / 1000000000000000000 : ℝ) (334186226251971 / 10000000000000000 : ℝ)
    (cell12696 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · have h := gap_lower (n := 12696) (a := (41127933928777 / 50000000000000 : ℝ)) (b := (32448215069 / 20000000000000 : ℝ)) (q := (2252172783887 / 100000000000000 : ℝ))
      (E := (cell12696 ⟨53, by decide⟩).energy) (xi := (334186226251971 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12696 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12696]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12696])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12696) (a := (41127933928777 / 50000000000000 : ℝ)) (b := (32448215069 / 20000000000000 : ℝ)) (q := (2252172783887 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12696])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12696])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12696]

theorem cert12696_54 : CellCertificate 12696 (886802328238787 / 10000000000000000 : ℝ) (1654413270258947 / 1000000000000000000 : ℝ) (334186226251971 / 10000000000000000 : ℝ)
    (cell12696 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · have h := gap_lower (n := 12696) (a := (20555541763179 / 25000000000000 : ℝ)) (b := (32448215069 / 20000000000000 : ℝ)) (q := (2252176786501 / 100000000000000 : ℝ))
      (E := (cell12696 ⟨54, by decide⟩).energy) (xi := (334186226251971 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12696 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12696]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12696])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12696) (a := (20555541763179 / 25000000000000 : ℝ)) (b := (32448215069 / 20000000000000 : ℝ)) (q := (2252176786501 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12696])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12696])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12696]

theorem cert12696_55 : CellCertificate 12696 (886802328238787 / 10000000000000000 : ℝ) (1654413270258947 / 1000000000000000000 : ℝ) (334186226251971 / 10000000000000000 : ℝ)
    (cell12696 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · have h := gap_lower (n := 12696) (a := (41094244743831 / 50000000000000 : ℝ)) (b := (32448215069 / 20000000000000 : ℝ)) (q := (2252180828977 / 100000000000000 : ℝ))
      (E := (cell12696 ⟨55, by decide⟩).energy) (xi := (334186226251971 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12696 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12696]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12696])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12696) (a := (41094244743831 / 50000000000000 : ℝ)) (b := (32448215069 / 20000000000000 : ℝ)) (q := (2252180828977 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12696])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12696])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12696]

theorem cert12696_56 : CellCertificate 12696 (886802328238787 / 10000000000000000 : ℝ) (1654413270258947 / 1000000000000000000 : ℝ) (334186226251971 / 10000000000000000 : ℝ)
    (cell12696 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · have h := gap_lower (n := 12696) (a := (82154835134577 / 100000000000000 : ℝ)) (b := (32448215069 / 20000000000000 : ℝ)) (q := (2252184848691 / 100000000000000 : ℝ))
      (E := (cell12696 ⟨56, by decide⟩).energy) (xi := (334186226251971 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12696 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12696]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12696])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12696) (a := (82154835134577 / 100000000000000 : ℝ)) (b := (32448215069 / 20000000000000 : ℝ)) (q := (2252184848691 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12696])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12696])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12696]

theorem cert12696_57 : CellCertificate 12696 (886802328238787 / 10000000000000000 : ℝ) (1654413270258947 / 1000000000000000000 : ℝ) (334186226251971 / 10000000000000000 : ℝ)
    (cell12696 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · have h := gap_lower (n := 12696) (a := (41060601982893 / 50000000000000 : ℝ)) (b := (32448215069 / 20000000000000 : ℝ)) (q := (450437768373 / 20000000000000 : ℝ))
      (E := (cell12696 ⟨57, by decide⟩).energy) (xi := (334186226251971 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12696 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12696]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12696])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12696) (a := (41060601982893 / 50000000000000 : ℝ)) (b := (32448215069 / 20000000000000 : ℝ)) (q := (450437768373 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12696])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12696])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12696]

theorem cert12696_58 : CellCertificate 12696 (886802328238787 / 10000000000000000 : ℝ) (1654413270258947 / 1000000000000000000 : ℝ) (334186226251971 / 10000000000000000 : ℝ)
    (cell12696 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · have h := gap_lower (n := 12696) (a := (20521898988437 / 25000000000000 : ℝ)) (b := (32448215069 / 20000000000000 : ℝ)) (q := (450438572737 / 20000000000000 : ℝ))
      (E := (cell12696 ⟨58, by decide⟩).energy) (xi := (334186226251971 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12696 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12696]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12696])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12696) (a := (20521898988437 / 25000000000000 : ℝ)) (b := (32448215069 / 20000000000000 : ℝ)) (q := (450438572737 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12696])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12696])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12696]

theorem cert12696_59 : CellCertificate 12696 (886802328238787 / 10000000000000000 : ℝ) (1654413270258947 / 1000000000000000000 : ℝ) (334186226251971 / 10000000000000000 : ℝ)
    (cell12696 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · have h := gap_lower (n := 12696) (a := (10256751383883 / 12500000000000 : ℝ)) (b := (32448215069 / 20000000000000 : ℝ)) (q := (1126098425417 / 50000000000000 : ℝ))
      (E := (cell12696 ⟨59, by decide⟩).energy) (xi := (334186226251971 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12696 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12696]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12696])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12696) (a := (10256751383883 / 12500000000000 : ℝ)) (b := (32448215069 / 20000000000000 : ℝ)) (q := (1126098425417 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12696])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12696])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12696]

theorem cert12697_40 : CellCertificate 12697 (443387188356063 / 5000000000000000 : ℝ) (827141463933327 / 500000000000000000 : ℝ) (334159263649849 / 10000000000000000 : ℝ)
    (cell12697 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · have h := gap_lower (n := 12697) (a := (41348051690467 / 50000000000000 : ℝ)) (b := (40557035369 / 25000000000000 : ℝ)) (q := (2251997909451 / 100000000000000 : ℝ))
      (E := (cell12697 ⟨40, by decide⟩).energy) (xi := (334159263649849 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12697 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12697]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12697])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12697) (a := (41348051690467 / 50000000000000 : ℝ)) (b := (40557035369 / 25000000000000 : ℝ)) (q := (2251997909451 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12697])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12697])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12697]

theorem cert12697_41 : CellCertificate 12697 (443387188356063 / 5000000000000000 : ℝ) (827141463933327 / 500000000000000000 : ℝ) (334159263649849 / 10000000000000000 : ℝ)
    (cell12697 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · have h := gap_lower (n := 12697) (a := (20665524541473 / 25000000000000 : ℝ)) (b := (40557035369 / 25000000000000 : ℝ)) (q := (2252001927929 / 100000000000000 : ℝ))
      (E := (cell12697 ⟨41, by decide⟩).energy) (xi := (334159263649849 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12697 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12697]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12697])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12697) (a := (20665524541473 / 25000000000000 : ℝ)) (b := (40557035369 / 25000000000000 : ℝ)) (q := (2252001927929 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12697])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12697])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12697]

theorem cert12697_42 : CellCertificate 12697 (443387188356063 / 5000000000000000 : ℝ) (827141463933327 / 500000000000000000 : ℝ) (334159263649849 / 10000000000000000 : ℝ)
    (cell12697 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · have h := gap_lower (n := 12697) (a := (5164257285301 / 6250000000000 : ℝ)) (b := (40557035369 / 25000000000000 : ℝ)) (q := (281500737027 / 12500000000000 : ℝ))
      (E := (cell12697 ⟨42, by decide⟩).energy) (xi := (334159263649849 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12697 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12697]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12697])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12697) (a := (5164257285301 / 6250000000000 : ℝ)) (b := (40557035369 / 25000000000000 : ℝ)) (q := (281500737027 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12697])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12697])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12697]

theorem cert12697_43 : CellCertificate 12697 (443387188356063 / 5000000000000000 : ℝ) (827141463933327 / 500000000000000000 : ℝ) (334159263649849 / 10000000000000000 : ℝ)
    (cell12697 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · have h := gap_lower (n := 12697) (a := (82594158548011 / 100000000000000 : ℝ)) (b := (40557035369 / 25000000000000 : ℝ)) (q := (1126004965541 / 50000000000000 : ℝ))
      (E := (cell12697 ⟨43, by decide⟩).energy) (xi := (334159263649849 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12697 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12697]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12697])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12697) (a := (82594158548011 / 100000000000000 : ℝ)) (b := (40557035369 / 25000000000000 : ℝ)) (q := (1126004965541 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12697])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12697])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12697]

theorem cert12697_44 : CellCertificate 12697 (443387188356063 / 5000000000000000 : ℝ) (827141463933327 / 500000000000000000 : ℝ) (334159263649849 / 10000000000000000 : ℝ)
    (cell12697 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · have h := gap_lower (n := 12697) (a := (41280112042967 / 50000000000000 : ℝ)) (b := (40557035369 / 25000000000000 : ℝ)) (q := (281501739237 / 12500000000000 : ℝ))
      (E := (cell12697 ⟨44, by decide⟩).energy) (xi := (334159263649849 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12697 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12697]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12697])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12697) (a := (41280112042967 / 50000000000000 : ℝ)) (b := (40557035369 / 25000000000000 : ℝ)) (q := (281501739237 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12697])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12697])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12697]

theorem cert12697_45 : CellCertificate 12697 (443387188356063 / 5000000000000000 : ℝ) (827141463933327 / 500000000000000000 : ℝ) (334159263649849 / 10000000000000000 : ℝ)
    (cell12697 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · have h := gap_lower (n := 12697) (a := (82526313149189 / 100000000000000 : ℝ)) (b := (40557035369 / 25000000000000 : ℝ)) (q := (2252017902219 / 100000000000000 : ℝ))
      (E := (cell12697 ⟨45, by decide⟩).energy) (xi := (334159263649849 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12697 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12697]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12697])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12697) (a := (82526313149189 / 100000000000000 : ℝ)) (b := (40557035369 / 25000000000000 : ℝ)) (q := (2252017902219 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12697])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12697])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12697]

theorem cert12697_46 : CellCertificate 12697 (443387188356063 / 5000000000000000 : ℝ) (827141463933327 / 500000000000000000 : ℝ) (334159263649849 / 10000000000000000 : ℝ)
    (cell12697 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · have h := gap_lower (n := 12697) (a := (82492425708529 / 100000000000000 : ℝ)) (b := (40557035369 / 25000000000000 : ℝ)) (q := (1126010947301 / 50000000000000 : ℝ))
      (E := (cell12697 ⟨46, by decide⟩).energy) (xi := (334159263649849 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12697 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12697]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12697])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12697) (a := (82492425708529 / 100000000000000 : ℝ)) (b := (40557035369 / 25000000000000 : ℝ)) (q := (1126010947301 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12697])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12697])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12697]

theorem cert12697_47 : CellCertificate 12697 (443387188356063 / 5000000000000000 : ℝ) (827141463933327 / 500000000000000000 : ℝ) (334159263649849 / 10000000000000000 : ℝ)
    (cell12697 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · have h := gap_lower (n := 12697) (a := (16491712346971 / 20000000000000 : ℝ)) (b := (40557035369 / 25000000000000 : ℝ)) (q := (2252025948289 / 100000000000000 : ℝ))
      (E := (cell12697 ⟨47, by decide⟩).energy) (xi := (334159263649849 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12697 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12697]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12697])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12697) (a := (16491712346971 / 20000000000000 : ℝ)) (b := (40557035369 / 25000000000000 : ℝ)) (q := (2252025948289 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12697])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12697])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12697]

theorem cert12697_48 : CellCertificate 12697 (443387188356063 / 5000000000000000 : ℝ) (827141463933327 / 500000000000000000 : ℝ) (334159263649849 / 10000000000000000 : ℝ)
    (cell12697 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · have h := gap_lower (n := 12697) (a := (82424721199211 / 100000000000000 : ℝ)) (b := (40557035369 / 25000000000000 : ℝ)) (q := (2252029943601 / 100000000000000 : ℝ))
      (E := (cell12697 ⟨48, by decide⟩).energy) (xi := (334159263649849 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12697 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12697]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12697])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12697) (a := (82424721199211 / 100000000000000 : ℝ)) (b := (40557035369 / 25000000000000 : ℝ)) (q := (2252029943601 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12697])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12697])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12697]

theorem cert12697_49 : CellCertificate 12697 (443387188356063 / 5000000000000000 : ℝ) (827141463933327 / 500000000000000000 : ℝ) (334159263649849 / 10000000000000000 : ℝ)
    (cell12697 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · have h := gap_lower (n := 12697) (a := (82390904072791 / 100000000000000 : ℝ)) (b := (40557035369 / 25000000000000 : ℝ)) (q := (225203393733 / 10000000000000 : ℝ))
      (E := (cell12697 ⟨49, by decide⟩).energy) (xi := (334159263649849 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12697 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12697]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12697])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12697) (a := (82390904072791 / 100000000000000 : ℝ)) (b := (40557035369 / 25000000000000 : ℝ)) (q := (225203393733 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12697])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12697])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12697]

theorem cert12697_50 : CellCertificate 12697 (443387188356063 / 5000000000000000 : ℝ) (827141463933327 / 500000000000000000 : ℝ) (334159263649849 / 10000000000000000 : ℝ)
    (cell12697 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · have h := gap_lower (n := 12697) (a := (82357110326929 / 100000000000000 : ℝ)) (b := (40557035369 / 25000000000000 : ℝ)) (q := (8797023153 / 390625000000 : ℝ))
      (E := (cell12697 ⟨50, by decide⟩).energy) (xi := (334159263649849 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12697 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12697]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12697])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12697) (a := (82357110326929 / 100000000000000 : ℝ)) (b := (40557035369 / 25000000000000 : ℝ)) (q := (8797023153 / 390625000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12697])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12697])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12697]

theorem cert12697_51 : CellCertificate 12697 (443387188356063 / 5000000000000000 : ℝ) (827141463933327 / 500000000000000000 : ℝ) (334159263649849 / 10000000000000000 : ℝ)
    (cell12697 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · have h := gap_lower (n := 12697) (a := (16464667986621 / 20000000000000 : ℝ)) (b := (40557035369 / 25000000000000 : ℝ)) (q := (2252041969601 / 100000000000000 : ℝ))
      (E := (cell12697 ⟨51, by decide⟩).energy) (xi := (334159263649849 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12697 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12697]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12697])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12697) (a := (16464667986621 / 20000000000000 : ℝ)) (b := (40557035369 / 25000000000000 : ℝ)) (q := (2252041969601 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12697])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12697])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12697]

theorem cert12697_52 : CellCertificate 12697 (443387188356063 / 5000000000000000 : ℝ) (827141463933327 / 500000000000000000 : ℝ) (334159263649849 / 10000000000000000 : ℝ)
    (cell12697 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · have h := gap_lower (n := 12697) (a := (41144796431471 / 50000000000000 : ℝ)) (b := (40557035369 / 25000000000000 : ℝ)) (q := (2252045943909 / 100000000000000 : ℝ))
      (E := (cell12697 ⟨52, by decide⟩).energy) (xi := (334159263649849 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12697 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12697]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12697])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12697) (a := (41144796431471 / 50000000000000 : ℝ)) (b := (40557035369 / 25000000000000 : ℝ)) (q := (2252045943909 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12697])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12697])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12697]

theorem cert12697_53 : CellCertificate 12697 (443387188356063 / 5000000000000000 : ℝ) (827141463933327 / 500000000000000000 : ℝ) (334159263649849 / 10000000000000000 : ℝ)
    (cell12697 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · have h := gap_lower (n := 12697) (a := (82255869088203 / 100000000000000 : ℝ)) (b := (40557035369 / 25000000000000 : ℝ)) (q := (450409993037 / 20000000000000 : ℝ))
      (E := (cell12697 ⟨53, by decide⟩).energy) (xi := (334159263649849 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12697 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12697]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12697])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12697) (a := (82255869088203 / 100000000000000 : ℝ)) (b := (40557035369 / 25000000000000 : ℝ)) (q := (450409993037 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12697])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12697])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12697]

theorem cert12697_54 : CellCertificate 12697 (443387188356063 / 5000000000000000 : ℝ) (827141463933327 / 500000000000000000 : ℝ) (334159263649849 / 10000000000000000 : ℝ)
    (cell12697 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · have h := gap_lower (n := 12697) (a := (16444433716159 / 20000000000000 : ℝ)) (b := (40557035369 / 25000000000000 : ℝ)) (q := (563013492817 / 25000000000000 : ℝ))
      (E := (cell12697 ⟨54, by decide⟩).energy) (xi := (334159263649849 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12697 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12697]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12697])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12697) (a := (16444433716159 / 20000000000000 : ℝ)) (b := (40557035369 / 25000000000000 : ℝ)) (q := (563013492817 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12697])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12697])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12697]

theorem cert12697_55 : CellCertificate 12697 (443387188356063 / 5000000000000000 : ℝ) (827141463933327 / 500000000000000000 : ℝ) (334159263649849 / 10000000000000000 : ℝ)
    (cell12697 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · have h := gap_lower (n := 12697) (a := (82188491312763 / 100000000000000 : ℝ)) (b := (40557035369 / 25000000000000 : ℝ)) (q := (1126028979399 / 50000000000000 : ℝ))
      (E := (cell12697 ⟨55, by decide⟩).energy) (xi := (334159263649849 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12697 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12697]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12697])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12697) (a := (82188491312763 / 100000000000000 : ℝ)) (b := (40557035369 / 25000000000000 : ℝ)) (q := (1126028979399 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12697])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12697])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12697]

theorem cert12697_56 : CellCertificate 12697 (443387188356063 / 5000000000000000 : ℝ) (827141463933327 / 500000000000000000 : ℝ) (334159263649849 / 10000000000000000 : ℝ)
    (cell12697 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · have h := gap_lower (n := 12697) (a := (82154837256293 / 100000000000000 : ℝ)) (b := (40557035369 / 25000000000000 : ℝ)) (q := (1126030991663 / 50000000000000 : ℝ))
      (E := (cell12697 ⟨56, by decide⟩).energy) (xi := (334159263649849 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12697 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12697]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12697])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12697) (a := (82154837256293 / 100000000000000 : ℝ)) (b := (40557035369 / 25000000000000 : ℝ)) (q := (1126030991663 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12697])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12697])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12697]

theorem cert12697_57 : CellCertificate 12697 (443387188356063 / 5000000000000000 : ℝ) (827141463933327 / 500000000000000000 : ℝ) (334159263649849 / 10000000000000000 : ℝ)
    (cell12697 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · have h := gap_lower (n := 12697) (a := (82121206383709 / 100000000000000 : ℝ)) (b := (40557035369 / 25000000000000 : ℝ)) (q := (1126032990999 / 50000000000000 : ℝ))
      (E := (cell12697 ⟨57, by decide⟩).energy) (xi := (334159263649849 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12697 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12697]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12697])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12697) (a := (82121206383709 / 100000000000000 : ℝ)) (b := (40557035369 / 25000000000000 : ℝ)) (q := (1126032990999 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12697])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12697])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12697]

theorem cert12697_58 : CellCertificate 12697 (443387188356063 / 5000000000000000 : ℝ) (827141463933327 / 500000000000000000 : ℝ) (334159263649849 / 10000000000000000 : ℝ)
    (cell12697 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · have h := gap_lower (n := 12697) (a := (82087598667473 / 100000000000000 : ℝ)) (b := (40557035369 / 25000000000000 : ℝ)) (q := (1126035004999 / 50000000000000 : ℝ))
      (E := (cell12697 ⟨58, by decide⟩).energy) (xi := (334159263649849 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12697 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12697]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12697])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12697) (a := (82087598667473 / 100000000000000 : ℝ)) (b := (40557035369 / 25000000000000 : ℝ)) (q := (1126035004999 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12697])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12697])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12697]

theorem cert12697_59 : CellCertificate 12697 (443387188356063 / 5000000000000000 : ℝ) (827141463933327 / 500000000000000000 : ℝ) (334159263649849 / 10000000000000000 : ℝ)
    (cell12697 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · have h := gap_lower (n := 12697) (a := (10256751760023 / 12500000000000 : ℝ)) (b := (40557035369 / 25000000000000 : ℝ)) (q := (2252074004011 / 100000000000000 : ℝ))
      (E := (cell12697 ⟨59, by decide⟩).energy) (xi := (334159263649849 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12697 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12697]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12697])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12697) (a := (10256751760023 / 12500000000000 : ℝ)) (b := (40557035369 / 25000000000000 : ℝ)) (q := (2252074004011 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12697])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12697])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12697]

theorem cert12698_40 : CellCertificate 12698 (886746429412687 / 10000000000000000 : ℝ) (1654152606010703 / 1000000000000000000 : ℝ) (167066152729327 / 5000000000000000 : ℝ)
    (cell12698 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · have h := gap_lower (n := 12698) (a := (10337012588547 / 12500000000000 : ℝ)) (b := (40553802421 / 25000000000000 : ℝ)) (q := (2251875105107 / 100000000000000 : ℝ))
      (E := (cell12698 ⟨40, by decide⟩).energy) (xi := (167066152729327 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12698 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12698]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12698])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12698) (a := (10337012588547 / 12500000000000 : ℝ)) (b := (40553802421 / 25000000000000 : ℝ)) (q := (2251875105107 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12698])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12698])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12698]

theorem cert12698_41 : CellCertificate 12698 (886746429412687 / 10000000000000000 : ℝ) (1654152606010703 / 1000000000000000000 : ℝ) (167066152729327 / 5000000000000000 : ℝ)
    (cell12698 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · have h := gap_lower (n := 12698) (a := (82662095796103 / 100000000000000 : ℝ)) (b := (40553802421 / 25000000000000 : ℝ)) (q := (1125939529677 / 50000000000000 : ℝ))
      (E := (cell12698 ⟨41, by decide⟩).energy) (xi := (167066152729327 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12698 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12698]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12698])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12698) (a := (82662095796103 / 100000000000000 : ℝ)) (b := (40553802421 / 25000000000000 : ℝ)) (q := (1125939529677 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12698])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12698])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12698]

theorem cert12698_42 : CellCertificate 12698 (886746429412687 / 10000000000000000 : ℝ) (1654152606010703 / 1000000000000000000 : ℝ) (167066152729327 / 5000000000000000 : ℝ)
    (cell12698 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · have h := gap_lower (n := 12698) (a := (2582128578043 / 3125000000000 : ℝ)) (b := (40553802421 / 25000000000000 : ℝ)) (q := (140742692603 / 6250000000000 : ℝ))
      (E := (cell12698 ⟨42, by decide⟩).energy) (xi := (167066152729327 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12698 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12698]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12698])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12698) (a := (2582128578043 / 3125000000000 : ℝ)) (b := (40553802421 / 25000000000000 : ℝ)) (q := (140742692603 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12698])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12698])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12698]

theorem cert12698_43 : CellCertificate 12698 (886746429412687 / 10000000000000000 : ℝ) (1654152606010703 / 1000000000000000000 : ℝ) (167066152729327 / 5000000000000000 : ℝ)
    (cell12698 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · have h := gap_lower (n := 12698) (a := (10324269597813 / 12500000000000 : ℝ)) (b := (40553802421 / 25000000000000 : ℝ)) (q := (1125943556221 / 50000000000000 : ℝ))
      (E := (cell12698 ⟨43, by decide⟩).energy) (xi := (167066152729327 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12698 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12698]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12698])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12698) (a := (10324269597813 / 12500000000000 : ℝ)) (b := (40553802421 / 25000000000000 : ℝ)) (q := (1125943556221 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12698])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12698])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12698]

theorem cert12698_44 : CellCertificate 12698 (886746429412687 / 10000000000000000 : ℝ) (1654152606010703 / 1000000000000000000 : ℝ) (167066152729327 / 5000000000000000 : ℝ)
    (cell12698 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · have h := gap_lower (n := 12698) (a := (82560222621943 / 100000000000000 : ℝ)) (b := (40553802421 / 25000000000000 : ℝ)) (q := (2251891091877 / 100000000000000 : ℝ))
      (E := (cell12698 ⟨44, by decide⟩).energy) (xi := (167066152729327 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12698 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12698]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12698])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12698) (a := (82560222621943 / 100000000000000 : ℝ)) (b := (40553802421 / 25000000000000 : ℝ)) (q := (2251891091877 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12698])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12698])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12698]

theorem cert12698_45 : CellCertificate 12698 (886746429412687 / 10000000000000000 : ℝ) (1654152606010703 / 1000000000000000000 : ℝ) (167066152729327 / 5000000000000000 : ℝ)
    (cell12698 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · have h := gap_lower (n := 12698) (a := (82526311986299 / 100000000000000 : ℝ)) (b := (40553802421 / 25000000000000 : ℝ)) (q := (1125947538757 / 50000000000000 : ℝ))
      (E := (cell12698 ⟨45, by decide⟩).energy) (xi := (167066152729327 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12698 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12698]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12698])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12698) (a := (82526311986299 / 100000000000000 : ℝ)) (b := (40553802421 / 25000000000000 : ℝ)) (q := (1125947538757 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12698])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12698])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12698]

theorem cert12698_46 : CellCertificate 12698 (886746429412687 / 10000000000000000 : ℝ) (1654152606010703 / 1000000000000000000 : ℝ) (167066152729327 / 5000000000000000 : ℝ)
    (cell12698 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · have h := gap_lower (n := 12698) (a := (41246212423163 / 50000000000000 : ℝ)) (b := (40553802421 / 25000000000000 : ℝ)) (q := (2251899126787 / 100000000000000 : ℝ))
      (E := (cell12698 ⟨46, by decide⟩).energy) (xi := (167066152729327 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12698 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12698]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12698])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12698) (a := (41246212423163 / 50000000000000 : ℝ)) (b := (40553802421 / 25000000000000 : ℝ)) (q := (2251899126787 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12698])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12698])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12698]

theorem cert12698_47 : CellCertificate 12698 (886746429412687 / 10000000000000000 : ℝ) (1654152606010703 / 1000000000000000000 : ℝ) (167066152729327 / 5000000000000000 : ℝ)
    (cell12698 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · have h := gap_lower (n := 12698) (a := (20614640293231 / 25000000000000 : ℝ)) (b := (40553802421 / 25000000000000 : ℝ)) (q := (56297578007 / 2500000000000 : ℝ))
      (E := (cell12698 ⟨47, by decide⟩).energy) (xi := (167066152729327 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12698 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12698]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12698])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12698) (a := (20614640293231 / 25000000000000 : ℝ)) (b := (40553802421 / 25000000000000 : ℝ)) (q := (56297578007 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12698])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12698])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12698]

theorem cert12698_48 : CellCertificate 12698 (886746429412687 / 10000000000000000 : ℝ) (1654152606010703 / 1000000000000000000 : ℝ) (167066152729327 / 5000000000000000 : ℝ)
    (cell12698 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · have h := gap_lower (n := 12698) (a := (4121236046857 / 5000000000000 : ℝ)) (b := (40553802421 / 25000000000000 : ℝ)) (q := (1125953557487 / 50000000000000 : ℝ))
      (E := (cell12698 ⟨48, by decide⟩).energy) (xi := (167066152729327 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12698 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12698]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12698])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12698) (a := (4121236046857 / 5000000000000 : ℝ)) (b := (40553802421 / 25000000000000 : ℝ)) (q := (1125953557487 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12698])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12698])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12698]

theorem cert12698_49 : CellCertificate 12698 (886746429412687 / 10000000000000000 : ℝ) (1654152606010703 / 1000000000000000000 : ℝ) (167066152729327 / 5000000000000000 : ℝ)
    (cell12698 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · have h := gap_lower (n := 12698) (a := (41195452055083 / 50000000000000 : ℝ)) (b := (40553802421 / 25000000000000 : ℝ)) (q := (1125955554387 / 50000000000000 : ℝ))
      (E := (cell12698 ⟨49, by decide⟩).energy) (xi := (167066152729327 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12698 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12698]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12698])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12698) (a := (41195452055083 / 50000000000000 : ℝ)) (b := (40553802421 / 25000000000000 : ℝ)) (q := (1125955554387 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12698])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12698])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12698]

theorem cert12698_50 : CellCertificate 12698 (886746429412687 / 10000000000000000 : ℝ) (1654152606010703 / 1000000000000000000 : ℝ) (167066152729327 / 5000000000000000 : ℝ)
    (cell12698 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · have h := gap_lower (n := 12698) (a := (41178555331669 / 50000000000000 : ℝ)) (b := (40553802421 / 25000000000000 : ℝ)) (q := (562978789589 / 25000000000000 : ℝ))
      (E := (cell12698 ⟨50, by decide⟩).energy) (xi := (167066152729327 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12698 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12698]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12698])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12698) (a := (41178555331669 / 50000000000000 : ℝ)) (b := (40553802421 / 25000000000000 : ℝ)) (q := (562978789589 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12698])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12698])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12698]

theorem cert12698_51 : CellCertificate 12698 (886746429412687 / 10000000000000000 : ℝ) (1654152606010703 / 1000000000000000000 : ℝ) (167066152729327 / 5000000000000000 : ℝ)
    (cell12698 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · have h := gap_lower (n := 12698) (a := (41161670284069 / 50000000000000 : ℝ)) (b := (40553802421 / 25000000000000 : ℝ)) (q := (1125959571627 / 50000000000000 : ℝ))
      (E := (cell12698 ⟨51, by decide⟩).energy) (xi := (167066152729327 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12698 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12698]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12698])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12698) (a := (41161670284069 / 50000000000000 : ℝ)) (b := (40553802421 / 25000000000000 : ℝ)) (q := (1125959571627 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12698])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12698])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12698]

theorem cert12698_52 : CellCertificate 12698 (886746429412687 / 10000000000000000 : ℝ) (1654152606010703 / 1000000000000000000 : ℝ) (167066152729327 / 5000000000000000 : ℝ)
    (cell12698 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · have h := gap_lower (n := 12698) (a := (20572398449047 / 25000000000000 : ℝ)) (b := (40553802421 / 25000000000000 : ℝ)) (q := (140745194981 / 6250000000000 : ℝ))
      (E := (cell12698 ⟨52, by decide⟩).energy) (xi := (167066152729327 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12698 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12698]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12698])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12698) (a := (20572398449047 / 25000000000000 : ℝ)) (b := (40553802421 / 25000000000000 : ℝ)) (q := (140745194981 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12698])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12698])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12698]

theorem cert12698_53 : CellCertificate 12698 (886746429412687 / 10000000000000000 : ℝ) (1654152606010703 / 1000000000000000000 : ℝ) (167066152729327 / 5000000000000000 : ℝ)
    (cell12698 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · have h := gap_lower (n := 12698) (a := (82255870319253 / 100000000000000 : ℝ)) (b := (40553802421 / 25000000000000 : ℝ)) (q := (2251927143791 / 100000000000000 : ℝ))
      (E := (cell12698 ⟨53, by decide⟩).energy) (xi := (167066152729327 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12698 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12698]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12698])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12698) (a := (82255870319253 / 100000000000000 : ℝ)) (b := (40553802421 / 25000000000000 : ℝ)) (q := (2251927143791 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12698])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12698])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12698]

theorem cert12698_54 : CellCertificate 12698 (886746429412687 / 10000000000000000 : ℝ) (1654152606010703 / 1000000000000000000 : ℝ) (167066152729327 / 5000000000000000 : ℝ)
    (cell12698 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · have h := gap_lower (n := 12698) (a := (82222170109239 / 100000000000000 : ℝ)) (b := (40553802421 / 25000000000000 : ℝ)) (q := (2251931153381 / 100000000000000 : ℝ))
      (E := (cell12698 ⟨54, by decide⟩).energy) (xi := (167066152729327 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12698 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12698]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12698])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12698) (a := (82222170109239 / 100000000000000 : ℝ)) (b := (40553802421 / 25000000000000 : ℝ)) (q := (2251931153381 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12698])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12698])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12698]

theorem cert12698_55 : CellCertificate 12698 (886746429412687 / 10000000000000000 : ℝ) (1654152606010703 / 1000000000000000000 : ℝ) (167066152729327 / 5000000000000000 : ℝ)
    (cell12698 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · have h := gap_lower (n := 12698) (a := (82188493138193 / 100000000000000 : ℝ)) (b := (40553802421 / 25000000000000 : ℝ)) (q := (2251935145101 / 100000000000000 : ℝ))
      (E := (cell12698 ⟨55, by decide⟩).energy) (xi := (167066152729327 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12698 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12698]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12698])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12698) (a := (82188493138193 / 100000000000000 : ℝ)) (b := (40553802421 / 25000000000000 : ℝ)) (q := (2251935145101 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12698])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12698])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12698]

theorem cert12698_56 : CellCertificate 12698 (886746429412687 / 10000000000000000 : ℝ) (1654152606010703 / 1000000000000000000 : ℝ) (167066152729327 / 5000000000000000 : ℝ)
    (cell12698 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · have h := gap_lower (n := 12698) (a := (41077419689151 / 50000000000000 : ℝ)) (b := (40553802421 / 25000000000000 : ℝ)) (q := (2251939174503 / 100000000000000 : ℝ))
      (E := (cell12698 ⟨56, by decide⟩).energy) (xi := (167066152729327 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12698 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12698]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12698])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12698) (a := (41077419689151 / 50000000000000 : ℝ)) (b := (40553802421 / 25000000000000 : ℝ)) (q := (2251939174503 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12698])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12698])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12698]

theorem cert12698_57 : CellCertificate 12698 (886746429412687 / 10000000000000000 : ℝ) (1654152606010703 / 1000000000000000000 : ℝ) (167066152729327 / 5000000000000000 : ℝ)
    (cell12698 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · have h := gap_lower (n := 12698) (a := (82121208801889 / 100000000000000 : ℝ)) (b := (40553802421 / 25000000000000 : ℝ)) (q := (2251943178733 / 100000000000000 : ℝ))
      (E := (cell12698 ⟨57, by decide⟩).energy) (xi := (167066152729327 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12698 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12698]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12698])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12698) (a := (82121208801889 / 100000000000000 : ℝ)) (b := (40553802421 / 25000000000000 : ℝ)) (q := (2251943178733 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12698])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12698])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12698]

theorem cert12698_58 : CellCertificate 12698 (886746429412687 / 10000000000000000 : ℝ) (1654152606010703 / 1000000000000000000 : ℝ) (167066152729327 / 5000000000000000 : ℝ)
    (cell12698 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · have h := gap_lower (n := 12698) (a := (41043800690709 / 50000000000000 : ℝ)) (b := (40553802421 / 25000000000000 : ℝ)) (q := (562986788451 / 25000000000000 : ℝ))
      (E := (cell12698 ⟨58, by decide⟩).energy) (xi := (167066152729327 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12698 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12698]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12698])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12698) (a := (41043800690709 / 50000000000000 : ℝ)) (b := (40553802421 / 25000000000000 : ℝ)) (q := (562986788451 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12698])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12698])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12698]

theorem cert12698_59 : CellCertificate 12698 (886746429412687 / 10000000000000000 : ℝ) (1654152606010703 / 1000000000000000000 : ℝ) (167066152729327 / 5000000000000000 : ℝ)
    (cell12698 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · have h := gap_lower (n := 12698) (a := (82054017089489 / 100000000000000 : ℝ)) (b := (40553802421 / 25000000000000 : ℝ)) (q := (562987788679 / 25000000000000 : ℝ))
      (E := (cell12698 ⟨59, by decide⟩).energy) (xi := (167066152729327 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12698 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12698]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12698])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12698) (a := (82054017089489 / 100000000000000 : ℝ)) (b := (40553802421 / 25000000000000 : ℝ)) (q := (562987788679 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12698])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12698])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12698]

theorem cert12699_40 : CellCertificate 12699 (443359243169733 / 5000000000000000 : ℝ) (1654022304686243 / 1000000000000000000 : ℝ) (33410535167721 / 1000000000000000 : ℝ)
    (cell12699 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · have h := gap_lower (n := 12699) (a := (20674024509173 / 25000000000000 : ℝ)) (b := (5068821249 / 3125000000000 : ℝ)) (q := (2251752297587 / 100000000000000 : ℝ))
      (E := (cell12699 ⟨40, by decide⟩).energy) (xi := (33410535167721 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12699 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12699]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12699])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12699) (a := (20674024509173 / 25000000000000 : ℝ)) (b := (5068821249 / 3125000000000 : ℝ)) (q := (2251752297587 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12699])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12699])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12699]

theorem cert12699_41 : CellCertificate 12699 (443359243169733 / 5000000000000000 : ℝ) (1654022304686243 / 1000000000000000000 : ℝ) (33410535167721 / 1000000000000000 : ℝ)
    (cell12699 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · have h := gap_lower (n := 12699) (a := (82662093427149 / 100000000000000 : ℝ)) (b := (5068821249 / 3125000000000 : ℝ)) (q := (450351261037 / 20000000000000 : ℝ))
      (E := (cell12699 ⟨41, by decide⟩).energy) (xi := (33410535167721 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12699 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12699]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12699])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12699) (a := (82662093427149 / 100000000000000 : ℝ)) (b := (5068821249 / 3125000000000 : ℝ)) (q := (450351261037 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12699])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12699])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12699]

theorem cert12699_42 : CellCertificate 12699 (443359243169733 / 5000000000000000 : ℝ) (1654022304686243 / 1000000000000000000 : ℝ) (33410535167721 / 1000000000000000 : ℝ)
    (cell12699 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · have h := gap_lower (n := 12699) (a := (5164257026921 / 6250000000000 : ℝ)) (b := (5068821249 / 3125000000000 : ℝ)) (q := (90070412911 / 4000000000000 : ℝ))
      (E := (cell12699 ⟨42, by decide⟩).energy) (xi := (33410535167721 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12699 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12699]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12699])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12699) (a := (5164257026921 / 6250000000000 : ℝ)) (b := (5068821249 / 3125000000000 : ℝ)) (q := (90070412911 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12699])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12699])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12699]

theorem cert12699_43 : CellCertificate 12699 (443359243169733 / 5000000000000000 : ℝ) (1654022304686243 / 1000000000000000000 : ℝ) (33410535167721 / 1000000000000000 : ℝ)
    (cell12699 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · have h := gap_lower (n := 12699) (a := (516213468861 / 625000000000 : ℝ)) (b := (5068821249 / 3125000000000 : ℝ)) (q := (2251764290741 / 100000000000000 : ℝ))
      (E := (cell12699 ⟨43, by decide⟩).energy) (xi := (33410535167721 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12699 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12699]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12699])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12699) (a := (516213468861 / 625000000000 : ℝ)) (b := (5068821249 / 3125000000000 : ℝ)) (q := (2251764290741 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12699])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12699])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12699]

theorem cert12699_44 : CellCertificate 12699 (443359243169733 / 5000000000000000 : ℝ) (1654022304686243 / 1000000000000000000 : ℝ) (33410535167721 / 1000000000000000 : ℝ)
    (cell12699 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · have h := gap_lower (n := 12699) (a := (2064005528967 / 2500000000000 : ℝ)) (b := (5068821249 / 3125000000000 : ℝ)) (q := (90070733027 / 4000000000000 : ℝ))
      (E := (cell12699 ⟨44, by decide⟩).energy) (xi := (33410535167721 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12699 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12699]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12699])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12699) (a := (2064005528967 / 2500000000000 : ℝ)) (b := (5068821249 / 3125000000000 : ℝ)) (q := (90070733027 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12699])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12699])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12699]

theorem cert12699_45 : CellCertificate 12699 (443359243169733 / 5000000000000000 : ℝ) (1654022304686243 / 1000000000000000000 : ℝ) (33410535167721 / 1000000000000000 : ℝ)
    (cell12699 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · have h := gap_lower (n := 12699) (a := (825263108241 / 1000000000000 : ℝ)) (b := (5068821249 / 3125000000000 : ℝ)) (q := (450354461737 / 20000000000000 : ℝ))
      (E := (cell12699 ⟨45, by decide⟩).energy) (xi := (33410535167721 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12699 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12699]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12699])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12699) (a := (825263108241 / 1000000000000 : ℝ)) (b := (5068821249 / 3125000000000 : ℝ)) (q := (450354461737 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12699])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12699])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12699]

theorem cert12699_46 : CellCertificate 12699 (443359243169733 / 5000000000000000 : ℝ) (1654022304686243 / 1000000000000000000 : ℝ) (33410535167721 / 1000000000000000 : ℝ)
    (cell12699 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · have h := gap_lower (n := 12699) (a := (82492423984777 / 100000000000000 : ℝ)) (b := (5068821249 / 3125000000000 : ℝ)) (q := (2251776356023 / 100000000000000 : ℝ))
      (E := (cell12699 ⟨46, by decide⟩).energy) (xi := (33410535167721 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12699 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12699]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12699])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12699) (a := (82492423984777 / 100000000000000 : ℝ)) (b := (5068821249 / 3125000000000 : ℝ)) (q := (2251776356023 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12699])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12699])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12699]

theorem cert12699_47 : CellCertificate 12699 (443359243169733 / 5000000000000000 : ℝ) (1654022304686243 / 1000000000000000000 : ℝ) (33410535167721 / 1000000000000000 : ℝ)
    (cell12699 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · have h := gap_lower (n := 12699) (a := (82458560611611 / 100000000000000 : ℝ)) (b := (5068821249 / 3125000000000 : ℝ)) (q := (2251780348269 / 100000000000000 : ℝ))
      (E := (cell12699 ⟨47, by decide⟩).energy) (xi := (33410535167721 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12699 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12699]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12699])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12699) (a := (82458560611611 / 100000000000000 : ℝ)) (b := (5068821249 / 3125000000000 : ℝ)) (q := (2251780348269 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12699])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12699])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12699]

theorem cert12699_48 : CellCertificate 12699 (443359243169733 / 5000000000000000 : ℝ) (1654022304686243 / 1000000000000000000 : ℝ) (33410535167721 / 1000000000000000 : ℝ)
    (cell12699 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · have h := gap_lower (n := 12699) (a := (82424720675649 / 100000000000000 : ℝ)) (b := (5068821249 / 3125000000000 : ℝ)) (q := (281473042801 / 12500000000000 : ℝ))
      (E := (cell12699 ⟨48, by decide⟩).energy) (xi := (33410535167721 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12699 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12699]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12699])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12699) (a := (82424720675649 / 100000000000000 : ℝ)) (b := (5068821249 / 3125000000000 : ℝ)) (q := (281473042801 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12699])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12699])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12699]

theorem cert12699_49 : CellCertificate 12699 (443359243169733 / 5000000000000000 : ℝ) (1654022304686243 / 1000000000000000000 : ℝ) (33410535167721 / 1000000000000000 : ℝ)
    (cell12699 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · have h := gap_lower (n := 12699) (a := (16478180829617 / 20000000000000 : ℝ)) (b := (5068821249 / 3125000000000 : ℝ)) (q := (2251788336341 / 100000000000000 : ℝ))
      (E := (cell12699 ⟨49, by decide⟩).energy) (xi := (33410535167721 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12699 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12699]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12699])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12699) (a := (16478180829617 / 20000000000000 : ℝ)) (b := (5068821249 / 3125000000000 : ℝ)) (q := (2251788336341 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12699])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12699])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12699]

theorem cert12699_50 : CellCertificate 12699 (443359243169733 / 5000000000000000 : ℝ) (1654022304686243 / 1000000000000000000 : ℝ) (33410535167721 / 1000000000000000 : ℝ)
    (cell12699 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · have h := gap_lower (n := 12699) (a := (1286829859379 / 1562500000000 : ℝ)) (b := (5068821249 / 3125000000000 : ℝ)) (q := (28147404097 / 1250000000000 : ℝ))
      (E := (cell12699 ⟨50, by decide⟩).energy) (xi := (33410535167721 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12699 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12699]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12699])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12699) (a := (1286829859379 / 1562500000000 : ℝ)) (b := (5068821249 / 3125000000000 : ℝ)) (q := (28147404097 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12699])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12699])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12699]

theorem cert12699_51 : CellCertificate 12699 (443359243169733 / 5000000000000000 : ℝ) (1654022304686243 / 1000000000000000000 : ℝ) (33410535167721 / 1000000000000000 : ℝ)
    (cell12699 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · have h := gap_lower (n := 12699) (a := (82323341203643 / 100000000000000 : ℝ)) (b := (5068821249 / 3125000000000 : ℝ)) (q := (562949093287 / 25000000000000 : ℝ))
      (E := (cell12699 ⟨51, by decide⟩).energy) (xi := (33410535167721 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12699 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12699]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12699])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12699) (a := (82323341203643 / 100000000000000 : ℝ)) (b := (5068821249 / 3125000000000 : ℝ)) (q := (562949093287 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12699])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12699])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12699]

theorem cert12699_52 : CellCertificate 12699 (443359243169733 / 5000000000000000 : ℝ) (1654022304686243 / 1000000000000000000 : ℝ) (33410535167721 / 1000000000000000 : ℝ)
    (cell12699 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · have h := gap_lower (n := 12699) (a := (8228959472987 / 10000000000000 : ℝ)) (b := (5068821249 / 3125000000000 : ℝ)) (q := (450360070357 / 20000000000000 : ℝ))
      (E := (cell12699 ⟨52, by decide⟩).energy) (xi := (33410535167721 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12699 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12699]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12699])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12699) (a := (8228959472987 / 10000000000000 : ℝ)) (b := (5068821249 / 3125000000000 : ℝ)) (q := (450360070357 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12699])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12699])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12699]

theorem cert12699_53 : CellCertificate 12699 (443359243169733 / 5000000000000000 : ℝ) (1654022304686243 / 1000000000000000000 : ℝ) (33410535167721 / 1000000000000000 : ℝ)
    (cell12699 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · have h := gap_lower (n := 12699) (a := (41127935775351 / 50000000000000 : ℝ)) (b := (5068821249 / 3125000000000 : ℝ)) (q := (2251804378761 / 100000000000000 : ℝ))
      (E := (cell12699 ⟨53, by decide⟩).energy) (xi := (33410535167721 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12699 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12699]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12699])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12699) (a := (41127935775351 / 50000000000000 : ℝ)) (b := (5068821249 / 3125000000000 : ℝ)) (q := (2251804378761 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12699])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12699])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12699]

theorem cert12699_54 : CellCertificate 12699 (443359243169733 / 5000000000000000 : ℝ) (1654022304686243 / 1000000000000000000 : ℝ) (33410535167721 / 1000000000000000 : ℝ)
    (cell12699 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · have h := gap_lower (n := 12699) (a := (82222171638047 / 100000000000000 : ℝ)) (b := (5068821249 / 3125000000000 : ℝ)) (q := (562952097979 / 25000000000000 : ℝ))
      (E := (cell12699 ⟨54, by decide⟩).energy) (xi := (33410535167721 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12699 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12699]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12699])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12699) (a := (82222171638047 / 100000000000000 : ℝ)) (b := (5068821249 / 3125000000000 : ℝ)) (q := (562952097979 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12699])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12699])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12699]

theorem cert12699_55 : CellCertificate 12699 (443359243169733 / 5000000000000000 : ℝ) (1654022304686243 / 1000000000000000000 : ℝ) (33410535167721 / 1000000000000000 : ℝ)
    (cell12699 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · have h := gap_lower (n := 12699) (a := (82188494963951 / 100000000000000 : ℝ)) (b := (5068821249 / 3125000000000 : ℝ)) (q := (140738274243 / 6250000000000 : ℝ))
      (E := (cell12699 ⟨55, by decide⟩).energy) (xi := (33410535167721 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12699 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12699]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12699])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12699) (a := (82188494963951 / 100000000000000 : ℝ)) (b := (5068821249 / 3125000000000 : ℝ)) (q := (140738274243 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12699])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12699])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12699]

theorem cert12699_56 : CellCertificate 12699 (443359243169733 / 5000000000000000 : ℝ) (1654022304686243 / 1000000000000000000 : ℝ) (33410535167721 / 1000000000000000 : ℝ)
    (cell12699 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · have h := gap_lower (n := 12699) (a := (41077420750301 / 50000000000000 : ℝ)) (b := (5068821249 / 3125000000000 : ℝ)) (q := (1125908181551 / 50000000000000 : ℝ))
      (E := (cell12699 ⟨56, by decide⟩).energy) (xi := (33410535167721 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12699 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12699]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12699])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12699) (a := (41077420750301 / 50000000000000 : ℝ)) (b := (5068821249 / 3125000000000 : ℝ)) (q := (1125908181551 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12699])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12699])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12699]

theorem cert12699_57 : CellCertificate 12699 (443359243169733 / 5000000000000000 : ℝ) (1654022304686243 / 1000000000000000000 : ℝ) (33410535167721 / 1000000000000000 : ℝ)
    (cell12699 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · have h := gap_lower (n := 12699) (a := (3284848448813 / 4000000000000 : ℝ)) (b := (5068821249 / 3125000000000 : ℝ)) (q := (1125910186463 / 50000000000000 : ℝ))
      (E := (cell12699 ⟨57, by decide⟩).energy) (xi := (33410535167721 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12699 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12699]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12699])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12699) (a := (3284848448813 / 4000000000000 : ℝ)) (b := (5068821249 / 3125000000000 : ℝ)) (q := (1125910186463 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12699])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12699])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12699]

theorem cert12699_58 : CellCertificate 12699 (443359243169733 / 5000000000000000 : ℝ) (1654022304686243 / 1000000000000000000 : ℝ) (33410535167721 / 1000000000000000 : ℝ)
    (cell12699 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · have h := gap_lower (n := 12699) (a := (2565237627987 / 3125000000000 : ℝ)) (b := (5068821249 / 3125000000000 : ℝ)) (q := (450364882689 / 20000000000000 : ℝ))
      (E := (cell12699 ⟨58, by decide⟩).energy) (xi := (33410535167721 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12699 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12699]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12699])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12699) (a := (2565237627987 / 3125000000000 : ℝ)) (b := (5068821249 / 3125000000000 : ℝ)) (q := (450364882689 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12699])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12699])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12699]

theorem cert12699_59 : CellCertificate 12699 (443359243169733 / 5000000000000000 : ℝ) (1654022304686243 / 1000000000000000000 : ℝ) (33410535167721 / 1000000000000000 : ℝ)
    (cell12699 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · have h := gap_lower (n := 12699) (a := (4102701004949 / 5000000000000 : ℝ)) (b := (5068821249 / 3125000000000 : ℝ)) (q := (2251828421339 / 100000000000000 : ℝ))
      (E := (cell12699 ⟨59, by decide⟩).energy) (xi := (33410535167721 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12699 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12699]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12699])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12699) (a := (4102701004949 / 5000000000000 : ℝ)) (b := (5068821249 / 3125000000000 : ℝ)) (q := (2251828421339 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12699])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12699])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12699]

end BstLean.Part268
