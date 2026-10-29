import BstLean.Part268CellShard19Checks1

/-! Twenty scalar cells per dimension in a 25-dimension shard. -/
namespace BstLean.Part268
open Real BstLean.Part263

theorem cert12825_40 : CellCertificate 12825 (441615566752293 / 5000000000000000 : ℝ) (1637766970200113 / 1000000000000000000 : ℝ) (66148812357929 / 2000000000000000 : ℝ)
    (cell12825 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · have h := gap_lower (n := 12825) (a := (82695768302317 / 100000000000000 : ℝ)) (b := (78412877 / 48828125000 : ℝ)) (q := (1118271049837 / 50000000000000 : ℝ))
      (E := (cell12825 ⟨40, by decide⟩).energy) (xi := (66148812357929 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12825 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12825]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12825])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12825) (a := (82695768302317 / 100000000000000 : ℝ)) (b := (78412877 / 48828125000 : ℝ)) (q := (1118271049837 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12825])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12825])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12825]

theorem cert12825_41 : CellCertificate 12825 (441615566752293 / 5000000000000000 : ℝ) (1637766970200113 / 1000000000000000000 : ℝ) (66148812357929 / 2000000000000000 : ℝ)
    (cell12825 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · have h := gap_lower (n := 12825) (a := (82661801545733 / 100000000000000 : ℝ)) (b := (78412877 / 48828125000 : ℝ)) (q := (1118273065793 / 50000000000000 : ℝ))
      (E := (cell12825 ⟨41, by decide⟩).energy) (xi := (66148812357929 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12825 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12825]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12825])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12825) (a := (82661801545733 / 100000000000000 : ℝ)) (b := (78412877 / 48828125000 : ℝ)) (q := (1118273065793 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12825])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12825])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12825]

theorem cert12825_42 : CellCertificate 12825 (441615566752293 / 5000000000000000 : ℝ) (1637766970200113 / 1000000000000000000 : ℝ) (66148812357929 / 2000000000000000 : ℝ)
    (cell12825 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · have h := gap_lower (n := 12825) (a := (20656964587519 / 25000000000000 : ℝ)) (b := (78412877 / 48828125000 : ℝ)) (q := (1118275071551 / 50000000000000 : ℝ))
      (E := (cell12825 ⟨42, by decide⟩).energy) (xi := (66148812357929 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12825 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12825]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12825])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12825) (a := (20656964587519 / 25000000000000 : ℝ)) (b := (78412877 / 48828125000 : ℝ)) (q := (1118275071551 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12825])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12825])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12825]

theorem cert12825_43 : CellCertificate 12825 (441615566752293 / 5000000000000000 : ℝ) (1637766970200113 / 1000000000000000000 : ℝ) (66148812357929 / 2000000000000000 : ℝ)
    (cell12825 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · have h := gap_lower (n := 12825) (a := (20648484671437 / 25000000000000 : ℝ)) (b := (78412877 / 48828125000 : ℝ)) (q := (279569266649 / 12500000000000 : ℝ))
      (E := (cell12825 ⟨43, by decide⟩).energy) (xi := (66148812357929 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12825 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12825]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12825])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12825) (a := (20648484671437 / 25000000000000 : ℝ)) (b := (78412877 / 48828125000 : ℝ)) (q := (279569266649 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12825])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12825])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12825]

theorem cert12825_44 : CellCertificate 12825 (441615566752293 / 5000000000000000 : ℝ) (1637766970200113 / 1000000000000000000 : ℝ) (66148812357929 / 2000000000000000 : ℝ)
    (cell12825 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · have h := gap_lower (n := 12825) (a := (41280021261651 / 50000000000000 : ℝ)) (b := (78412877 / 48828125000 : ℝ)) (q := (2236558159459 / 100000000000000 : ℝ))
      (E := (cell12825 ⟨44, by decide⟩).energy) (xi := (66148812357929 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12825 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12825]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12825])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12825) (a := (41280021261651 / 50000000000000 : ℝ)) (b := (78412877 / 48828125000 : ℝ)) (q := (2236558159459 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12825])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12825])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12825]

theorem cert12825_45 : CellCertificate 12825 (441615566752293 / 5000000000000000 : ℝ) (1637766970200113 / 1000000000000000000 : ℝ) (66148812357929 / 2000000000000000 : ℝ)
    (cell12825 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · have h := gap_lower (n := 12825) (a := (20631542458359 / 25000000000000 : ℝ)) (b := (78412877 / 48828125000 : ℝ)) (q := (69892567551 / 3125000000000 : ℝ))
      (E := (cell12825 ⟨45, by decide⟩).energy) (xi := (66148812357929 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12825 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12825]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12825])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12825) (a := (20631542458359 / 25000000000000 : ℝ)) (b := (78412877 / 48828125000 : ℝ)) (q := (69892567551 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12825])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12825])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12825]

theorem cert12825_46 : CellCertificate 12825 (441615566752293 / 5000000000000000 : ℝ) (1637766970200113 / 1000000000000000000 : ℝ) (66148812357929 / 2000000000000000 : ℝ)
    (cell12825 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · have h := gap_lower (n := 12825) (a := (82492320586999 / 100000000000000 : ℝ)) (b := (78412877 / 48828125000 : ℝ)) (q := (2236566138029 / 100000000000000 : ℝ))
      (E := (cell12825 ⟨46, by decide⟩).energy) (xi := (66148812357929 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12825 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12825]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12825])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12825) (a := (82492320586999 / 100000000000000 : ℝ)) (b := (78412877 / 48828125000 : ℝ)) (q := (2236566138029 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12825])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12825])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12825]

theorem cert12825_47 : CellCertificate 12825 (441615566752293 / 5000000000000000 : ℝ) (1637766970200113 / 1000000000000000000 : ℝ) (66148812357929 / 2000000000000000 : ℝ)
    (cell12825 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · have h := gap_lower (n := 12825) (a := (10307311844373 / 12500000000000 : ℝ)) (b := (78412877 / 48828125000 : ℝ)) (q := (2236570145677 / 100000000000000 : ℝ))
      (E := (cell12825 ⟨47, by decide⟩).energy) (xi := (66148812357929 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12825 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12825]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12825])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12825) (a := (10307311844373 / 12500000000000 : ℝ)) (b := (78412877 / 48828125000 : ℝ)) (q := (2236570145677 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12825])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12825])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12825]

theorem cert12825_48 : CellCertificate 12825 (441615566752293 / 5000000000000000 : ℝ) (1637766970200113 / 1000000000000000000 : ℝ) (66148812357929 / 2000000000000000 : ℝ)
    (cell12825 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · have h := gap_lower (n := 12825) (a := (8242469230853 / 10000000000000 : ℝ)) (b := (78412877 / 48828125000 : ℝ)) (q := (2236574182537 / 100000000000000 : ℝ))
      (E := (cell12825 ⟨48, by decide⟩).energy) (xi := (66148812357929 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12825 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12825]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12825])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12825) (a := (8242469230853 / 10000000000000 : ℝ)) (b := (78412877 / 48828125000 : ℝ)) (q := (2236574182537 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12825])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12825])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12825]

theorem cert12825_49 : CellCertificate 12825 (441615566752293 / 5000000000000000 : ℝ) (1637766970200113 / 1000000000000000000 : ℝ) (66148812357929 / 2000000000000000 : ℝ)
    (cell12825 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · have h := gap_lower (n := 12825) (a := (82390913218921 / 100000000000000 : ℝ)) (b := (78412877 / 48828125000 : ℝ)) (q := (279572273423 / 12500000000000 : ℝ))
      (E := (cell12825 ⟨49, by decide⟩).energy) (xi := (66148812357929 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12825 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12825]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12825])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12825) (a := (82390913218921 / 100000000000000 : ℝ)) (b := (78412877 / 48828125000 : ℝ)) (q := (279572273423 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12825])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12825])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12825]

theorem cert12825_50 : CellCertificate 12825 (441615566752293 / 5000000000000000 : ℝ) (1637766970200113 / 1000000000000000000 : ℝ) (66148812357929 / 2000000000000000 : ℝ)
    (cell12825 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · have h := gap_lower (n := 12825) (a := (41178578728793 / 50000000000000 : ℝ)) (b := (78412877 / 48828125000 : ℝ)) (q := (89463288667 / 4000000000000 : ℝ))
      (E := (cell12825 ⟨50, by decide⟩).energy) (xi := (66148812357929 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12825 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12825]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12825])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12825) (a := (41178578728793 / 50000000000000 : ℝ)) (b := (78412877 / 48828125000 : ℝ)) (q := (89463288667 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12825])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12825])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12825]

theorem cert12825_51 : CellCertificate 12825 (441615566752293 / 5000000000000000 : ℝ) (1637766970200113 / 1000000000000000000 : ℝ) (66148812357929 / 2000000000000000 : ℝ)
    (cell12825 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · have h := gap_lower (n := 12825) (a := (16464684999219 / 20000000000000 : ℝ)) (b := (78412877 / 48828125000 : ℝ)) (q := (447317241743 / 20000000000000 : ℝ))
      (E := (cell12825 ⟨51, by decide⟩).energy) (xi := (66148812357929 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12825 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12825]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12825])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12825) (a := (16464684999219 / 20000000000000 : ℝ)) (b := (78412877 / 48828125000 : ℝ)) (q := (447317241743 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12825])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12825])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12825]

theorem cert12825_52 : CellCertificate 12825 (441615566752293 / 5000000000000000 : ℝ) (1637766970200113 / 1000000000000000000 : ℝ) (66148812357929 / 2000000000000000 : ℝ)
    (cell12825 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · have h := gap_lower (n := 12825) (a := (82289715806161 / 100000000000000 : ℝ)) (b := (78412877 / 48828125000 : ℝ)) (q := (1118295109793 / 50000000000000 : ℝ))
      (E := (cell12825 ⟨52, by decide⟩).energy) (xi := (66148812357929 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12825 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12825]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12825])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12825) (a := (82289715806161 / 100000000000000 : ℝ)) (b := (78412877 / 48828125000 : ℝ)) (q := (1118295109793 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12825])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12825])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12825]

theorem cert12825_53 : CellCertificate 12825 (441615566752293 / 5000000000000000 : ℝ) (1637766970200113 / 1000000000000000000 : ℝ) (66148812357929 / 2000000000000000 : ℝ)
    (cell12825 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · have h := gap_lower (n := 12825) (a := (82256029859639 / 100000000000000 : ℝ)) (b := (78412877 / 48828125000 : ℝ)) (q := (1118297093561 / 50000000000000 : ℝ))
      (E := (cell12825 ⟨53, by decide⟩).energy) (xi := (66148812357929 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12825 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12825]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12825])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12825) (a := (82256029859639 / 100000000000000 : ℝ)) (b := (78412877 / 48828125000 : ℝ)) (q := (1118297093561 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12825])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12825])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12825]

theorem cert12825_54 : CellCertificate 12825 (441615566752293 / 5000000000000000 : ℝ) (1637766970200113 / 1000000000000000000 : ℝ) (66148812357929 / 2000000000000000 : ℝ)
    (cell12825 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · have h := gap_lower (n := 12825) (a := (82222367128523 / 100000000000000 : ℝ)) (b := (78412877 / 48828125000 : ℝ)) (q := (2236598226123 / 100000000000000 : ℝ))
      (E := (cell12825 ⟨54, by decide⟩).energy) (xi := (66148812357929 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12825 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12825]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12825])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12825) (a := (82222367128523 / 100000000000000 : ℝ)) (b := (78412877 / 48828125000 : ℝ)) (q := (2236598226123 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12825])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12825])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12825]

theorem cert12825_55 : CellCertificate 12825 (441615566752293 / 5000000000000000 : ℝ) (1637766970200113 / 1000000000000000000 : ℝ) (66148812357929 / 2000000000000000 : ℝ)
    (cell12825 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · have h := gap_lower (n := 12825) (a := (82188727584949 / 100000000000000 : ℝ)) (b := (78412877 / 48828125000 : ℝ)) (q := (559150553729 / 25000000000000 : ℝ))
      (E := (cell12825 ⟨55, by decide⟩).energy) (xi := (66148812357929 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12825 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12825]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12825])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12825) (a := (82188727584949 / 100000000000000 : ℝ)) (b := (78412877 / 48828125000 : ℝ)) (q := (559150553729 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12825])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12825])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12825]

theorem cert12825_56 : CellCertificate 12825 (441615566752293 / 5000000000000000 : ℝ) (1637766970200113 / 1000000000000000000 : ℝ) (66148812357929 / 2000000000000000 : ℝ)
    (cell12825 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · have h := gap_lower (n := 12825) (a := (8215511120119 / 10000000000000 : ℝ)) (b := (78412877 / 48828125000 : ℝ)) (q := (279575783497 / 12500000000000 : ℝ))
      (E := (cell12825 ⟨56, by decide⟩).energy) (xi := (66148812357929 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12825 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12825]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12825])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12825) (a := (8215511120119 / 10000000000000 : ℝ)) (b := (78412877 / 48828125000 : ℝ)) (q := (279575783497 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12825])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12825])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12825]

theorem cert12825_57 : CellCertificate 12825 (441615566752293 / 5000000000000000 : ℝ) (1637766970200113 / 1000000000000000000 : ℝ) (66148812357929 / 2000000000000000 : ℝ)
    (cell12825 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · have h := gap_lower (n := 12825) (a := (41060758974829 / 50000000000000 : ℝ)) (b := (78412877 / 48828125000 : ℝ)) (q := (559152565781 / 25000000000000 : ℝ))
      (E := (cell12825 ⟨57, by decide⟩).energy) (xi := (66148812357929 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12825 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12825]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12825])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12825) (a := (41060758974829 / 50000000000000 : ℝ)) (b := (78412877 / 48828125000 : ℝ)) (q := (559152565781 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12825])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12825])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12825]

theorem cert12825_58 : CellCertificate 12825 (441615566752293 / 5000000000000000 : ℝ) (1637766970200113 / 1000000000000000000 : ℝ) (66148812357929 / 2000000000000000 : ℝ)
    (cell12825 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · have h := gap_lower (n := 12825) (a := (41043973901451 / 50000000000000 : ℝ)) (b := (78412877 / 48828125000 : ℝ)) (q := (559153563833 / 25000000000000 : ℝ))
      (E := (cell12825 ⟨58, by decide⟩).energy) (xi := (66148812357929 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12825 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12825]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12825])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12825) (a := (41043973901451 / 50000000000000 : ℝ)) (b := (78412877 / 48828125000 : ℝ)) (q := (559153563833 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12825])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12825])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12825]

theorem cert12825_59 : CellCertificate 12825 (441615566752293 / 5000000000000000 : ℝ) (1637766970200113 / 1000000000000000000 : ℝ) (66148812357929 / 2000000000000000 : ℝ)
    (cell12825 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · have h := gap_lower (n := 12825) (a := (82054400733609 / 100000000000000 : ℝ)) (b := (78412877 / 48828125000 : ℝ)) (q := (1118309120127 / 50000000000000 : ℝ))
      (E := (cell12825 ⟨59, by decide⟩).energy) (xi := (66148812357929 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12825 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12825]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12825])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12825) (a := (82054400733609 / 100000000000000 : ℝ)) (b := (78412877 / 48828125000 : ℝ)) (q := (1118309120127 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12825])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12825])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12825]

theorem cert12826_40 : CellCertificate 12826 (6900029055497 / 78125000000000 : ℝ) (818819618728447 / 500000000000000000 : ℝ) (330717658666419 / 10000000000000000 : ℝ)
    (cell12826 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · have h := gap_lower (n := 12826) (a := (41347882869717 / 50000000000000 : ℝ)) (b := (40144225473 / 25000000000000 : ℝ)) (q := (2236423361431 / 100000000000000 : ℝ))
      (E := (cell12826 ⟨40, by decide⟩).energy) (xi := (330717658666419 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12826 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12826]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12826])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12826) (a := (41347882869717 / 50000000000000 : ℝ)) (b := (40144225473 / 25000000000000 : ℝ)) (q := (2236423361431 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12826])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12826])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12826]

theorem cert12826_41 : CellCertificate 12826 (6900029055497 / 78125000000000 : ℝ) (818819618728447 / 500000000000000000 : ℝ) (330717658666419 / 10000000000000000 : ℝ)
    (cell12826 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · have h := gap_lower (n := 12826) (a := (4133089964049 / 5000000000000 : ℝ)) (b := (40144225473 / 25000000000000 : ℝ)) (q := (447285467127 / 20000000000000 : ℝ))
      (E := (cell12826 ⟨41, by decide⟩).energy) (xi := (330717658666419 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12826 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12826]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12826])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12826) (a := (4133089964049 / 5000000000000 : ℝ)) (b := (40144225473 / 25000000000000 : ℝ)) (q := (447285467127 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12826])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12826])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12826]

theorem cert12826_42 : CellCertificate 12826 (6900029055497 / 78125000000000 : ℝ) (818819618728447 / 500000000000000000 : ℝ) (330717658666419 / 10000000000000000 : ℝ)
    (cell12826 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · have h := gap_lower (n := 12826) (a := (82627856383041 / 100000000000000 : ℝ)) (b := (40144225473 / 25000000000000 : ℝ)) (q := (223643134889 / 10000000000000 : ℝ))
      (E := (cell12826 ⟨42, by decide⟩).energy) (xi := (330717658666419 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12826 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12826]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12826])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12826) (a := (82627856383041 / 100000000000000 : ℝ)) (b := (40144225473 / 25000000000000 : ℝ)) (q := (223643134889 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12826])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12826])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12826]

theorem cert12826_43 : CellCertificate 12826 (6900029055497 / 78125000000000 : ℝ) (818819618728447 / 500000000000000000 : ℝ) (330717658666419 / 10000000000000000 : ℝ)
    (cell12826 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · have h := gap_lower (n := 12826) (a := (41296968508011 / 50000000000000 : ℝ)) (b := (40144225473 / 25000000000000 : ℝ)) (q := (559108835351 / 25000000000000 : ℝ))
      (E := (cell12826 ⟨43, by decide⟩).energy) (xi := (330717658666419 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12826 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12826]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12826])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12826) (a := (41296968508011 / 50000000000000 : ℝ)) (b := (40144225473 / 25000000000000 : ℝ)) (q := (559108835351 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12826])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12826])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12826]

theorem cert12826_44 : CellCertificate 12826 (6900029055497 / 78125000000000 : ℝ) (818819618728447 / 500000000000000000 : ℝ) (330717658666419 / 10000000000000000 : ℝ)
    (cell12826 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · have h := gap_lower (n := 12826) (a := (41280020575237 / 50000000000000 : ℝ)) (b := (40144225473 / 25000000000000 : ℝ)) (q := (2236439370781 / 100000000000000 : ℝ))
      (E := (cell12826 ⟨44, by decide⟩).energy) (xi := (330717658666419 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12826 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12826]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12826])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12826) (a := (41280020575237 / 50000000000000 : ℝ)) (b := (40144225473 / 25000000000000 : ℝ)) (q := (2236439370781 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12826])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12826])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12826]

theorem cert12826_45 : CellCertificate 12826 (6900029055497 / 78125000000000 : ℝ) (818819618728447 / 500000000000000000 : ℝ) (330717658666419 / 10000000000000000 : ℝ)
    (cell12826 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · have h := gap_lower (n := 12826) (a := (41263084378549 / 50000000000000 : ℝ)) (b := (40144225473 / 25000000000000 : ℝ)) (q := (2236443376749 / 100000000000000 : ℝ))
      (E := (cell12826 ⟨45, by decide⟩).energy) (xi := (330717658666419 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12826 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12826]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12826])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12826) (a := (41263084378549 / 50000000000000 : ℝ)) (b := (40144225473 / 25000000000000 : ℝ)) (q := (2236443376749 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12826])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12826])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12826]

theorem cert12826_46 : CellCertificate 12826 (6900029055497 / 78125000000000 : ℝ) (818819618728447 / 500000000000000000 : ℝ) (330717658666419 / 10000000000000000 : ℝ)
    (cell12826 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · have h := gap_lower (n := 12826) (a := (82492319806743 / 100000000000000 : ℝ)) (b := (40144225473 / 25000000000000 : ℝ)) (q := (89457896661 / 4000000000000 : ℝ))
      (E := (cell12826 ⟨46, by decide⟩).energy) (xi := (330717658666419 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12826 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12826]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12826])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12826) (a := (82492319806743 / 100000000000000 : ℝ)) (b := (40144225473 / 25000000000000 : ℝ)) (q := (89457896661 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12826])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12826])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12826]

theorem cert12826_47 : CellCertificate 12826 (6900029055497 / 78125000000000 : ℝ) (818819618728447 / 500000000000000000 : ℝ) (330717658666419 / 10000000000000000 : ℝ)
    (cell12826 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · have h := gap_lower (n := 12826) (a := (82458494270403 / 100000000000000 : ℝ)) (b := (40144225473 / 25000000000000 : ℝ)) (q := (559112842609 / 25000000000000 : ℝ))
      (E := (cell12826 ⟨47, by decide⟩).energy) (xi := (330717658666419 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12826 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12826]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12826])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12826) (a := (82458494270403 / 100000000000000 : ℝ)) (b := (40144225473 / 25000000000000 : ℝ)) (q := (559112842609 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12826])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12826])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12826]

theorem cert12826_48 : CellCertificate 12826 (6900029055497 / 78125000000000 : ℝ) (818819618728447 / 500000000000000000 : ℝ) (330717658666419 / 10000000000000000 : ℝ)
    (cell12826 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · have h := gap_lower (n := 12826) (a := (82424692119217 / 100000000000000 : ℝ)) (b := (40144225473 / 25000000000000 : ℝ)) (q := (2236455413141 / 100000000000000 : ℝ))
      (E := (cell12826 ⟨48, by decide⟩).energy) (xi := (330717658666419 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12826 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12826]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12826])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12826) (a := (82424692119217 / 100000000000000 : ℝ)) (b := (40144225473 / 25000000000000 : ℝ)) (q := (2236455413141 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12826])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12826])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12826]

theorem cert12826_49 : CellCertificate 12826 (6900029055497 / 78125000000000 : ℝ) (818819618728447 / 500000000000000000 : ℝ) (330717658666419 / 10000000000000000 : ℝ)
    (cell12826 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · have h := gap_lower (n := 12826) (a := (82390913324471 / 100000000000000 : ℝ)) (b := (40144225473 / 25000000000000 : ℝ)) (q := (559114856129 / 25000000000000 : ℝ))
      (E := (cell12826 ⟨49, by decide⟩).energy) (xi := (330717658666419 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12826 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12826]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12826])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12826) (a := (82390913324471 / 100000000000000 : ℝ)) (b := (40144225473 / 25000000000000 : ℝ)) (q := (559114856129 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12826])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12826])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12826]

theorem cert12826_50 : CellCertificate 12826 (6900029055497 / 78125000000000 : ℝ) (818819618728447 / 500000000000000000 : ℝ) (330717658666419 / 10000000000000000 : ℝ)
    (cell12826 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · have h := gap_lower (n := 12826) (a := (41178578928797 / 50000000000000 : ℝ)) (b := (40144225473 / 25000000000000 : ℝ)) (q := (2236463402021 / 100000000000000 : ℝ))
      (E := (cell12826 ⟨50, by decide⟩).energy) (xi := (330717658666419 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12826 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12826]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12826])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12826) (a := (41178578928797 / 50000000000000 : ℝ)) (b := (40144225473 / 25000000000000 : ℝ)) (q := (2236463402021 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12826])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12826])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12826]

theorem cert12826_51 : CellCertificate 12826 (6900029055497 / 78125000000000 : ℝ) (818819618728447 / 500000000000000000 : ℝ) (330717658666419 / 10000000000000000 : ℝ)
    (cell12826 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · have h := gap_lower (n := 12826) (a := (20580856422539 / 25000000000000 : ℝ)) (b := (40144225473 / 25000000000000 : ℝ)) (q := (1118233700963 / 50000000000000 : ℝ))
      (E := (cell12826 ⟨51, by decide⟩).energy) (xi := (330717658666419 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12826 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12826]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12826])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12826) (a := (20580856422539 / 25000000000000 : ℝ)) (b := (40144225473 / 25000000000000 : ℝ)) (q := (1118233700963 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12826])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12826])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12826]

theorem cert12826_52 : CellCertificate 12826 (6900029055497 / 78125000000000 : ℝ) (818819618728447 / 500000000000000000 : ℝ) (330717658666419 / 10000000000000000 : ℝ)
    (cell12826 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · have h := gap_lower (n := 12826) (a := (82289716793871 / 100000000000000 : ℝ)) (b := (40144225473 / 25000000000000 : ℝ)) (q := (2236471421343 / 100000000000000 : ℝ))
      (E := (cell12826 ⟨52, by decide⟩).energy) (xi := (330717658666419 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12826 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12826]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12826])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12826) (a := (82289716793871 / 100000000000000 : ℝ)) (b := (40144225473 / 25000000000000 : ℝ)) (q := (2236471421343 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12826])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12826])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12826]

theorem cert12826_53 : CellCertificate 12826 (6900029055497 / 78125000000000 : ℝ) (818819618728447 / 500000000000000000 : ℝ) (330717658666419 / 10000000000000000 : ℝ)
    (cell12826 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · have h := gap_lower (n := 12826) (a := (16451206228119 / 20000000000000 : ℝ)) (b := (40144225473 / 25000000000000 : ℝ)) (q := (223647545717 / 10000000000000 : ℝ))
      (E := (cell12826 ⟨53, by decide⟩).energy) (xi := (330717658666419 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12826 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12826]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12826])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12826) (a := (16451206228119 / 20000000000000 : ℝ)) (b := (40144225473 / 25000000000000 : ℝ)) (q := (223647545717 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12826])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12826])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12826]

theorem cert12826_54 : CellCertificate 12826 (6900029055497 / 78125000000000 : ℝ) (818819618728447 / 500000000000000000 : ℝ) (330717658666419 / 10000000000000000 : ℝ)
    (cell12826 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · have h := gap_lower (n := 12826) (a := (82222368702323 / 100000000000000 : ℝ)) (b := (40144225473 / 25000000000000 : ℝ)) (q := (223647944701 / 10000000000000 : ℝ))
      (E := (cell12826 ⟨54, by decide⟩).energy) (xi := (330717658666419 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12826 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12826]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12826])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12826) (a := (82222368702323 / 100000000000000 : ℝ)) (b := (40144225473 / 25000000000000 : ℝ)) (q := (223647944701 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12826])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12826])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12826]

theorem cert12826_55 : CellCertificate 12826 (6900029055497 / 78125000000000 : ℝ) (818819618728447 / 500000000000000000 : ℝ) (330717658666419 / 10000000000000000 : ℝ)
    (cell12826 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · have h := gap_lower (n := 12826) (a := (82188729451191 / 100000000000000 : ℝ)) (b := (40144225473 / 25000000000000 : ℝ)) (q := (1118241723193 / 50000000000000 : ℝ))
      (E := (cell12826 ⟨55, by decide⟩).energy) (xi := (330717658666419 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12826 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12826]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12826])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12826) (a := (82188729451191 / 100000000000000 : ℝ)) (b := (40144225473 / 25000000000000 : ℝ)) (q := (1118241723193 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12826])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12826])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12826]

theorem cert12826_56 : CellCertificate 12826 (6900029055497 / 78125000000000 : ℝ) (818819618728447 / 500000000000000000 : ℝ) (330717658666419 / 10000000000000000 : ℝ)
    (cell12826 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · have h := gap_lower (n := 12826) (a := (41077556679737 / 50000000000000 : ℝ)) (b := (40144225473 / 25000000000000 : ℝ)) (q := (223648745157 / 10000000000000 : ℝ))
      (E := (cell12826 ⟨56, by decide⟩).energy) (xi := (330717658666419 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12826 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12826]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12826])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12826) (a := (41077556679737 / 50000000000000 : ℝ)) (b := (40144225473 / 25000000000000 : ℝ)) (q := (223648745157 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12826])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12826])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12826]

theorem cert12826_57 : CellCertificate 12826 (6900029055497 / 78125000000000 : ℝ) (818819618728447 / 500000000000000000 : ℝ) (330717658666419 / 10000000000000000 : ℝ)
    (cell12826 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · have h := gap_lower (n := 12826) (a := (82121520399583 / 100000000000000 : ℝ)) (b := (40144225473 / 25000000000000 : ℝ)) (q := (2236491458631 / 100000000000000 : ℝ))
      (E := (cell12826 ⟨57, by decide⟩).energy) (xi := (330717658666419 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12826 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12826]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12826])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12826) (a := (82121520399583 / 100000000000000 : ℝ)) (b := (40144225473 / 25000000000000 : ℝ)) (q := (2236491458631 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12826])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12826])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12826]

theorem cert12826_58 : CellCertificate 12826 (6900029055497 / 78125000000000 : ℝ) (818819618728447 / 500000000000000000 : ℝ) (330717658666419 / 10000000000000000 : ℝ)
    (cell12826 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · have h := gap_lower (n := 12826) (a := (82087950544069 / 100000000000000 : ℝ)) (b := (40144225473 / 25000000000000 : ℝ)) (q := (559123865857 / 25000000000000 : ℝ))
      (E := (cell12826 ⟨58, by decide⟩).energy) (xi := (330717658666419 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12826 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12826]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12826])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12826) (a := (82087950544069 / 100000000000000 : ℝ)) (b := (40144225473 / 25000000000000 : ℝ)) (q := (559123865857 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12826])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12826])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12826]

theorem cert12826_59 : CellCertificate 12826 (6900029055497 / 78125000000000 : ℝ) (818819618728447 / 500000000000000000 : ℝ) (330717658666419 / 10000000000000000 : ℝ)
    (cell12826 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · have h := gap_lower (n := 12826) (a := (41027201882809 / 50000000000000 : ℝ)) (b := (40144225473 / 25000000000000 : ℝ)) (q := (447299892323 / 20000000000000 : ℝ))
      (E := (cell12826 ⟨59, by decide⟩).energy) (xi := (330717658666419 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12826 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12826]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12826])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12826) (a := (41027201882809 / 50000000000000 : ℝ)) (b := (40144225473 / 25000000000000 : ℝ)) (q := (447299892323 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12826])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12826])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12826]

theorem cert12827_40 : CellCertificate 12827 (176635261760569 / 2000000000000000 : ℝ) (1637511524636387 / 1000000000000000000 : ℝ) (165345629903309 / 5000000000000000 : ℝ)
    (cell12827 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · have h := gap_lower (n := 12827) (a := (5168485198587 / 6250000000000 : ℝ)) (b := (160564233699 / 100000000000000 : ℝ)) (q := (17890436961 / 800000000000 : ℝ))
      (E := (cell12827 ⟨40, by decide⟩).energy) (xi := (165345629903309 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12827 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12827]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12827])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12827) (a := (5168485198587 / 6250000000000 : ℝ)) (b := (160564233699 / 100000000000000 : ℝ)) (q := (17890436961 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12827])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12827])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12827]

theorem cert12827_41 : CellCertificate 12827 (176635261760569 / 2000000000000000 : ℝ) (1637511524636387 / 1000000000000000000 : ℝ) (165345629903309 / 5000000000000000 : ℝ)
    (cell12827 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · have h := gap_lower (n := 12827) (a := (10332724627129 / 12500000000000 : ℝ)) (b := (160564233699 / 100000000000000 : ℝ)) (q := (27953857443 / 1250000000000 : ℝ))
      (E := (cell12827 ⟨41, by decide⟩).energy) (xi := (165345629903309 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12827 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12827]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12827])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12827) (a := (10332724627129 / 12500000000000 : ℝ)) (b := (160564233699 / 100000000000000 : ℝ)) (q := (27953857443 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12827])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12827])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12827]

theorem cert12827_42 : CellCertificate 12827 (176635261760569 / 2000000000000000 : ℝ) (1637511524636387 / 1000000000000000000 : ℝ) (165345629903309 / 5000000000000000 : ℝ)
    (cell12827 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · have h := gap_lower (n := 12827) (a := (10328481802097 / 12500000000000 : ℝ)) (b := (160564233699 / 100000000000000 : ℝ)) (q := (1118156305247 / 50000000000000 : ℝ))
      (E := (cell12827 ⟨42, by decide⟩).energy) (xi := (165345629903309 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12827 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12827]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12827])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12827) (a := (10328481802097 / 12500000000000 : ℝ)) (b := (160564233699 / 100000000000000 : ℝ)) (q := (1118156305247 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12827])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12827])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12827]

theorem cert12827_43 : CellCertificate 12827 (176635261760569 / 2000000000000000 : ℝ) (1637511524636387 / 1000000000000000000 : ℝ) (165345629903309 / 5000000000000000 : ℝ)
    (cell12827 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · have h := gap_lower (n := 12827) (a := (82593935347029 / 100000000000000 : ℝ)) (b := (160564233699 / 100000000000000 : ℝ)) (q := (559079151373 / 25000000000000 : ℝ))
      (E := (cell12827 ⟨43, by decide⟩).energy) (xi := (165345629903309 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12827 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12827]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12827])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12827) (a := (82593935347029 / 100000000000000 : ℝ)) (b := (160564233699 / 100000000000000 : ℝ)) (q := (559079151373 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12827])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12827])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12827]

theorem cert12827_44 : CellCertificate 12827 (176635261760569 / 2000000000000000 : ℝ) (1637511524636387 / 1000000000000000000 : ℝ) (165345629903309 / 5000000000000000 : ℝ)
    (cell12827 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · have h := gap_lower (n := 12827) (a := (10320004972293 / 12500000000000 : ℝ)) (b := (160564233699 / 100000000000000 : ℝ)) (q := (55908015951 / 2500000000000 : ℝ))
      (E := (cell12827 ⟨44, by decide⟩).energy) (xi := (165345629903309 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12827 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12827]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12827])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12827) (a := (10320004972293 / 12500000000000 : ℝ)) (b := (160564233699 / 100000000000000 : ℝ)) (q := (55908015951 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12827])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12827])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12827]

theorem cert12827_45 : CellCertificate 12827 (176635261760569 / 2000000000000000 : ℝ) (1637511524636387 / 1000000000000000000 : ℝ) (165345629903309 / 5000000000000000 : ℝ)
    (cell12827 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · have h := gap_lower (n := 12827) (a := (82526167681423 / 100000000000000 : ℝ)) (b := (160564233699 / 100000000000000 : ℝ)) (q := (2236324647863 / 100000000000000 : ℝ))
      (E := (cell12827 ⟨45, by decide⟩).energy) (xi := (165345629903309 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12827 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12827]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12827])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12827) (a := (82526167681423 / 100000000000000 : ℝ)) (b := (160564233699 / 100000000000000 : ℝ)) (q := (2236324647863 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12827])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12827])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12827]

theorem cert12827_46 : CellCertificate 12827 (176635261760569 / 2000000000000000 : ℝ) (1637511524636387 / 1000000000000000000 : ℝ) (165345629903309 / 5000000000000000 : ℝ)
    (cell12827 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · have h := gap_lower (n := 12827) (a := (41246159513557 / 50000000000000 : ℝ)) (b := (160564233699 / 100000000000000 : ℝ)) (q := (1118164316639 / 50000000000000 : ℝ))
      (E := (cell12827 ⟨46, by decide⟩).energy) (xi := (165345629903309 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12827 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12827]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12827])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12827) (a := (41246159513557 / 50000000000000 : ℝ)) (b := (160564233699 / 100000000000000 : ℝ)) (q := (1118164316639 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12827])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12827])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12827]

theorem cert12827_47 : CellCertificate 12827 (176635261760569 / 2000000000000000 : ℝ) (1637511524636387 / 1000000000000000000 : ℝ) (165345629903309 / 5000000000000000 : ℝ)
    (cell12827 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · have h := gap_lower (n := 12827) (a := (82458493786413 / 100000000000000 : ℝ)) (b := (160564233699 / 100000000000000 : ℝ)) (q := (139770790707 / 6250000000000 : ℝ))
      (E := (cell12827 ⟨47, by decide⟩).energy) (xi := (165345629903309 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12827 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12827]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12827])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12827) (a := (82458493786413 / 100000000000000 : ℝ)) (b := (160564233699 / 100000000000000 : ℝ)) (q := (139770790707 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12827])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12827])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12827]

theorem cert12827_48 : CellCertificate 12827 (176635261760569 / 2000000000000000 : ℝ) (1637511524636387 / 1000000000000000000 : ℝ) (165345629903309 / 5000000000000000 : ℝ)
    (cell12827 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · have h := gap_lower (n := 12827) (a := (82424691930461 / 100000000000000 : ℝ)) (b := (160564233699 / 100000000000000 : ℝ)) (q := (1118168320487 / 50000000000000 : ℝ))
      (E := (cell12827 ⟨48, by decide⟩).energy) (xi := (165345629903309 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12827 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12827]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12827])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12827) (a := (82424691930461 / 100000000000000 : ℝ)) (b := (160564233699 / 100000000000000 : ℝ)) (q := (1118168320487 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12827])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12827])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12827]

theorem cert12827_49 : CellCertificate 12827 (176635261760569 / 2000000000000000 : ℝ) (1637511524636387 / 1000000000000000000 : ℝ) (165345629903309 / 5000000000000000 : ℝ)
    (cell12827 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · have h := gap_lower (n := 12827) (a := (41195456715271 / 50000000000000 : ℝ)) (b := (160564233699 / 100000000000000 : ℝ)) (q := (69885645591 / 3125000000000 : ℝ))
      (E := (cell12827 ⟨49, by decide⟩).energy) (xi := (165345629903309 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12827 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12827]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12827])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12827) (a := (41195456715271 / 50000000000000 : ℝ)) (b := (160564233699 / 100000000000000 : ℝ)) (q := (69885645591 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12827])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12827])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12827]

theorem cert12827_50 : CellCertificate 12827 (176635261760569 / 2000000000000000 : ℝ) (1637511524636387 / 1000000000000000000 : ℝ) (165345629903309 / 5000000000000000 : ℝ)
    (cell12827 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · have h := gap_lower (n := 12827) (a := (41178579129043 / 50000000000000 : ℝ)) (b := (160564233699 / 100000000000000 : ℝ)) (q := (1118172321831 / 50000000000000 : ℝ))
      (E := (cell12827 ⟨50, by decide⟩).energy) (xi := (165345629903309 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12827 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12827]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12827])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12827) (a := (41178579129043 / 50000000000000 : ℝ)) (b := (160564233699 / 100000000000000 : ℝ)) (q := (1118172321831 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12827])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12827])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12827]

theorem cert12827_51 : CellCertificate 12827 (176635261760569 / 2000000000000000 : ℝ) (1637511524636387 / 1000000000000000000 : ℝ) (165345629903309 / 5000000000000000 : ℝ)
    (cell12827 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · have h := gap_lower (n := 12827) (a := (41161713192333 / 50000000000000 : ℝ)) (b := (160564233699 / 100000000000000 : ℝ)) (q := (2236348651493 / 100000000000000 : ℝ))
      (E := (cell12827 ⟨51, by decide⟩).energy) (xi := (165345629903309 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12827 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12827]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12827])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12827) (a := (41161713192333 / 50000000000000 : ℝ)) (b := (160564233699 / 100000000000000 : ℝ)) (q := (2236348651493 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12827])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12827])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12827]

theorem cert12827_52 : CellCertificate 12827 (176635261760569 / 2000000000000000 : ℝ) (1637511524636387 / 1000000000000000000 : ℝ) (165345629903309 / 5000000000000000 : ℝ)
    (cell12827 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · have h := gap_lower (n := 12827) (a := (16457943556399 / 20000000000000 : ℝ)) (b := (160564233699 / 100000000000000 : ℝ)) (q := (559088169879 / 25000000000000 : ℝ))
      (E := (cell12827 ⟨52, by decide⟩).energy) (xi := (165345629903309 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12827 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12827]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12827])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12827) (a := (16457943556399 / 20000000000000 : ℝ)) (b := (160564233699 / 100000000000000 : ℝ)) (q := (559088169879 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12827])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12827])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12827]

theorem cert12827_53 : CellCertificate 12827 (176635261760569 / 2000000000000000 : ℝ) (1637511524636387 / 1000000000000000000 : ℝ) (165345629903309 / 5000000000000000 : ℝ)
    (cell12827 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · have h := gap_lower (n := 12827) (a := (82256032421931 / 100000000000000 : ℝ)) (b := (160564233699 / 100000000000000 : ℝ)) (q := (1118178332781 / 50000000000000 : ℝ))
      (E := (cell12827 ⟨53, by decide⟩).energy) (xi := (165345629903309 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12827 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12827]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12827])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12827) (a := (82256032421931 / 100000000000000 : ℝ)) (b := (160564233699 / 100000000000000 : ℝ)) (q := (1118178332781 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12827])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12827])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12827]

theorem cert12827_54 : CellCertificate 12827 (176635261760569 / 2000000000000000 : ℝ) (1637511524636387 / 1000000000000000000 : ℝ) (165345629903309 / 5000000000000000 : ℝ)
    (cell12827 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · have h := gap_lower (n := 12827) (a := (20555592569117 / 25000000000000 : ℝ)) (b := (160564233699 / 100000000000000 : ℝ)) (q := (223636072443 / 10000000000000 : ℝ))
      (E := (cell12827 ⟨54, by decide⟩).energy) (xi := (165345629903309 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12827 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12827]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12827])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12827) (a := (20555592569117 / 25000000000000 : ℝ)) (b := (160564233699 / 100000000000000 : ℝ)) (q := (223636072443 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12827])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12827])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12827]

theorem cert12827_55 : CellCertificate 12827 (176635261760569 / 2000000000000000 : ℝ) (1637511524636387 / 1000000000000000000 : ℝ) (165345629903309 / 5000000000000000 : ℝ)
    (cell12827 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · have h := gap_lower (n := 12827) (a := (82188731317743 / 100000000000000 : ℝ)) (b := (160564233699 / 100000000000000 : ℝ)) (q := (139772795903 / 6250000000000 : ℝ))
      (E := (cell12827 ⟨55, by decide⟩).energy) (xi := (165345629903309 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12827 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12827]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12827])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12827) (a := (82188731317743 / 100000000000000 : ℝ)) (b := (160564233699 / 100000000000000 : ℝ)) (q := (139772795903 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12827])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12827])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12827]

theorem cert12827_56 : CellCertificate 12827 (176635261760569 / 2000000000000000 : ℝ) (1637511524636387 / 1000000000000000000 : ℝ) (165345629903309 / 5000000000000000 : ℝ)
    (cell12827 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · have h := gap_lower (n := 12827) (a := (5134694719877 / 6250000000000 : ℝ)) (b := (160564233699 / 100000000000000 : ℝ)) (q := (279546086477 / 12500000000000 : ℝ))
      (E := (cell12827 ⟨56, by decide⟩).energy) (xi := (165345629903309 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12827 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12827]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12827])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12827) (a := (5134694719877 / 6250000000000 : ℝ)) (b := (160564233699 / 100000000000000 : ℝ)) (q := (279546086477 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12827])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12827])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12827]

theorem cert12827_57 : CellCertificate 12827 (176635261760569 / 2000000000000000 : ℝ) (1637511524636387 / 1000000000000000000 : ℝ) (165345629903309 / 5000000000000000 : ℝ)
    (cell12827 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · have h := gap_lower (n := 12827) (a := (20530380712437 / 25000000000000 : ℝ)) (b := (160564233699 / 100000000000000 : ℝ)) (q := (34943323607 / 1562500000000 : ℝ))
      (E := (cell12827 ⟨57, by decide⟩).energy) (xi := (165345629903309 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12827 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12827]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12827])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12827) (a := (20530380712437 / 25000000000000 : ℝ)) (b := (160564233699 / 100000000000000 : ℝ)) (q := (34943323607 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12827])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12827])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12827]

theorem cert12827_58 : CellCertificate 12827 (176635261760569 / 2000000000000000 : ℝ) (1637511524636387 / 1000000000000000000 : ℝ) (165345629903309 / 5000000000000000 : ℝ)
    (cell12827 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · have h := gap_lower (n := 12827) (a := (82087953285441 / 100000000000000 : ℝ)) (b := (160564233699 / 100000000000000 : ℝ)) (q := (2236376728293 / 100000000000000 : ℝ))
      (E := (cell12827 ⟨58, by decide⟩).energy) (xi := (165345629903309 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12827 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12827]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12827])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12827) (a := (82087953285441 / 100000000000000 : ℝ)) (b := (160564233699 / 100000000000000 : ℝ)) (q := (2236376728293 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12827])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12827])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12827]

theorem cert12827_59 : CellCertificate 12827 (176635261760569 / 2000000000000000 : ℝ) (1637511524636387 / 1000000000000000000 : ℝ) (165345629903309 / 5000000000000000 : ℝ)
    (cell12827 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · have h := gap_lower (n := 12827) (a := (41027203398899 / 50000000000000 : ℝ)) (b := (160564233699 / 100000000000000 : ℝ)) (q := (2236380739803 / 100000000000000 : ℝ))
      (E := (cell12827 ⟨59, by decide⟩).energy) (xi := (165345629903309 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12827 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12827]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12827])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12827) (a := (41027203398899 / 50000000000000 : ℝ)) (b := (160564233699 / 100000000000000 : ℝ)) (q := (2236380739803 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12827])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12827])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12827]

theorem cert12828_40 : CellCertificate 12828 (883148902601309 / 10000000000000000 : ℝ) (409345957933483 / 250000000000000000 : ℝ) (330664865209131 / 10000000000000000 : ℝ)
    (cell12828 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · have h := gap_lower (n := 12828) (a := (8269576061619 / 10000000000000 : ℝ)) (b := (40137891879 / 25000000000000 : ℝ)) (q := (1118092937879 / 50000000000000 : ℝ))
      (E := (cell12828 ⟨40, by decide⟩).energy) (xi := (330664865209131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12828 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12828]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12828])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12828) (a := (8269576061619 / 10000000000000 : ℝ)) (b := (40137891879 / 25000000000000 : ℝ)) (q := (1118092937879 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12828])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12828])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12828]

theorem cert12828_41 : CellCertificate 12828 (883148902601309 / 10000000000000000 : ℝ) (409345957933483 / 250000000000000000 : ℝ) (330664865209131 / 10000000000000000 : ℝ)
    (cell12828 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · have h := gap_lower (n := 12828) (a := (2583181086059 / 3125000000000 : ℝ)) (b := (40137891879 / 25000000000000 : ℝ)) (q := (559047477751 / 25000000000000 : ℝ))
      (E := (cell12828 ⟨41, by decide⟩).energy) (xi := (330664865209131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12828 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12828]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12828])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12828) (a := (2583181086059 / 3125000000000 : ℝ)) (b := (40137891879 / 25000000000000 : ℝ)) (q := (559047477751 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12828])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12828])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12828]

theorem cert12828_42 : CellCertificate 12828 (883148902601309 / 10000000000000000 : ℝ) (409345957933483 / 250000000000000000 : ℝ) (330664865209131 / 10000000000000000 : ℝ)
    (cell12828 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · have h := gap_lower (n := 12828) (a := (82627852451279 / 100000000000000 : ℝ)) (b := (40137891879 / 25000000000000 : ℝ)) (q := (223619386911 / 10000000000000 : ℝ))
      (E := (cell12828 ⟨42, by decide⟩).energy) (xi := (330664865209131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12828 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12828]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12828])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12828) (a := (82627852451279 / 100000000000000 : ℝ)) (b := (40137891879 / 25000000000000 : ℝ)) (q := (223619386911 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12828])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12828])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12828]

theorem cert12828_43 : CellCertificate 12828 (883148902601309 / 10000000000000000 : ℝ) (409345957933483 / 250000000000000000 : ℝ) (330664865209131 / 10000000000000000 : ℝ)
    (cell12828 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · have h := gap_lower (n := 12828) (a := (82593933678769 / 100000000000000 : ℝ)) (b := (40137891879 / 25000000000000 : ℝ)) (q := (111809896273 / 5000000000000 : ℝ))
      (E := (cell12828 ⟨43, by decide⟩).energy) (xi := (330664865209131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12828 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12828]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12828])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12828) (a := (82593933678769 / 100000000000000 : ℝ)) (b := (40137891879 / 25000000000000 : ℝ)) (q := (111809896273 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12828])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12828])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12828]

theorem cert12828_44 : CellCertificate 12828 (883148902601309 / 10000000000000000 : ℝ) (409345957933483 / 250000000000000000 : ℝ) (330664865209131 / 10000000000000000 : ℝ)
    (cell12828 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · have h := gap_lower (n := 12828) (a := (82560038406911 / 100000000000000 : ℝ)) (b := (40137891879 / 25000000000000 : ℝ)) (q := (447240380477 / 20000000000000 : ℝ))
      (E := (cell12828 ⟨44, by decide⟩).energy) (xi := (330664865209131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12828 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12828]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12828])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12828) (a := (82560038406911 / 100000000000000 : ℝ)) (b := (40137891879 / 25000000000000 : ℝ)) (q := (447240380477 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12828])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12828])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12828]

theorem cert12828_45 : CellCertificate 12828 (883148902601309 / 10000000000000000 : ℝ) (409345957933483 / 250000000000000000 : ℝ) (330664865209131 / 10000000000000000 : ℝ)
    (cell12828 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · have h := gap_lower (n := 12828) (a := (82526166606409 / 100000000000000 : ℝ)) (b := (40137891879 / 25000000000000 : ℝ)) (q := (2236205916099 / 100000000000000 : ℝ))
      (E := (cell12828 ⟨45, by decide⟩).energy) (xi := (330664865209131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12828 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12828]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12828])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12828) (a := (82526166606409 / 100000000000000 : ℝ)) (b := (40137891879 / 25000000000000 : ℝ)) (q := (2236205916099 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12828])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12828])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12828]

theorem cert12828_46 : CellCertificate 12828 (883148902601309 / 10000000000000000 : ℝ) (409345957933483 / 250000000000000000 : ℝ) (330664865209131 / 10000000000000000 : ℝ)
    (cell12828 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · have h := gap_lower (n := 12828) (a := (5155769890507 / 6250000000000 : ℝ)) (b := (40137891879 / 25000000000000 : ℝ)) (q := (279526238261 / 12500000000000 : ℝ))
      (E := (cell12828 ⟨46, by decide⟩).energy) (xi := (330664865209131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12828 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12828]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12828])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12828) (a := (5155769890507 / 6250000000000 : ℝ)) (b := (40137891879 / 25000000000000 : ℝ)) (q := (279526238261 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12828])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12828])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12828]

theorem cert12828_47 : CellCertificate 12828 (883148902601309 / 10000000000000000 : ℝ) (409345957933483 / 250000000000000000 : ℝ) (330664865209131 / 10000000000000000 : ℝ)
    (cell12828 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · have h := gap_lower (n := 12828) (a := (16491698660603 / 20000000000000 : ℝ)) (b := (40137891879 / 25000000000000 : ℝ)) (q := (111810696469 / 5000000000000 : ℝ))
      (E := (cell12828 ⟨47, by decide⟩).energy) (xi := (330664865209131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12828 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12828]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12828])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12828) (a := (16491698660603 / 20000000000000 : ℝ)) (b := (40137891879 / 25000000000000 : ℝ)) (q := (111810696469 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12828])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12828])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12828]

theorem cert12828_48 : CellCertificate 12828 (883148902601309 / 10000000000000000 : ℝ) (409345957933483 / 250000000000000000 : ℝ) (330664865209131 / 10000000000000000 : ℝ)
    (cell12828 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · have h := gap_lower (n := 12828) (a := (4121234587113 / 5000000000000 : ℝ)) (b := (40137891879 / 25000000000000 : ℝ)) (q := (279527240623 / 12500000000000 : ℝ))
      (E := (cell12828 ⟨48, by decide⟩).energy) (xi := (330664865209131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12828 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12828]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12828])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12828) (a := (4121234587113 / 5000000000000 : ℝ)) (b := (40137891879 / 25000000000000 : ℝ)) (q := (279527240623 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12828])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12828])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12828]

theorem cert12828_49 : CellCertificate 12828 (883148902601309 / 10000000000000000 : ℝ) (409345957933483 / 250000000000000000 : ℝ) (330664865209131 / 10000000000000000 : ℝ)
    (cell12828 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · have h := gap_lower (n := 12828) (a := (82390913537133 / 100000000000000 : ℝ)) (b := (40137891879 / 25000000000000 : ℝ)) (q := (447244389909 / 20000000000000 : ℝ))
      (E := (cell12828 ⟨49, by decide⟩).energy) (xi := (330664865209131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12828 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12828]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12828])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12828) (a := (82390913537133 / 100000000000000 : ℝ)) (b := (40137891879 / 25000000000000 : ℝ)) (q := (447244389909 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12828])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12828])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12828]

theorem cert12828_50 : CellCertificate 12828 (883148902601309 / 10000000000000000 : ℝ) (409345957933483 / 250000000000000000 : ℝ) (330664865209131 / 10000000000000000 : ℝ)
    (cell12828 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · have h := gap_lower (n := 12828) (a := (10294644832383 / 12500000000000 : ℝ)) (b := (40137891879 / 25000000000000 : ℝ)) (q := (2795282427 / 125000000000 : ℝ))
      (E := (cell12828 ⟨50, by decide⟩).energy) (xi := (330664865209131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12828 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12828]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12828])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12828) (a := (10294644832383 / 12500000000000 : ℝ)) (b := (40137891879 / 25000000000000 : ℝ)) (q := (2795282427 / 125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12828])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12828])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12828]

theorem cert12828_51 : CellCertificate 12828 (883148902601309 / 10000000000000000 : ℝ) (409345957933483 / 250000000000000000 : ℝ) (330664865209131 / 10000000000000000 : ℝ)
    (cell12828 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · have h := gap_lower (n := 12828) (a := (41161713539813 / 50000000000000 : ℝ)) (b := (40137891879 / 25000000000000 : ℝ)) (q := (2236229957417 / 100000000000000 : ℝ))
      (E := (cell12828 ⟨51, by decide⟩).energy) (xi := (330664865209131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12828 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12828]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12828])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12828) (a := (41161713539813 / 50000000000000 : ℝ)) (b := (40137891879 / 25000000000000 : ℝ)) (q := (2236229957417 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12828])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12828])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12828]

theorem cert12828_52 : CellCertificate 12828 (883148902601309 / 10000000000000000 : ℝ) (409345957933483 / 250000000000000000 : ℝ) (330664865209131 / 10000000000000000 : ℝ)
    (cell12828 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · have h := gap_lower (n := 12828) (a := (16457943754107 / 20000000000000 : ℝ)) (b := (40137891879 / 25000000000000 : ℝ)) (q := (1118116967531 / 50000000000000 : ℝ))
      (E := (cell12828 ⟨52, by decide⟩).energy) (xi := (330664865209131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12828 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12828]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12828])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12828) (a := (16457943754107 / 20000000000000 : ℝ)) (b := (40137891879 / 25000000000000 : ℝ)) (q := (1118116967531 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12828])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12828])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12828]

theorem cert12828_53 : CellCertificate 12828 (883148902601309 / 10000000000000000 : ℝ) (409345957933483 / 250000000000000000 : ℝ) (330664865209131 / 10000000000000000 : ℝ)
    (cell12828 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · have h := gap_lower (n := 12828) (a := (41128016851823 / 50000000000000 : ℝ)) (b := (40137891879 / 25000000000000 : ℝ)) (q := (1118118994747 / 50000000000000 : ℝ))
      (E := (cell12828 ⟨53, by decide⟩).energy) (xi := (330664865209131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12828 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12828]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12828])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12828) (a := (41128016851823 / 50000000000000 : ℝ)) (b := (40137891879 / 25000000000000 : ℝ)) (q := (1118118994747 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12828])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12828])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12828]

theorem cert12828_54 : CellCertificate 12828 (883148902601309 / 10000000000000000 : ℝ) (409345957933483 / 250000000000000000 : ℝ) (330664865209131 / 10000000000000000 : ℝ)
    (cell12828 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · have h := gap_lower (n := 12828) (a := (82222371850957 / 100000000000000 : ℝ)) (b := (40137891879 / 25000000000000 : ℝ)) (q := (2236241999297 / 100000000000000 : ℝ))
      (E := (cell12828 ⟨54, by decide⟩).energy) (xi := (330664865209131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12828 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12828]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12828])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12828) (a := (82222371850957 / 100000000000000 : ℝ)) (b := (40137891879 / 25000000000000 : ℝ)) (q := (2236241999297 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12828])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12828])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12828]

theorem cert12828_55 : CellCertificate 12828 (883148902601309 / 10000000000000000 : ℝ) (409345957933483 / 250000000000000000 : ℝ) (330664865209131 / 10000000000000000 : ℝ)
    (cell12828 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · have h := gap_lower (n := 12828) (a := (16437746636921 / 20000000000000 : ℝ)) (b := (40137891879 / 25000000000000 : ℝ)) (q := (2236245960879 / 100000000000000 : ℝ))
      (E := (cell12828 ⟨55, by decide⟩).energy) (xi := (330664865209131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12828 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12828]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12828])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12828) (a := (16437746636921 / 20000000000000 : ℝ)) (b := (40137891879 / 25000000000000 : ℝ)) (q := (2236245960879 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12828])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12828])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12828]

theorem cert12828_56 : CellCertificate 12828 (883148902601309 / 10000000000000000 : ℝ) (409345957933483 / 250000000000000000 : ℝ) (330664865209131 / 10000000000000000 : ℝ)
    (cell12828 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · have h := gap_lower (n := 12828) (a := (16431023535373 / 20000000000000 : ℝ)) (b := (40137891879 / 25000000000000 : ℝ)) (q := (447249997743 / 20000000000000 : ℝ))
      (E := (cell12828 ⟨56, by decide⟩).energy) (xi := (330664865209131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12828 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12828]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12828])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12828) (a := (16431023535373 / 20000000000000 : ℝ)) (b := (40137891879 / 25000000000000 : ℝ)) (q := (447249997743 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12828])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12828])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12828]

theorem cert12828_57 : CellCertificate 12828 (883148902601309 / 10000000000000000 : ℝ) (409345957933483 / 250000000000000000 : ℝ) (330664865209131 / 10000000000000000 : ℝ)
    (cell12828 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · have h := gap_lower (n := 12828) (a := (10265190662519 / 12500000000000 : ℝ)) (b := (40137891879 / 25000000000000 : ℝ)) (q := (2236254019779 / 100000000000000 : ℝ))
      (E := (cell12828 ⟨57, by decide⟩).energy) (xi := (330664865209131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12828 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12828]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12828])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12828) (a := (10265190662519 / 12500000000000 : ℝ)) (b := (40137891879 / 25000000000000 : ℝ)) (q := (2236254019779 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12828])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12828])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12828]

theorem cert12828_58 : CellCertificate 12828 (883148902601309 / 10000000000000000 : ℝ) (409345957933483 / 250000000000000000 : ℝ) (330664865209131 / 10000000000000000 : ℝ)
    (cell12828 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · have h := gap_lower (n := 12828) (a := (82087956027017 / 100000000000000 : ℝ)) (b := (40137891879 / 25000000000000 : ℝ)) (q := (559064497687 / 25000000000000 : ℝ))
      (E := (cell12828 ⟨58, by decide⟩).energy) (xi := (330664865209131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12828 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12828]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12828])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12828) (a := (82087956027017 / 100000000000000 : ℝ)) (b := (40137891879 / 25000000000000 : ℝ)) (q := (559064497687 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12828])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12828])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12828]

theorem cert12828_59 : CellCertificate 12828 (883148902601309 / 10000000000000000 : ℝ) (409345957933483 / 250000000000000000 : ℝ) (330664865209131 / 10000000000000000 : ℝ)
    (cell12828 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · have h := gap_lower (n := 12828) (a := (82054409830147 / 100000000000000 : ℝ)) (b := (40137891879 / 25000000000000 : ℝ)) (q := (1118131007809 / 50000000000000 : ℝ))
      (E := (cell12828 ⟨59, by decide⟩).energy) (xi := (330664865209131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12828 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12828]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12828])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12828) (a := (82054409830147 / 100000000000000 : ℝ)) (b := (40137891879 / 25000000000000 : ℝ)) (q := (1118131007809 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12828])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12828])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12828]

theorem cert12829_40 : CellCertificate 12829 (883121500498043 / 10000000000000000 : ℝ) (409314039686217 / 250000000000000000 : ℝ) (330638474872847 / 10000000000000000 : ℝ)
    (cell12829 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · have h := gap_lower (n := 12829) (a := (82695758055829 / 100000000000000 : ℝ)) (b := (160538903343 / 100000000000000 : ℝ)) (q := (2236067187089 / 100000000000000 : ℝ))
      (E := (cell12829 ⟨40, by decide⟩).energy) (xi := (330638474872847 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12829 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12829]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12829])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12829) (a := (82695758055829 / 100000000000000 : ℝ)) (b := (160538903343 / 100000000000000 : ℝ)) (q := (2236067187089 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12829])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12829])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12829]

theorem cert12829_41 : CellCertificate 12829 (883121500498043 / 10000000000000000 : ℝ) (409314039686217 / 250000000000000000 : ℝ) (330638474872847 / 10000000000000000 : ℝ)
    (cell12829 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · have h := gap_lower (n := 12829) (a := (20665448122887 / 25000000000000 : ℝ)) (b := (160538903343 / 100000000000000 : ℝ)) (q := (447214244709 / 20000000000000 : ℝ))
      (E := (cell12829 ⟨41, by decide⟩).energy) (xi := (330638474872847 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12829 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12829]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12829])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12829) (a := (20665448122887 / 25000000000000 : ℝ)) (b := (160538903343 / 100000000000000 : ℝ)) (q := (447214244709 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12829])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12829])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12829]

theorem cert12829_42 : CellCertificate 12829 (883121500498043 / 10000000000000000 : ℝ) (409314039686217 / 250000000000000000 : ℝ) (330638474872847 / 10000000000000000 : ℝ)
    (cell12829 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · have h := gap_lower (n := 12829) (a := (82627850486551 / 100000000000000 : ℝ)) (b := (160538903343 / 100000000000000 : ℝ)) (q := (447215036709 / 20000000000000 : ℝ))
      (E := (cell12829 ⟨42, by decide⟩).energy) (xi := (330638474872847 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12829 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12829]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12829])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12829) (a := (82627850486551 / 100000000000000 : ℝ)) (b := (160538903343 / 100000000000000 : ℝ)) (q := (447215036709 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12829])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12829])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12829]

theorem cert12829_43 : CellCertificate 12829 (883121500498043 / 10000000000000000 : ℝ) (409314039686217 / 250000000000000000 : ℝ) (330638474872847 / 10000000000000000 : ℝ)
    (cell12829 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · have h := gap_lower (n := 12829) (a := (41296966005621 / 50000000000000 : ℝ)) (b := (160538903343 / 100000000000000 : ℝ)) (q := (1118039591823 / 50000000000000 : ℝ))
      (E := (cell12829 ⟨43, by decide⟩).energy) (xi := (330638474872847 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12829 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12829]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12829])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12829) (a := (41296966005621 / 50000000000000 : ℝ)) (b := (160538903343 / 100000000000000 : ℝ)) (q := (1118039591823 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12829])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12829])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12829]

theorem cert12829_44 : CellCertificate 12829 (883121500498043 / 10000000000000000 : ℝ) (409314039686217 / 250000000000000000 : ℝ) (330638474872847 / 10000000000000000 : ℝ)
    (cell12829 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · have h := gap_lower (n := 12829) (a := (5160002314761 / 6250000000000 : ℝ)) (b := (160538903343 / 100000000000000 : ℝ)) (q := (2236083222667 / 100000000000000 : ℝ))
      (E := (cell12829 ⟨44, by decide⟩).energy) (xi := (330638474872847 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12829 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12829]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12829])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12829) (a := (5160002314761 / 6250000000000 : ℝ)) (b := (160538903343 / 100000000000000 : ℝ)) (q := (2236083222667 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12829])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12829])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12829]

theorem cert12829_45 : CellCertificate 12829 (883121500498043 / 10000000000000000 : ℝ) (409314039686217 / 250000000000000000 : ℝ) (330638474872847 / 10000000000000000 : ℝ)
    (cell12829 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · have h := gap_lower (n := 12829) (a := (41263082766029 / 50000000000000 : ℝ)) (b := (160538903343 / 100000000000000 : ℝ)) (q := (559021810083 / 25000000000000 : ℝ))
      (E := (cell12829 ⟨45, by decide⟩).energy) (xi := (330638474872847 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12829 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12829]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12829])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12829) (a := (41263082766029 / 50000000000000 : ℝ)) (b := (160538903343 / 100000000000000 : ℝ)) (q := (559021810083 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12829])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12829])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12829]

theorem cert12829_46 : CellCertificate 12829 (883121500498043 / 10000000000000000 : ℝ) (409314039686217 / 250000000000000000 : ℝ) (330638474872847 / 10000000000000000 : ℝ)
    (cell12829 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · have h := gap_lower (n := 12829) (a := (10311539683717 / 12500000000000 : ℝ)) (b := (160538903343 / 100000000000000 : ℝ)) (q := (2236091234957 / 100000000000000 : ℝ))
      (E := (cell12829 ⟨46, by decide⟩).energy) (xi := (330638474872847 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12829 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12829]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12829])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12829) (a := (10311539683717 / 12500000000000 : ℝ)) (b := (160538903343 / 100000000000000 : ℝ)) (q := (2236091234957 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12829])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12829])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12829]

theorem cert12829_47 : CellCertificate 12829 (883121500498043 / 10000000000000000 : ℝ) (409314039686217 / 250000000000000000 : ℝ) (330638474872847 / 10000000000000000 : ℝ)
    (cell12829 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · have h := gap_lower (n := 12829) (a := (82458492820207 / 100000000000000 : ℝ)) (b := (160538903343 / 100000000000000 : ℝ)) (q := (139755953973 / 6250000000000 : ℝ))
      (E := (cell12829 ⟨47, by decide⟩).energy) (xi := (330638474872847 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12829 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12829]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12829])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12829) (a := (82458492820207 / 100000000000000 : ℝ)) (b := (160538903343 / 100000000000000 : ℝ)) (q := (139755953973 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12829])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12829])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12829]

theorem cert12829_48 : CellCertificate 12829 (883121500498043 / 10000000000000000 : ℝ) (409314039686217 / 250000000000000000 : ℝ) (330638474872847 / 10000000000000000 : ℝ)
    (cell12829 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · have h := gap_lower (n := 12829) (a := (41212345777307 / 50000000000000 : ℝ)) (b := (160538903343 / 100000000000000 : ℝ)) (q := (2236099265173 / 100000000000000 : ℝ))
      (E := (cell12829 ⟨48, by decide⟩).energy) (xi := (330638474872847 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12829 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12829]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12829])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12829) (a := (41212345777307 / 50000000000000 : ℝ)) (b := (160538903343 / 100000000000000 : ℝ)) (q := (2236099265173 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12829])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12829])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12829]

theorem cert12829_49 : CellCertificate 12829 (883121500498043 / 10000000000000000 : ℝ) (409314039686217 / 250000000000000000 : ℝ) (330638474872847 / 10000000000000000 : ℝ)
    (cell12829 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · have h := gap_lower (n := 12829) (a := (20597728411061 / 25000000000000 : ℝ)) (b := (160538903343 / 100000000000000 : ℝ)) (q := (447220647489 / 20000000000000 : ℝ))
      (E := (cell12829 ⟨49, by decide⟩).energy) (xi := (330638474872847 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12829 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12829]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12829])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12829) (a := (20597728411061 / 25000000000000 : ℝ)) (b := (160538903343 / 100000000000000 : ℝ)) (q := (447220647489 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12829])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12829])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12829]

theorem cert12829_50 : CellCertificate 12829 (883121500498043 / 10000000000000000 : ℝ) (409314039686217 / 250000000000000000 : ℝ) (330638474872847 / 10000000000000000 : ℝ)
    (cell12829 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · have h := gap_lower (n := 12829) (a := (82357159060527 / 100000000000000 : ℝ)) (b := (160538903343 / 100000000000000 : ℝ)) (q := (55902680921 / 2500000000000 : ℝ))
      (E := (cell12829 ⟨50, by decide⟩).energy) (xi := (330638474872847 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12829 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12829]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12829])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12829) (a := (82357159060527 / 100000000000000 : ℝ)) (b := (160538903343 / 100000000000000 : ℝ)) (q := (55902680921 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12829])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12829])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12829]

theorem cert12829_51 : CellCertificate 12829 (883121500498043 / 10000000000000000 : ℝ) (409314039686217 / 250000000000000000 : ℝ) (330638474872847 / 10000000000000000 : ℝ)
    (cell12829 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · have h := gap_lower (n := 12829) (a := (20580856943759 / 25000000000000 : ℝ)) (b := (160538903343 / 100000000000000 : ℝ)) (q := (1118055630339 / 50000000000000 : ℝ))
      (E := (cell12829 ⟨51, by decide⟩).energy) (xi := (330638474872847 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12829 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12829]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12829])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12829) (a := (20580856943759 / 25000000000000 : ℝ)) (b := (160538903343 / 100000000000000 : ℝ)) (q := (1118055630339 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12829])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12829])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12829]

theorem cert12829_52 : CellCertificate 12829 (883121500498043 / 10000000000000000 : ℝ) (409314039686217 / 250000000000000000 : ℝ) (330638474872847 / 10000000000000000 : ℝ)
    (cell12829 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · have h := gap_lower (n := 12829) (a := (642888435621 / 781250000000 : ℝ)) (b := (160538903343 / 100000000000000 : ℝ)) (q := (89444609881 / 4000000000000 : ℝ))
      (E := (cell12829 ⟨52, by decide⟩).energy) (xi := (330638474872847 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12829 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12829]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12829])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12829) (a := (642888435621 / 781250000000 : ℝ)) (b := (160538903343 / 100000000000000 : ℝ)) (q := (89444609881 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12829])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12829])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12829]

theorem cert12829_53 : CellCertificate 12829 (883121500498043 / 10000000000000000 : ℝ) (409314039686217 / 250000000000000000 : ℝ) (330638474872847 / 10000000000000000 : ℝ)
    (cell12829 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · have h := gap_lower (n := 12829) (a := (4112801749287 / 5000000000000 : ℝ)) (b := (160538903343 / 100000000000000 : ℝ)) (q := (2236119251773 / 100000000000000 : ℝ))
      (E := (cell12829 ⟨53, by decide⟩).energy) (xi := (330638474872847 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12829 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12829]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12829])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12829) (a := (4112801749287 / 5000000000000 : ℝ)) (b := (160538903343 / 100000000000000 : ℝ)) (q := (2236119251773 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12829])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12829])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12829]

theorem cert12829_54 : CellCertificate 12829 (883121500498043 / 10000000000000000 : ℝ) (409314039686217 / 250000000000000000 : ℝ) (330638474872847 / 10000000000000000 : ℝ)
    (cell12829 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · have h := gap_lower (n := 12829) (a := (8222237342579 / 10000000000000 : ℝ)) (b := (160538903343 / 100000000000000 : ℝ)) (q := (2236123271611 / 100000000000000 : ℝ))
      (E := (cell12829 ⟨54, by decide⟩).energy) (xi := (330638474872847 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12829 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12829]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12829])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12829) (a := (8222237342579 / 10000000000000 : ℝ)) (b := (160538903343 / 100000000000000 : ℝ)) (q := (2236123271611 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12829])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12829])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12829]

theorem cert12829_55 : CellCertificate 12829 (883121500498043 / 10000000000000000 : ℝ) (409314039686217 / 250000000000000000 : ℝ) (330638474872847 / 10000000000000000 : ℝ)
    (cell12829 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · have h := gap_lower (n := 12829) (a := (3287549402071 / 4000000000000 : ℝ)) (b := (160538903343 / 100000000000000 : ℝ)) (q := (1118063651509 / 50000000000000 : ℝ))
      (E := (cell12829 ⟨55, by decide⟩).energy) (xi := (330638474872847 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12829 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12829]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12829])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12829) (a := (3287549402071 / 4000000000000 : ℝ)) (b := (160538903343 / 100000000000000 : ℝ)) (q := (1118063651509 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12829])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12829])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12829]

theorem cert12829_56 : CellCertificate 12829 (883121500498043 / 10000000000000000 : ℝ) (409314039686217 / 250000000000000000 : ℝ) (330638474872847 / 10000000000000000 : ℝ)
    (cell12829 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · have h := gap_lower (n := 12829) (a := (20538779958993 / 25000000000000 : ℝ)) (b := (160538903343 / 100000000000000 : ℝ)) (q := (559032820783 / 25000000000000 : ℝ))
      (E := (cell12829 ⟨56, by decide⟩).energy) (xi := (330638474872847 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12829 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12829]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12829])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12829) (a := (20538779958993 / 25000000000000 : ℝ)) (b := (160538903343 / 100000000000000 : ℝ)) (q := (559032820783 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12829])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12829])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12829]

theorem cert12829_57 : CellCertificate 12829 (883121500498043 / 10000000000000000 : ℝ) (409314039686217 / 250000000000000000 : ℝ) (330638474872847 / 10000000000000000 : ℝ)
    (cell12829 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · have h := gap_lower (n := 12829) (a := (20530381937699 / 25000000000000 : ℝ)) (b := (160538903343 / 100000000000000 : ℝ)) (q := (1118067663131 / 50000000000000 : ℝ))
      (E := (cell12829 ⟨57, by decide⟩).energy) (xi := (330638474872847 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12829 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12829]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12829])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12829) (a := (20530381937699 / 25000000000000 : ℝ)) (b := (160538903343 / 100000000000000 : ℝ)) (q := (1118067663131 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12829])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12829])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12829]

theorem cert12829_58 : CellCertificate 12829 (883121500498043 / 10000000000000000 : ℝ) (409314039686217 / 250000000000000000 : ℝ) (330638474872847 / 10000000000000000 : ℝ)
    (cell12829 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · have h := gap_lower (n := 12829) (a := (82087958768797 / 100000000000000 : ℝ)) (b := (160538903343 / 100000000000000 : ℝ)) (q := (279517413747 / 12500000000000 : ℝ))
      (E := (cell12829 ⟨58, by decide⟩).energy) (xi := (330638474872847 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12829 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12829]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12829])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12829) (a := (82087958768797 / 100000000000000 : ℝ)) (b := (160538903343 / 100000000000000 : ℝ)) (q := (279517413747 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12829])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12829])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12829]

theorem cert12829_59 : CellCertificate 12829 (883121500498043 / 10000000000000000 : ℝ) (409314039686217 / 250000000000000000 : ℝ) (330638474872847 / 10000000000000000 : ℝ)
    (cell12829 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · have h := gap_lower (n := 12829) (a := (41027206431333 / 50000000000000 : ℝ)) (b := (160538903343 / 100000000000000 : ℝ)) (q := (279517918533 / 12500000000000 : ℝ))
      (E := (cell12829 ⟨59, by decide⟩).energy) (xi := (330638474872847 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12829 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12829]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12829])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12829) (a := (41027206431333 / 50000000000000 : ℝ)) (b := (160538903343 / 100000000000000 : ℝ)) (q := (279517918533 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12829])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12829])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12829]

theorem cert12830_40 : CellCertificate 12830 (220773525623021 / 2500000000000000 : ℝ) (1637128505664539 / 1000000000000000000 : ℝ) (20663255549791 / 625000000000000 : ℝ)
    (cell12830 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · have h := gap_lower (n := 12830) (a := (82695755496307 / 100000000000000 : ℝ)) (b := (8026312059 / 5000000000000 : ℝ)) (q := (55898713853 / 2500000000000 : ℝ))
      (E := (cell12830 ⟨40, by decide⟩).energy) (xi := (20663255549791 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12830 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12830]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12830])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12830) (a := (82695755496307 / 100000000000000 : ℝ)) (b := (8026312059 / 5000000000000 : ℝ)) (q := (55898713853 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12830])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12830])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12830]

theorem cert12830_41 : CellCertificate 12830 (220773525623021 / 2500000000000000 : ℝ) (1637128505664539 / 1000000000000000000 : ℝ) (20663255549791 / 625000000000000 : ℝ)
    (cell12830 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · have h := gap_lower (n := 12830) (a := (82661790230013 / 100000000000000 : ℝ)) (b := (8026312059 / 5000000000000 : ℝ)) (q := (111797626653 / 5000000000000 : ℝ))
      (E := (cell12830 ⟨41, by decide⟩).energy) (xi := (20663255549791 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12830 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12830]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12830])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12830) (a := (82661790230013 / 100000000000000 : ℝ)) (b := (8026312059 / 5000000000000 : ℝ)) (q := (111797626653 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12830])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12830])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12830]

theorem cert12830_42 : CellCertificate 12830 (220773525623021 / 2500000000000000 : ℝ) (1637128505664539 / 1000000000000000000 : ℝ) (20663255549791 / 625000000000000 : ℝ)
    (cell12830 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · have h := gap_lower (n := 12830) (a := (82627848522591 / 100000000000000 : ℝ)) (b := (8026312059 / 5000000000000 : ℝ)) (q := (2235956553799 / 100000000000000 : ℝ))
      (E := (cell12830 ⟨42, by decide⟩).energy) (xi := (20663255549791 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12830 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12830]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12830])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12830) (a := (82627848522591 / 100000000000000 : ℝ)) (b := (8026312059 / 5000000000000 : ℝ)) (q := (2235956553799 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12830])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12830])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12830]

theorem cert12830_43 : CellCertificate 12830 (220773525623021 / 2500000000000000 : ℝ) (1637128505664539 / 1000000000000000000 : ℝ) (20663255549791 / 625000000000000 : ℝ)
    (cell12830 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · have h := gap_lower (n := 12830) (a := (82593930344447 / 100000000000000 : ℝ)) (b := (8026312059 / 5000000000000 : ℝ)) (q := (1117980278271 / 50000000000000 : ℝ))
      (E := (cell12830 ⟨43, by decide⟩).energy) (xi := (20663255549791 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12830 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12830]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12830])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12830) (a := (82593930344447 / 100000000000000 : ℝ)) (b := (8026312059 / 5000000000000 : ℝ)) (q := (1117980278271 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12830])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12830])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12830]

theorem cert12830_44 : CellCertificate 12830 (220773525623021 / 2500000000000000 : ℝ) (1637128505664539 / 1000000000000000000 : ℝ) (20663255549791 / 625000000000000 : ℝ)
    (cell12830 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · have h := gap_lower (n := 12830) (a := (41280017833069 / 50000000000000 : ℝ)) (b := (8026312059 / 5000000000000 : ℝ)) (q := (558991135009 / 25000000000000 : ℝ))
      (E := (cell12830 ⟨44, by decide⟩).energy) (xi := (20663255549791 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12830 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12830]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12830])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12830) (a := (41280017833069 / 50000000000000 : ℝ)) (b := (8026312059 / 5000000000000 : ℝ)) (q := (558991135009 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12830])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12830])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12830]

theorem cert12830_45 : CellCertificate 12830 (220773525623021 / 2500000000000000 : ℝ) (1637128505664539 / 1000000000000000000 : ℝ) (20663255549791 / 625000000000000 : ℝ)
    (cell12830 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · have h := gap_lower (n := 12830) (a := (644735659831 / 781250000000 : ℝ)) (b := (8026312059 / 5000000000000 : ℝ)) (q := (279496070211 / 12500000000000 : ℝ))
      (E := (cell12830 ⟨45, by decide⟩).energy) (xi := (20663255549791 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12830 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12830]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12830])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12830) (a := (644735659831 / 781250000000 : ℝ)) (b := (8026312059 / 5000000000000 : ℝ)) (q := (279496070211 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12830])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12830])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12830]

theorem cert12830_46 : CellCertificate 12830 (220773525623021 / 2500000000000000 : ℝ) (1637128505664539 / 1000000000000000000 : ℝ) (20663255549791 / 625000000000000 : ℝ)
    (cell12830 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · have h := gap_lower (n := 12830) (a := (41246158345993 / 50000000000000 : ℝ)) (b := (8026312059 / 5000000000000 : ℝ)) (q := (279496570123 / 12500000000000 : ℝ))
      (E := (cell12830 ⟨46, by decide⟩).energy) (xi := (20663255549791 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12830 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12830]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12830])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12830) (a := (41246158345993 / 50000000000000 : ℝ)) (b := (8026312059 / 5000000000000 : ℝ)) (q := (279496570123 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12830])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12830])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12830]

theorem cert12830_47 : CellCertificate 12830 (220773525623021 / 2500000000000000 : ℝ) (1637128505664539 / 1000000000000000000 : ℝ) (20663255549791 / 625000000000000 : ℝ)
    (cell12830 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · have h := gap_lower (n := 12830) (a := (8245849233799 / 10000000000000 : ℝ)) (b := (8026312059 / 5000000000000 : ℝ)) (q := (44719531899 / 2000000000000 : ℝ))
      (E := (cell12830 ⟨47, by decide⟩).energy) (xi := (20663255549791 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12830 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12830]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12830])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12830) (a := (8245849233799 / 10000000000000 : ℝ)) (b := (8026312059 / 5000000000000 : ℝ)) (q := (44719531899 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12830])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12830])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12830]

theorem cert12830_48 : CellCertificate 12830 (220773525623021 / 2500000000000000 : ℝ) (1637128505664539 / 1000000000000000000 : ℝ) (20663255549791 / 625000000000000 : ℝ)
    (cell12830 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · have h := gap_lower (n := 12830) (a := (20606172841881 / 25000000000000 : ℝ)) (b := (8026312059 / 5000000000000 : ℝ)) (q := (69874393831 / 3125000000000 : ℝ))
      (E := (cell12830 ⟨48, by decide⟩).energy) (xi := (20663255549791 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12830 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12830]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12830])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12830) (a := (20606172841881 / 25000000000000 : ℝ)) (b := (8026312059 / 5000000000000 : ℝ)) (q := (69874393831 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12830])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12830])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12830]

theorem cert12830_49 : CellCertificate 12830 (220773525623021 / 2500000000000000 : ℝ) (1637128505664539 / 1000000000000000000 : ℝ) (20663255549791 / 625000000000000 : ℝ)
    (cell12830 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · have h := gap_lower (n := 12830) (a := (131825462003 / 160000000000 : ℝ)) (b := (8026312059 / 5000000000000 : ℝ)) (q := (2235984581583 / 100000000000000 : ℝ))
      (E := (cell12830 ⟨49, by decide⟩).energy) (xi := (20663255549791 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12830 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12830]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12830])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12830) (a := (131825462003 / 160000000000 : ℝ)) (b := (8026312059 / 5000000000000 : ℝ)) (q := (2235984581583 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12830])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12830])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12830]

theorem cert12830_50 : CellCertificate 12830 (220773525623021 / 2500000000000000 : ℝ) (1637128505664539 / 1000000000000000000 : ℝ) (20663255549791 / 625000000000000 : ℝ)
    (cell12830 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · have h := gap_lower (n := 12830) (a := (41178579731237 / 50000000000000 : ℝ)) (b := (8026312059 / 5000000000000 : ℝ)) (q := (1117994294189 / 50000000000000 : ℝ))
      (E := (cell12830 ⟨50, by decide⟩).energy) (xi := (20663255549791 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12830 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12830]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12830])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12830) (a := (41178579731237 / 50000000000000 : ℝ)) (b := (8026312059 / 5000000000000 : ℝ)) (q := (1117994294189 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12830])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12830])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12830]

theorem cert12830_51 : CellCertificate 12830 (220773525623021 / 2500000000000000 : ℝ) (1637128505664539 / 1000000000000000000 : ℝ) (20663255549791 / 625000000000000 : ℝ)
    (cell12830 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · have h := gap_lower (n := 12830) (a := (16464685694179 / 20000000000000 : ℝ)) (b := (8026312059 / 5000000000000 : ℝ)) (q := (2235992620297 / 100000000000000 : ℝ))
      (E := (cell12830 ⟨51, by decide⟩).energy) (xi := (20663255549791 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12830 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12830]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12830])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12830) (a := (16464685694179 / 20000000000000 : ℝ)) (b := (8026312059 / 5000000000000 : ℝ)) (q := (2235992620297 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12830])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12830])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12830]

theorem cert12830_52 : CellCertificate 12830 (220773525623021 / 2500000000000000 : ℝ) (1637128505664539 / 1000000000000000000 : ℝ) (20663255549791 / 625000000000000 : ℝ)
    (cell12830 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · have h := gap_lower (n := 12830) (a := (10286215093607 / 12500000000000 : ℝ)) (b := (8026312059 / 5000000000000 : ℝ)) (q := (558999153851 / 25000000000000 : ℝ))
      (E := (cell12830 ⟨52, by decide⟩).energy) (xi := (20663255549791 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12830 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12830]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12830])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12830) (a := (10286215093607 / 12500000000000 : ℝ)) (b := (8026312059 / 5000000000000 : ℝ)) (q := (558999153851 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12830])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12830])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12830]

theorem cert12830_53 : CellCertificate 12830 (220773525623021 / 2500000000000000 : ℝ) (1637128505664539 / 1000000000000000000 : ℝ) (20663255549791 / 625000000000000 : ℝ)
    (cell12830 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · have h := gap_lower (n := 12830) (a := (41128018134107 / 50000000000000 : ℝ)) (b := (8026312059 / 5000000000000 : ℝ)) (q := (2236000629591 / 100000000000000 : ℝ))
      (E := (cell12830 ⟨53, by decide⟩).energy) (xi := (20663255549791 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12830 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12830]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12830])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12830) (a := (41128018134107 / 50000000000000 : ℝ)) (b := (8026312059 / 5000000000000 : ℝ)) (q := (2236000629591 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12830])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12830])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12830]

theorem cert12830_54 : CellCertificate 12830 (220773525623021 / 2500000000000000 : ℝ) (1637128505664539 / 1000000000000000000 : ℝ) (20663255549791 / 625000000000000 : ℝ)
    (cell12830 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · have h := gap_lower (n := 12830) (a := (10277796875121 / 12500000000000 : ℝ)) (b := (8026312059 / 5000000000000 : ℝ)) (q := (2236004600459 / 100000000000000 : ℝ))
      (E := (cell12830 ⟨54, by decide⟩).energy) (xi := (20663255549791 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12830 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12830]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12830])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12830) (a := (10277796875121 / 12500000000000 : ℝ)) (b := (8026312059 / 5000000000000 : ℝ)) (q := (2236004600459 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12830])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12830])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12830]

theorem cert12830_55 : CellCertificate 12830 (220773525623021 / 2500000000000000 : ℝ) (1637128505664539 / 1000000000000000000 : ℝ) (20663255549791 / 625000000000000 : ℝ)
    (cell12830 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · have h := gap_lower (n := 12830) (a := (16437747383851 / 20000000000000 : ℝ)) (b := (8026312059 / 5000000000000 : ℝ)) (q := (2236008642639 / 100000000000000 : ℝ))
      (E := (cell12830 ⟨55, by decide⟩).energy) (xi := (20663255549791 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12830 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12830]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12830])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12830) (a := (16437747383851 / 20000000000000 : ℝ)) (b := (8026312059 / 5000000000000 : ℝ)) (q := (2236008642639 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12830])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12830])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12830]

theorem cert12830_56 : CellCertificate 12830 (220773525623021 / 2500000000000000 : ℝ) (1637128505664539 / 1000000000000000000 : ℝ) (20663255549791 / 625000000000000 : ℝ)
    (cell12830 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · have h := gap_lower (n := 12830) (a := (41077560997677 / 50000000000000 : ℝ)) (b := (8026312059 / 5000000000000 : ℝ)) (q := (1118006317101 / 50000000000000 : ℝ))
      (E := (cell12830 ⟨56, by decide⟩).energy) (xi := (20663255549791 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12830 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12830]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12830])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12830) (a := (41077560997677 / 50000000000000 : ℝ)) (b := (8026312059 / 5000000000000 : ℝ)) (q := (1118006317101 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12830])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12830])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12830]

theorem cert12830_57 : CellCertificate 12830 (220773525623021 / 2500000000000000 : ℝ) (1637128505664539 / 1000000000000000000 : ℝ) (20663255549791 / 625000000000000 : ℝ)
    (cell12830 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · have h := gap_lower (n := 12830) (a := (41060765100839 / 50000000000000 : ℝ)) (b := (8026312059 / 5000000000000 : ℝ)) (q := (2236016630301 / 100000000000000 : ℝ))
      (E := (cell12830 ⟨57, by decide⟩).energy) (xi := (20663255549791 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12830 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12830]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12830])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12830) (a := (41060765100839 / 50000000000000 : ℝ)) (b := (8026312059 / 5000000000000 : ℝ)) (q := (2236016630301 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12830])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12830])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12830]

theorem cert12830_58 : CellCertificate 12830 (220773525623021 / 2500000000000000 : ℝ) (1637128505664539 / 1000000000000000000 : ℝ) (20663255549791 / 625000000000000 : ℝ)
    (cell12830 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · have h := gap_lower (n := 12830) (a := (41043980755391 / 50000000000000 : ℝ)) (b := (8026312059 / 5000000000000 : ℝ)) (q := (89440827439 / 4000000000000 : ℝ))
      (E := (cell12830 ⟨58, by decide⟩).energy) (xi := (20663255549791 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12830 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12830]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12830])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12830) (a := (41043980755391 / 50000000000000 : ℝ)) (b := (8026312059 / 5000000000000 : ℝ)) (q := (89440827439 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12830])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12830])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12830]

theorem cert12830_59 : CellCertificate 12830 (220773525623021 / 2500000000000000 : ℝ) (1637128505664539 / 1000000000000000000 : ℝ) (20663255549791 / 625000000000000 : ℝ)
    (cell12830 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · have h := gap_lower (n := 12830) (a := (16410883179071 / 20000000000000 : ℝ)) (b := (8026312059 / 5000000000000 : ℝ)) (q := (1118012339267 / 50000000000000 : ℝ))
      (E := (cell12830 ⟨59, by decide⟩).energy) (xi := (20663255549791 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12830 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12830]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12830])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12830) (a := (16410883179071 / 20000000000000 : ℝ)) (b := (8026312059 / 5000000000000 : ℝ)) (q := (1118012339267 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12830])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12830])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12830]

theorem cert12831_40 : CellCertificate 12831 (220766677145617 / 2500000000000000 : ℝ) (51156277265259 / 31250000000000000 : ℝ) (330585706979449 / 10000000000000000 : ℝ)
    (cell12831 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · have h := gap_lower (n := 12831) (a := (661566023501 / 800000000000 : ℝ)) (b := (80256790513 / 50000000000000 : ℝ)) (q := (558957479523 / 25000000000000 : ℝ))
      (E := (cell12831 ⟨40, by decide⟩).energy) (xi := (330585706979449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12831 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12831]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12831])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12831) (a := (661566023501 / 800000000000 : ℝ)) (b := (80256790513 / 50000000000000 : ℝ)) (q := (558957479523 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12831])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12831])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12831]

theorem cert12831_41 : CellCertificate 12831 (220766677145617 / 2500000000000000 : ℝ) (51156277265259 / 31250000000000000 : ℝ) (330585706979449 / 10000000000000000 : ℝ)
    (cell12831 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · have h := gap_lower (n := 12831) (a := (82661787969281 / 100000000000000 : ℝ)) (b := (80256790513 / 50000000000000 : ℝ)) (q := (2235833898337 / 100000000000000 : ℝ))
      (E := (cell12831 ⟨41, by decide⟩).energy) (xi := (330585706979449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12831 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12831]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12831])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12831) (a := (82661787969281 / 100000000000000 : ℝ)) (b := (80256790513 / 50000000000000 : ℝ)) (q := (2235833898337 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12831])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12831])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12831]

theorem cert12831_42 : CellCertificate 12831 (220766677145617 / 2500000000000000 : ℝ) (51156277265259 / 31250000000000000 : ℝ) (330585706979449 / 10000000000000000 : ℝ)
    (cell12831 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · have h := gap_lower (n := 12831) (a := (82627846559399 / 100000000000000 : ℝ)) (b := (80256790513 / 50000000000000 : ℝ)) (q := (558959480267 / 25000000000000 : ℝ))
      (E := (cell12831 ⟨42, by decide⟩).energy) (xi := (330585706979449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12831 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12831]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12831])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12831) (a := (82627846559399 / 100000000000000 : ℝ)) (b := (80256790513 / 50000000000000 : ℝ)) (q := (558959480267 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12831])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12831])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12831]

theorem cert12831_43 : CellCertificate 12831 (220766677145617 / 2500000000000000 : ℝ) (51156277265259 / 31250000000000000 : ℝ) (330585706979449 / 10000000000000000 : ℝ)
    (cell12831 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · have h := gap_lower (n := 12831) (a := (41296964339193 / 50000000000000 : ℝ)) (b := (80256790513 / 50000000000000 : ℝ)) (q := (2235841926487 / 100000000000000 : ℝ))
      (E := (cell12831 ⟨43, by decide⟩).energy) (xi := (330585706979449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12831 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12831]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12831])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12831) (a := (41296964339193 / 50000000000000 : ℝ)) (b := (80256790513 / 50000000000000 : ℝ)) (q := (2235841926487 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12831])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12831])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12831]

theorem cert12831_44 : CellCertificate 12831 (220766677145617 / 2500000000000000 : ℝ) (51156277265259 / 31250000000000000 : ℝ) (330585706979449 / 10000000000000000 : ℝ)
    (cell12831 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · have h := gap_lower (n := 12831) (a := (41280017148399 / 50000000000000 : ℝ)) (b := (80256790513 / 50000000000000 : ℝ)) (q := (2235845913343 / 100000000000000 : ℝ))
      (E := (cell12831 ⟨44, by decide⟩).energy) (xi := (330585706979449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12831 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12831]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12831])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12831) (a := (41280017148399 / 50000000000000 : ℝ)) (b := (80256790513 / 50000000000000 : ℝ)) (q := (2235845913343 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12831])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12831])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12831]

theorem cert12831_45 : CellCertificate 12831 (220766677145617 / 2500000000000000 : ℝ) (51156277265259 / 31250000000000000 : ℝ) (330585706979449 / 10000000000000000 : ℝ)
    (cell12831 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · have h := gap_lower (n := 12831) (a := (82526163385339 / 100000000000000 : ℝ)) (b := (80256790513 / 50000000000000 : ℝ)) (q := (558962484761 / 25000000000000 : ℝ))
      (E := (cell12831 ⟨45, by decide⟩).energy) (xi := (330585706979449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12831 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12831]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12831])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12831) (a := (82526163385339 / 100000000000000 : ℝ)) (b := (80256790513 / 50000000000000 : ℝ)) (q := (558962484761 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12831])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12831])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12831]

theorem cert12831_46 : CellCertificate 12831 (220766677145617 / 2500000000000000 : ℝ) (51156277265259 / 31250000000000000 : ℝ) (330585706979449 / 10000000000000000 : ℝ)
    (cell12831 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · have h := gap_lower (n := 12831) (a := (41246157957431 / 50000000000000 : ℝ)) (b := (80256790513 / 50000000000000 : ℝ)) (q := (69870435721 / 3125000000000 : ℝ))
      (E := (cell12831 ⟨46, by decide⟩).energy) (xi := (330585706979449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12831 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12831]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12831])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12831) (a := (41246157957431 / 50000000000000 : ℝ)) (b := (80256790513 / 50000000000000 : ℝ)) (q := (69870435721 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12831])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12831])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12831]

theorem cert12831_47 : CellCertificate 12831 (220766677145617 / 2500000000000000 : ℝ) (51156277265259 / 31250000000000000 : ℝ) (330585706979449 / 10000000000000000 : ℝ)
    (cell12831 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · have h := gap_lower (n := 12831) (a := (20614622964091 / 25000000000000 : ℝ)) (b := (80256790513 / 50000000000000 : ℝ)) (q := (2235857923527 / 100000000000000 : ℝ))
      (E := (cell12831 ⟨47, by decide⟩).energy) (xi := (330585706979449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12831 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12831]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12831])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12831) (a := (20614622964091 / 25000000000000 : ℝ)) (b := (80256790513 / 50000000000000 : ℝ)) (q := (2235857923527 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12831])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12831])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12831]

theorem cert12831_48 : CellCertificate 12831 (220766677145617 / 2500000000000000 : ℝ) (51156277265259 / 31250000000000000 : ℝ) (330585706979449 / 10000000000000000 : ℝ)
    (cell12831 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · have h := gap_lower (n := 12831) (a := (82424691180989 / 100000000000000 : ℝ)) (b := (80256790513 / 50000000000000 : ℝ)) (q := (2235861937243 / 100000000000000 : ℝ))
      (E := (cell12831 ⟨48, by decide⟩).energy) (xi := (330585706979449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12831 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12831]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12831])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12831) (a := (82424691180989 / 100000000000000 : ℝ)) (b := (80256790513 / 50000000000000 : ℝ)) (q := (2235861937243 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12831])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12831])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12831]

theorem cert12831_49 : CellCertificate 12831 (220766677145617 / 2500000000000000 : ℝ) (51156277265259 / 31250000000000000 : ℝ) (330585706979449 / 10000000000000000 : ℝ)
    (cell12831 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · have h := gap_lower (n := 12831) (a := (41195456930013 / 50000000000000 : ℝ)) (b := (80256790513 / 50000000000000 : ℝ)) (q := (55896649549 / 2500000000000 : ℝ))
      (E := (cell12831 ⟨49, by decide⟩).energy) (xi := (330585706979449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12831 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12831]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12831])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12831) (a := (41195456930013 / 50000000000000 : ℝ)) (b := (80256790513 / 50000000000000 : ℝ)) (q := (55896649549 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12831])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12831])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12831]

theorem cert12831_50 : CellCertificate 12831 (220766677145617 / 2500000000000000 : ℝ) (51156277265259 / 31250000000000000 : ℝ) (330585706979449 / 10000000000000000 : ℝ)
    (cell12831 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · have h := gap_lower (n := 12831) (a := (41178579932453 / 50000000000000 : ℝ)) (b := (80256790513 / 50000000000000 : ℝ)) (q := (2235869937221 / 100000000000000 : ℝ))
      (E := (cell12831 ⟨50, by decide⟩).energy) (xi := (330585706979449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12831 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12831]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12831])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12831) (a := (41178579932453 / 50000000000000 : ℝ)) (b := (80256790513 / 50000000000000 : ℝ)) (q := (2235869937221 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12831])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12831])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12831]

theorem cert12831_51 : CellCertificate 12831 (220766677145617 / 2500000000000000 : ℝ) (51156277265259 / 31250000000000000 : ℝ) (330585706979449 / 10000000000000000 : ℝ)
    (cell12831 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · have h := gap_lower (n := 12831) (a := (20580857291801 / 25000000000000 : ℝ)) (b := (80256790513 / 50000000000000 : ℝ)) (q := (279484247157 / 12500000000000 : ℝ))
      (E := (cell12831 ⟨51, by decide⟩).energy) (xi := (330585706979449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12831 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12831]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12831])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12831) (a := (20580857291801 / 25000000000000 : ℝ)) (b := (80256790513 / 50000000000000 : ℝ)) (q := (279484247157 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12831])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12831])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12831]

theorem cert12831_52 : CellCertificate 12831 (220766677145617 / 2500000000000000 : ℝ) (51156277265259 / 31250000000000000 : ℝ) (330585706979449 / 10000000000000000 : ℝ)
    (cell12831 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · have h := gap_lower (n := 12831) (a := (41144860869319 / 50000000000000 : ℝ)) (b := (80256790513 / 50000000000000 : ℝ)) (q := (55896949529 / 2500000000000 : ℝ))
      (E := (cell12831 ⟨52, by decide⟩).energy) (xi := (330585706979449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12831 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12831]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12831])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12831) (a := (41144860869319 / 50000000000000 : ℝ)) (b := (80256790513 / 50000000000000 : ℝ)) (q := (55896949529 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12831])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12831])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12831]

theorem cert12831_53 : CellCertificate 12831 (220766677145617 / 2500000000000000 : ℝ) (51156277265259 / 31250000000000000 : ℝ) (330585706979449 / 10000000000000000 : ℝ)
    (cell12831 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · have h := gap_lower (n := 12831) (a := (82256037551067 / 100000000000000 : ℝ)) (b := (80256790513 / 50000000000000 : ℝ)) (q := (1117941002411 / 50000000000000 : ℝ))
      (E := (cell12831 ⟨53, by decide⟩).energy) (xi := (330585706979449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12831 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12831]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12831])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12831) (a := (82256037551067 / 100000000000000 : ℝ)) (b := (80256790513 / 50000000000000 : ℝ)) (q := (1117941002411 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12831])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12831])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12831]

theorem cert12831_54 : CellCertificate 12831 (220766677145617 / 2500000000000000 : ℝ) (51156277265259 / 31250000000000000 : ℝ) (330585706979449 / 10000000000000000 : ℝ)
    (cell12831 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · have h := gap_lower (n := 12831) (a := (82222376576489 / 100000000000000 : ℝ)) (b := (80256790513 / 50000000000000 : ℝ)) (q := (558971496461 / 25000000000000 : ℝ))
      (E := (cell12831 ⟨54, by decide⟩).energy) (xi := (330585706979449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12831 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12831]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12831])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12831) (a := (82222376576489 / 100000000000000 : ℝ)) (b := (80256790513 / 50000000000000 : ℝ)) (q := (558971496461 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12831])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12831])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12831]

theorem cert12831_55 : CellCertificate 12831 (220766677145617 / 2500000000000000 : ℝ) (51156277265259 / 31250000000000000 : ℝ) (330585706979449 / 10000000000000000 : ℝ)
    (cell12831 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · have h := gap_lower (n := 12831) (a := (20547184696761 / 25000000000000 : ℝ)) (b := (80256790513 / 50000000000000 : ℝ)) (q := (69871561867 / 3125000000000 : ℝ))
      (E := (cell12831 ⟨55, by decide⟩).energy) (xi := (330585706979449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12831 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12831]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12831])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12831) (a := (20547184696761 / 25000000000000 : ℝ)) (b := (80256790513 / 50000000000000 : ℝ)) (q := (69871561867 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12831])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12831])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12831]

theorem cert12831_56 : CellCertificate 12831 (220766677145617 / 2500000000000000 : ℝ) (51156277265259 / 31250000000000000 : ℝ) (330585706979449 / 10000000000000000 : ℝ)
    (cell12831 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · have h := gap_lower (n := 12831) (a := (82155124155009 / 100000000000000 : ℝ)) (b := (80256790513 / 50000000000000 : ℝ)) (q := (2235893982793 / 100000000000000 : ℝ))
      (E := (cell12831 ⟨56, by decide⟩).energy) (xi := (330585706979449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12831 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12831]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12831])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12831) (a := (82155124155009 / 100000000000000 : ℝ)) (b := (80256790513 / 50000000000000 : ℝ)) (q := (2235893982793 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12831])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12831])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12831]

theorem cert12831_57 : CellCertificate 12831 (220766677145617 / 2500000000000000 : ℝ) (51156277265259 / 31250000000000000 : ℝ) (330585706979449 / 10000000000000000 : ℝ)
    (cell12831 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · have h := gap_lower (n := 12831) (a := (12831489477 / 15625000000 : ℝ)) (b := (80256790513 / 50000000000000 : ℝ)) (q := (1117948995527 / 50000000000000 : ℝ))
      (E := (cell12831 ⟨57, by decide⟩).energy) (xi := (330585706979449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12831 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12831]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12831])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12831) (a := (12831489477 / 15625000000 : ℝ)) (b := (80256790513 / 50000000000000 : ℝ)) (q := (1117948995527 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12831])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12831])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12831]

theorem cert12831_58 : CellCertificate 12831 (220766677145617 / 2500000000000000 : ℝ) (51156277265259 / 31250000000000000 : ℝ) (330585706979449 / 10000000000000000 : ℝ)
    (cell12831 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · have h := gap_lower (n := 12831) (a := (20521991063243 / 25000000000000 : ℝ)) (b := (80256790513 / 50000000000000 : ℝ)) (q := (2235902000383 / 100000000000000 : ℝ))
      (E := (cell12831 ⟨58, by decide⟩).energy) (xi := (330585706979449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12831 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12831]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12831])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12831) (a := (20521991063243 / 25000000000000 : ℝ)) (b := (80256790513 / 50000000000000 : ℝ)) (q := (2235902000383 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12831])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12831])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12831]

theorem cert12831_59 : CellCertificate 12831 (220766677145617 / 2500000000000000 : ℝ) (51156277265259 / 31250000000000000 : ℝ) (330585706979449 / 10000000000000000 : ℝ)
    (cell12831 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · have h := gap_lower (n := 12831) (a := (20513604732053 / 25000000000000 : ℝ)) (b := (80256790513 / 50000000000000 : ℝ)) (q := (2235906006433 / 100000000000000 : ℝ))
      (E := (cell12831 ⟨59, by decide⟩).energy) (xi := (330585706979449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12831 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12831]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12831])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12831) (a := (20513604732053 / 25000000000000 : ℝ)) (b := (80256790513 / 50000000000000 : ℝ)) (q := (2235906006433 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12831])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12831])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12831]

theorem cert12832_40 : CellCertificate 12832 (883039318768233 / 10000000000000000 : ℝ) (1636873259211459 / 1000000000000000000 : ℝ) (82639832355029 / 2500000000000000 : ℝ)
    (cell12832 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · have h := gap_lower (n := 12832) (a := (41347875189891 / 50000000000000 : ℝ)) (b := (160500922881 / 100000000000000 : ℝ)) (q := (447142255801 / 20000000000000 : ℝ))
      (E := (cell12832 ⟨40, by decide⟩).energy) (xi := (82639832355029 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12832 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12832]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12832])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12832) (a := (41347875189891 / 50000000000000 : ℝ)) (b := (160500922881 / 100000000000000 : ℝ)) (q := (447142255801 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12832])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12832])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12832]

theorem cert12832_41 : CellCertificate 12832 (883039318768233 / 10000000000000000 : ℝ) (1636873259211459 / 1000000000000000000 : ℝ) (82639832355029 / 2500000000000000 : ℝ)
    (cell12832 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · have h := gap_lower (n := 12832) (a := (82661785709353 / 100000000000000 : ℝ)) (b := (160500922881 / 100000000000000 : ℝ)) (q := (3577144511 / 160000000000 : ℝ))
      (E := (cell12832 ⟨41, by decide⟩).energy) (xi := (82639832355029 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12832 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12832]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12832])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12832) (a := (82661785709353 / 100000000000000 : ℝ)) (b := (160500922881 / 100000000000000 : ℝ)) (q := (3577144511 / 160000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12832])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12832])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12832]

theorem cert12832_42 : CellCertificate 12832 (883039318768233 / 10000000000000000 : ℝ) (1636873259211459 / 1000000000000000000 : ℝ) (82639832355029 / 2500000000000000 : ℝ)
    (cell12832 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · have h := gap_lower (n := 12832) (a := (3305113783879 / 4000000000000 : ℝ)) (b := (160500922881 / 100000000000000 : ℝ)) (q := (44714385707 / 2000000000000 : ℝ))
      (E := (cell12832 ⟨42, by decide⟩).energy) (xi := (82639832355029 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12832 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12832]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12832])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12832) (a := (3305113783879 / 4000000000000 : ℝ)) (b := (160500922881 / 100000000000000 : ℝ)) (q := (44714385707 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12832])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12832])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12832]

theorem cert12832_43 : CellCertificate 12832 (883039318768233 / 10000000000000000 : ℝ) (1636873259211459 / 1000000000000000000 : ℝ) (82639832355029 / 2500000000000000 : ℝ)
    (cell12832 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · have h := gap_lower (n := 12832) (a := (1290530109579 / 1562500000000 : ℝ)) (b := (160500922881 / 100000000000000 : ℝ)) (q := (558930823371 / 25000000000000 : ℝ))
      (E := (cell12832 ⟨43, by decide⟩).energy) (xi := (82639832355029 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12832 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12832]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12832])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12832) (a := (1290530109579 / 1562500000000 : ℝ)) (b := (160500922881 / 100000000000000 : ℝ)) (q := (558930823371 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12832])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12832])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12832]

theorem cert12832_44 : CellCertificate 12832 (883039318768233 / 10000000000000000 : ℝ) (1636873259211459 / 1000000000000000000 : ℝ) (82639832355029 / 2500000000000000 : ℝ)
    (cell12832 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · have h := gap_lower (n := 12832) (a := (82560032928153 / 100000000000000 : ℝ)) (b := (160500922881 / 100000000000000 : ℝ)) (q := (1117863671297 / 50000000000000 : ℝ))
      (E := (cell12832 ⟨44, by decide⟩).energy) (xi := (82639832355029 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12832 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12832]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12832])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12832) (a := (82560032928153 / 100000000000000 : ℝ)) (b := (160500922881 / 100000000000000 : ℝ)) (q := (1117863671297 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12832])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12832])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12832]

theorem cert12832_45 : CellCertificate 12832 (883039318768233 / 10000000000000000 : ℝ) (1636873259211459 / 1000000000000000000 : ℝ) (82639832355029 / 2500000000000000 : ℝ)
    (cell12832 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · have h := gap_lower (n := 12832) (a := (20631540578243 / 25000000000000 : ℝ)) (b := (160500922881 / 100000000000000 : ℝ)) (q := (2235731313523 / 100000000000000 : ℝ))
      (E := (cell12832 ⟨45, by decide⟩).energy) (xi := (82639832355029 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12832 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12832]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12832])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12832) (a := (20631540578243 / 25000000000000 : ℝ)) (b := (160500922881 / 100000000000000 : ℝ)) (q := (2235731313523 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12832])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12832])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12832]

theorem cert12832_46 : CellCertificate 12832 (883039318768233 / 10000000000000000 : ℝ) (1636873259211459 / 1000000000000000000 : ℝ) (82639832355029 / 2500000000000000 : ℝ)
    (cell12832 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · have h := gap_lower (n := 12832) (a := (20623078784591 / 25000000000000 : ℝ)) (b := (160500922881 / 100000000000000 : ℝ)) (q := (2235735322319 / 100000000000000 : ℝ))
      (E := (cell12832 ⟨46, by decide⟩).energy) (xi := (82639832355029 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12832 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12832]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12832])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12832) (a := (20623078784591 / 25000000000000 : ℝ)) (b := (160500922881 / 100000000000000 : ℝ)) (q := (2235735322319 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12832])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12832])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12832]

theorem cert12832_47 : CellCertificate 12832 (883039318768233 / 10000000000000000 : ℝ) (1636873259211459 / 1000000000000000000 : ℝ) (82639832355029 / 2500000000000000 : ℝ)
    (cell12832 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · have h := gap_lower (n := 12832) (a := (2576827855479 / 3125000000000 : ℝ)) (b := (160500922881 / 100000000000000 : ℝ)) (q := (89429572329 / 4000000000000 : ℝ))
      (E := (cell12832 ⟨47, by decide⟩).energy) (xi := (82639832355029 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12832 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12832]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12832])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12832) (a := (2576827855479 / 3125000000000 : ℝ)) (b := (160500922881 / 100000000000000 : ℝ)) (q := (89429572329 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12832])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12832])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12832]

theorem cert12832_48 : CellCertificate 12832 (883039318768233 / 10000000000000000 : ℝ) (1636873259211459 / 1000000000000000000 : ℝ) (82639832355029 / 2500000000000000 : ℝ)
    (cell12832 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · have h := gap_lower (n := 12832) (a := (82424690995009 / 100000000000000 : ℝ)) (b := (160500922881 / 100000000000000 : ℝ)) (q := (2235743328073 / 100000000000000 : ℝ))
      (E := (cell12832 ⟨48, by decide⟩).energy) (xi := (82639832355029 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12832 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12832]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12832])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12832) (a := (82424690995009 / 100000000000000 : ℝ)) (b := (160500922881 / 100000000000000 : ℝ)) (q := (2235743328073 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12832])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12832])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12832]

theorem cert12832_49 : CellCertificate 12832 (883039318768233 / 10000000000000000 : ℝ) (1636873259211459 / 1000000000000000000 : ℝ) (82639832355029 / 2500000000000000 : ℝ)
    (cell12832 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · have h := gap_lower (n := 12832) (a := (10298864246087 / 12500000000000 : ℝ)) (b := (160500922881 / 100000000000000 : ℝ)) (q := (447149464127 / 20000000000000 : ℝ))
      (E := (cell12832 ⟨49, by decide⟩).energy) (xi := (82639832355029 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12832 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12832]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12832])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12832) (a := (10298864246087 / 12500000000000 : ℝ)) (b := (160500922881 / 100000000000000 : ℝ)) (q := (447149464127 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12832])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12832])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12832]

theorem cert12832_50 : CellCertificate 12832 (883039318768233 / 10000000000000000 : ℝ) (1636873259211459 / 1000000000000000000 : ℝ) (82639832355029 / 2500000000000000 : ℝ)
    (cell12832 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · have h := gap_lower (n := 12832) (a := (41178580133911 / 50000000000000 : ℝ)) (b := (160500922881 / 100000000000000 : ℝ)) (q := (1117875671181 / 50000000000000 : ℝ))
      (E := (cell12832 ⟨50, by decide⟩).energy) (xi := (82639832355029 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12832 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12832]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12832])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12832) (a := (41178580133911 / 50000000000000 : ℝ)) (b := (160500922881 / 100000000000000 : ℝ)) (q := (1117875671181 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12832])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12832])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12832]

theorem cert12832_51 : CellCertificate 12832 (883039318768233 / 10000000000000000 : ℝ) (1636873259211459 / 1000000000000000000 : ℝ) (82639832355029 / 2500000000000000 : ℝ)
    (cell12832 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · have h := gap_lower (n := 12832) (a := (41161714931981 / 50000000000000 : ℝ)) (b := (160500922881 / 100000000000000 : ℝ)) (q := (2235755390573 / 100000000000000 : ℝ))
      (E := (cell12832 ⟨51, by decide⟩).energy) (xi := (82639832355029 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12832 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12832]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12832])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12832) (a := (41161714931981 / 50000000000000 : ℝ)) (b := (160500922881 / 100000000000000 : ℝ)) (q := (2235755390573 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12832])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12832])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12832]

theorem cert12832_52 : CellCertificate 12832 (883039318768233 / 10000000000000000 : ℝ) (1636873259211459 / 1000000000000000000 : ℝ) (82639832355029 / 2500000000000000 : ℝ)
    (cell12832 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · have h := gap_lower (n := 12832) (a := (41144861364417 / 50000000000000 : ℝ)) (b := (160500922881 / 100000000000000 : ℝ)) (q := (558939836073 / 25000000000000 : ℝ))
      (E := (cell12832 ⟨52, by decide⟩).energy) (xi := (82639832355029 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12832 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12832]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12832])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12832) (a := (41144861364417 / 50000000000000 : ℝ)) (b := (160500922881 / 100000000000000 : ℝ)) (q := (558939836073 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12832])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12832])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12832]

theorem cert12832_53 : CellCertificate 12832 (883039318768233 / 10000000000000000 : ℝ) (1636873259211459 / 1000000000000000000 : ℝ) (82639832355029 / 2500000000000000 : ℝ)
    (cell12832 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · have h := gap_lower (n := 12832) (a := (41128019417149 / 50000000000000 : ℝ)) (b := (160500922881 / 100000000000000 : ℝ)) (q := (2235763377467 / 100000000000000 : ℝ))
      (E := (cell12832 ⟨53, by decide⟩).energy) (xi := (82639832355029 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12832 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12832]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12832])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12832) (a := (41128019417149 / 50000000000000 : ℝ)) (b := (160500922881 / 100000000000000 : ℝ)) (q := (2235763377467 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12832])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12832])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12832]

theorem cert12832_54 : CellCertificate 12832 (883039318768233 / 10000000000000000 : ℝ) (1636873259211459 / 1000000000000000000 : ℝ) (82639832355029 / 2500000000000000 : ℝ)
    (cell12832 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · have h := gap_lower (n := 12832) (a := (41111189076177 / 50000000000000 : ℝ)) (b := (160500922881 / 100000000000000 : ℝ)) (q := (1117883684339 / 50000000000000 : ℝ))
      (E := (cell12832 ⟨54, by decide⟩).energy) (xi := (82639832355029 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12832 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12832]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12832])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12832) (a := (41111189076177 / 50000000000000 : ℝ)) (b := (160500922881 / 100000000000000 : ℝ)) (q := (1117883684339 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12832])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12832])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12832]

theorem cert12832_55 : CellCertificate 12832 (883039318768233 / 10000000000000000 : ℝ) (1636873259211459 / 1000000000000000000 : ℝ) (82639832355029 / 2500000000000000 : ℝ)
    (cell12832 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · have h := gap_lower (n := 12832) (a := (82188740655141 / 100000000000000 : ℝ)) (b := (160500922881 / 100000000000000 : ℝ)) (q := (447154274689 / 20000000000000 : ℝ))
      (E := (cell12832 ⟨55, by decide⟩).energy) (xi := (82639832355029 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12832 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12832]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12832])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12832) (a := (82188740655141 / 100000000000000 : ℝ)) (b := (160500922881 / 100000000000000 : ℝ)) (q := (447154274689 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12832])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12832])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12832]

theorem cert12832_56 : CellCertificate 12832 (883039318768233 / 10000000000000000 : ℝ) (1636873259211459 / 1000000000000000000 : ℝ) (82639832355029 / 2500000000000000 : ℝ)
    (cell12832 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · have h := gap_lower (n := 12832) (a := (41077563157469 / 50000000000000 : ℝ)) (b := (160500922881 / 100000000000000 : ℝ)) (q := (2235775388039 / 100000000000000 : ℝ))
      (E := (cell12832 ⟨56, by decide⟩).energy) (xi := (82639832355029 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12832 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12832]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12832])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12832) (a := (41077563157469 / 50000000000000 : ℝ)) (b := (160500922881 / 100000000000000 : ℝ)) (q := (2235775388039 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12832])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12832])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12832]

theorem cert12832_57 : CellCertificate 12832 (883039318768233 / 10000000000000000 : ℝ) (1636873259211459 / 1000000000000000000 : ℝ) (82639832355029 / 2500000000000000 : ℝ)
    (cell12832 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · have h := gap_lower (n := 12832) (a := (82121535104161 / 100000000000000 : ℝ)) (b := (160500922881 / 100000000000000 : ℝ)) (q := (2235779408521 / 100000000000000 : ℝ))
      (E := (cell12832 ⟨57, by decide⟩).energy) (xi := (82639832355029 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12832 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12832]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12832])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12832) (a := (82121535104161 / 100000000000000 : ℝ)) (b := (160500922881 / 100000000000000 : ℝ)) (q := (2235779408521 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12832])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12832])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12832]

theorem cert12832_58 : CellCertificate 12832 (883039318768233 / 10000000000000000 : ℝ) (1636873259211459 / 1000000000000000000 : ℝ) (82639832355029 / 2500000000000000 : ℝ)
    (cell12832 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · have h := gap_lower (n := 12832) (a := (16417593399073 / 20000000000000 : ℝ)) (b := (160500922881 / 100000000000000 : ℝ)) (q := (558945857687 / 25000000000000 : ℝ))
      (E := (cell12832 ⟨58, by decide⟩).energy) (xi := (82639832355029 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12832 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12832]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12832])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12832) (a := (16417593399073 / 20000000000000 : ℝ)) (b := (160500922881 / 100000000000000 : ℝ)) (q := (558945857687 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12832])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12832])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12832]

theorem cert12832_59 : CellCertificate 12832 (883039318768233 / 10000000000000000 : ℝ) (1636873259211459 / 1000000000000000000 : ℝ) (82639832355029 / 2500000000000000 : ℝ)
    (cell12832 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · have h := gap_lower (n := 12832) (a := (82054421961239 / 100000000000000 : ℝ)) (b := (160500922881 / 100000000000000 : ℝ)) (q := (223578745037 / 10000000000000 : ℝ))
      (E := (cell12832 ⟨59, by decide⟩).energy) (xi := (82639832355029 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12832 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12832]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12832])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12832) (a := (82054421961239 / 100000000000000 : ℝ)) (b := (160500922881 / 100000000000000 : ℝ)) (q := (223578745037 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12832])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12832])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12832]

theorem cert12833_40 : CellCertificate 12833 (27594122907763 / 312500000000000 : ℝ) (8183728329147 / 5000000000000000 : ℝ) (330532956117549 / 10000000000000000 : ℝ)
    (cell12833 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · have h := gap_lower (n := 12833) (a := (41347873911389 / 50000000000000 : ℝ)) (b := (160488266743 / 100000000000000 : ℝ)) (q := (2235592695621 / 100000000000000 : ℝ))
      (E := (cell12833 ⟨40, by decide⟩).energy) (xi := (330532956117549 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12833 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12833]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12833])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12833) (a := (41347873911389 / 50000000000000 : ℝ)) (b := (160488266743 / 100000000000000 : ℝ)) (q := (2235592695621 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12833])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12833])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12833]

theorem cert12833_41 : CellCertificate 12833 (27594122907763 / 312500000000000 : ℝ) (8183728329147 / 5000000000000000 : ℝ) (330532956117549 / 10000000000000000 : ℝ)
    (cell12833 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · have h := gap_lower (n := 12833) (a := (82661783450229 / 100000000000000 : ℝ)) (b := (160488266743 / 100000000000000 : ℝ)) (q := (139724796087 / 6250000000000 : ℝ))
      (E := (cell12833 ⟨41, by decide⟩).energy) (xi := (330532956117549 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12833 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12833]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12833])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12833) (a := (82661783450229 / 100000000000000 : ℝ)) (b := (160488266743 / 100000000000000 : ℝ)) (q := (139724796087 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12833])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12833])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12833]

theorem cert12833_42 : CellCertificate 12833 (27594122907763 / 312500000000000 : ℝ) (8183728329147 / 5000000000000000 : ℝ) (330532956117549 / 10000000000000000 : ℝ)
    (cell12833 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · have h := gap_lower (n := 12833) (a := (82627842635319 / 100000000000000 : ℝ)) (b := (160488266743 / 100000000000000 : ℝ)) (q := (139725044091 / 6250000000000 : ℝ))
      (E := (cell12833 ⟨42, by decide⟩).energy) (xi := (330532956117549 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12833 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12833]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12833])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12833) (a := (82627842635319 / 100000000000000 : ℝ)) (b := (160488266743 / 100000000000000 : ℝ)) (q := (139725044091 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12833])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12833])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12833]

theorem cert12833_43 : CellCertificate 12833 (27594122907763 / 312500000000000 : ℝ) (8183728329147 / 5000000000000000 : ℝ) (330532956117549 / 10000000000000000 : ℝ)
    (cell12833 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · have h := gap_lower (n := 12833) (a := (82593925348459 / 100000000000000 : ℝ)) (b := (160488266743 / 100000000000000 : ℝ)) (q := (558901179091 / 25000000000000 : ℝ))
      (E := (cell12833 ⟨43, by decide⟩).energy) (xi := (330532956117549 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12833 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12833]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12833])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12833) (a := (82593925348459 / 100000000000000 : ℝ)) (b := (160488266743 / 100000000000000 : ℝ)) (q := (558901179091 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12833])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12833])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12833]

theorem cert12833_44 : CellCertificate 12833 (27594122907763 / 312500000000000 : ℝ) (8183728329147 / 5000000000000000 : ℝ) (330532956117549 / 10000000000000000 : ℝ)
    (cell12833 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · have h := gap_lower (n := 12833) (a := (41280015780103 / 50000000000000 : ℝ)) (b := (160488266743 / 100000000000000 : ℝ)) (q := (1117804355039 / 50000000000000 : ℝ))
      (E := (cell12833 ⟨44, by decide⟩).energy) (xi := (330532956117549 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12833 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12833]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12833])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12833) (a := (41280015780103 / 50000000000000 : ℝ)) (b := (160488266743 / 100000000000000 : ℝ)) (q := (1117804355039 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12833])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12833])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12833]

theorem cert12833_45 : CellCertificate 12833 (27594122907763 / 312500000000000 : ℝ) (8183728329147 / 5000000000000000 : ℝ) (330532956117549 / 10000000000000000 : ℝ)
    (cell12833 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · have h := gap_lower (n := 12833) (a := (16505232248253 / 20000000000000 : ℝ)) (b := (160488266743 / 100000000000000 : ℝ)) (q := (1117806372003 / 50000000000000 : ℝ))
      (E := (cell12833 ⟨45, by decide⟩).energy) (xi := (330532956117549 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12833 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12833]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12833])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12833) (a := (16505232248253 / 20000000000000 : ℝ)) (b := (160488266743 / 100000000000000 : ℝ)) (q := (1117806372003 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12833])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12833])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12833]

theorem cert12833_46 : CellCertificate 12833 (27594122907763 / 312500000000000 : ℝ) (8183728329147 / 5000000000000000 : ℝ) (330532956117549 / 10000000000000000 : ℝ)
    (cell12833 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · have h := gap_lower (n := 12833) (a := (82492314362491 / 100000000000000 : ℝ)) (b := (160488266743 / 100000000000000 : ℝ)) (q := (2235616757629 / 100000000000000 : ℝ))
      (E := (cell12833 ⟨46, by decide⟩).energy) (xi := (330532956117549 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12833 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12833]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12833])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12833) (a := (82492314362491 / 100000000000000 : ℝ)) (b := (160488266743 / 100000000000000 : ℝ)) (q := (2235616757629 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12833])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12833])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12833]

theorem cert12833_47 : CellCertificate 12833 (27594122907763 / 312500000000000 : ℝ) (8183728329147 / 5000000000000000 : ℝ) (330532956117549 / 10000000000000000 : ℝ)
    (cell12833 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · have h := gap_lower (n := 12833) (a := (41229245447441 / 50000000000000 : ℝ)) (b := (160488266743 / 100000000000000 : ℝ)) (q := (447124149809 / 20000000000000 : ℝ))
      (E := (cell12833 ⟨47, by decide⟩).energy) (xi := (330532956117549 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12833 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12833]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12833])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12833) (a := (41229245447441 / 50000000000000 : ℝ)) (b := (160488266743 / 100000000000000 : ℝ)) (q := (447124149809 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12833])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12833])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12833]

theorem cert12833_48 : CellCertificate 12833 (27594122907763 / 312500000000000 : ℝ) (8183728329147 / 5000000000000000 : ℝ) (330532956117549 / 10000000000000000 : ℝ)
    (cell12833 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · have h := gap_lower (n := 12833) (a := (5151543175599 / 6250000000000 : ℝ)) (b := (160488266743 / 100000000000000 : ℝ)) (q := (1117812387543 / 50000000000000 : ℝ))
      (E := (cell12833 ⟨48, by decide⟩).energy) (xi := (330532956117549 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12833 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12833]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12833])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12833) (a := (5151543175599 / 6250000000000 : ℝ)) (b := (160488266743 / 100000000000000 : ℝ)) (q := (1117812387543 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12833])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12833])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12833]

theorem cert12833_49 : CellCertificate 12833 (27594122907763 / 312500000000000 : ℝ) (8183728329147 / 5000000000000000 : ℝ) (330532956117549 / 10000000000000000 : ℝ)
    (cell12833 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · have h := gap_lower (n := 12833) (a := (41195457038943 / 50000000000000 : ℝ)) (b := (160488266743 / 100000000000000 : ℝ)) (q := (1117814387261 / 50000000000000 : ℝ))
      (E := (cell12833 ⟨49, by decide⟩).energy) (xi := (330532956117549 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12833 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12833]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12833])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12833) (a := (41195457038943 / 50000000000000 : ℝ)) (b := (160488266743 / 100000000000000 : ℝ)) (q := (1117814387261 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12833])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12833])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12833]

theorem cert12833_50 : CellCertificate 12833 (27594122907763 / 312500000000000 : ℝ) (8183728329147 / 5000000000000000 : ℝ) (330532956117549 / 10000000000000000 : ℝ)
    (cell12833 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · have h := gap_lower (n := 12833) (a := (41178580335611 / 50000000000000 : ℝ)) (b := (160488266743 / 100000000000000 : ℝ)) (q := (447126560761 / 20000000000000 : ℝ))
      (E := (cell12833 ⟨50, by decide⟩).energy) (xi := (330532956117549 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12833 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12833]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12833])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12833) (a := (41178580335611 / 50000000000000 : ℝ)) (b := (160488266743 / 100000000000000 : ℝ)) (q := (447126560761 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12833])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12833])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12833]

theorem cert12833_51 : CellCertificate 12833 (27594122907763 / 312500000000000 : ℝ) (8183728329147 / 5000000000000000 : ℝ) (330532956117549 / 10000000000000000 : ℝ)
    (cell12833 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · have h := gap_lower (n := 12833) (a := (5145214410073 / 6250000000000 : ℝ)) (b := (160488266743 / 100000000000000 : ℝ)) (q := (447127360247 / 20000000000000 : ℝ))
      (E := (cell12833 ⟨51, by decide⟩).energy) (xi := (330532956117549 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12833 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12833]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12833])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12833) (a := (5145214410073 / 6250000000000 : ℝ)) (b := (160488266743 / 100000000000000 : ℝ)) (q := (447127360247 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12833])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12833])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12833]

theorem cert12833_52 : CellCertificate 12833 (27594122907763 / 312500000000000 : ℝ) (8183728329147 / 5000000000000000 : ℝ) (330532956117549 / 10000000000000000 : ℝ)
    (cell12833 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · have h := gap_lower (n := 12833) (a := (20572430929861 / 25000000000000 : ℝ)) (b := (160488266743 / 100000000000000 : ℝ)) (q := (1117820411443 / 50000000000000 : ℝ))
      (E := (cell12833 ⟨52, by decide⟩).energy) (xi := (330532956117549 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12833 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12833]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12833])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12833) (a := (20572430929861 / 25000000000000 : ℝ)) (b := (160488266743 / 100000000000000 : ℝ)) (q := (1117820411443 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12833])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12833])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12833]

theorem cert12833_53 : CellCertificate 12833 (27594122907763 / 312500000000000 : ℝ) (8183728329147 / 5000000000000000 : ℝ) (330532956117549 / 10000000000000000 : ℝ)
    (cell12833 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · have h := gap_lower (n := 12833) (a := (20564010029477 / 25000000000000 : ℝ)) (b := (160488266743 / 100000000000000 : ℝ)) (q := (223564480659 / 10000000000000 : ℝ))
      (E := (cell12833 ⟨53, by decide⟩).energy) (xi := (330532956117549 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12833 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12833]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12833])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12833) (a := (20564010029477 / 25000000000000 : ℝ)) (b := (160488266743 / 100000000000000 : ℝ)) (q := (223564480659 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12833])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12833])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12833]

theorem cert12833_54 : CellCertificate 12833 (27594122907763 / 312500000000000 : ℝ) (8183728329147 / 5000000000000000 : ℝ) (330532956117549 / 10000000000000000 : ℝ)
    (cell12833 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · have h := gap_lower (n := 12833) (a := (82222379728563 / 100000000000000 : ℝ)) (b := (160488266743 / 100000000000000 : ℝ)) (q := (44712976161 / 2000000000000 : ℝ))
      (E := (cell12833 ⟨54, by decide⟩).energy) (xi := (330532956117549 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12833 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12833]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12833])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12833) (a := (82222379728563 / 100000000000000 : ℝ)) (b := (160488266743 / 100000000000000 : ℝ)) (q := (44712976161 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12833])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12833])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12833]

theorem cert12833_55 : CellCertificate 12833 (27594122907763 / 312500000000000 : ℝ) (8183728329147 / 5000000000000000 : ℝ) (330532956117549 / 10000000000000000 : ℝ)
    (cell12833 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · have h := gap_lower (n := 12833) (a := (82188742523547 / 100000000000000 : ℝ)) (b := (160488266743 / 100000000000000 : ℝ)) (q := (447130564749 / 20000000000000 : ℝ))
      (E := (cell12833 ⟨55, by decide⟩).energy) (xi := (330532956117549 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12833 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12833]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12833])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12833) (a := (82188742523547 / 100000000000000 : ℝ)) (b := (160488266743 / 100000000000000 : ℝ)) (q := (447130564749 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12833])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12833])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12833]

theorem cert12833_56 : CellCertificate 12833 (27594122907763 / 312500000000000 : ℝ) (8183728329147 / 5000000000000000 : ℝ) (330532956117549 / 10000000000000000 : ℝ)
    (cell12833 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · have h := gap_lower (n := 12833) (a := (82155128475141 / 100000000000000 : ℝ)) (b := (160488266743 / 100000000000000 : ℝ)) (q := (2235656849943 / 100000000000000 : ℝ))
      (E := (cell12833 ⟨56, by decide⟩).energy) (xi := (330532956117549 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12833 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12833]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12833])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12833) (a := (82155128475141 / 100000000000000 : ℝ)) (b := (160488266743 / 100000000000000 : ℝ)) (q := (2235656849943 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12833])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12833])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12833]

theorem cert12833_57 : CellCertificate 12833 (27594122907763 / 312500000000000 : ℝ) (8183728329147 / 5000000000000000 : ℝ) (330532956117549 / 10000000000000000 : ℝ)
    (cell12833 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · have h := gap_lower (n := 12833) (a := (82121537555761 / 100000000000000 : ℝ)) (b := (160488266743 / 100000000000000 : ℝ)) (q := (1117830411773 / 50000000000000 : ℝ))
      (E := (cell12833 ⟨57, by decide⟩).energy) (xi := (330532956117549 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12833 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12833]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12833])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12833) (a := (82121537555761 / 100000000000000 : ℝ)) (b := (160488266743 / 100000000000000 : ℝ)) (q := (1117830411773 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12833])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12833])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12833]

theorem cert12833_58 : CellCertificate 12833 (27594122907763 / 312500000000000 : ℝ) (8183728329147 / 5000000000000000 : ℝ) (330532956117549 / 10000000000000000 : ℝ)
    (cell12833 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · have h := gap_lower (n := 12833) (a := (41043984868981 / 50000000000000 : ℝ)) (b := (160488266743 / 100000000000000 : ℝ)) (q := (1117832429353 / 50000000000000 : ℝ))
      (E := (cell12833 ⟨58, by decide⟩).energy) (xi := (330532956117549 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12833 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12833]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12833])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12833) (a := (41043984868981 / 50000000000000 : ℝ)) (b := (160488266743 / 100000000000000 : ℝ)) (q := (1117832429353 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12833])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12833])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12833]

theorem cert12833_59 : CellCertificate 12833 (27594122907763 / 312500000000000 : ℝ) (8183728329147 / 5000000000000000 : ℝ) (330532956117549 / 10000000000000000 : ℝ)
    (cell12833 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · have h := gap_lower (n := 12833) (a := (20513606248609 / 25000000000000 : ℝ)) (b := (160488266743 / 100000000000000 : ℝ)) (q := (2235668832729 / 100000000000000 : ℝ))
      (E := (cell12833 ⟨59, by decide⟩).energy) (xi := (330532956117549 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12833 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12833]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12833])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12833) (a := (20513606248609 / 25000000000000 : ℝ)) (b := (160488266743 / 100000000000000 : ℝ)) (q := (2235668832729 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12833])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12833])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12833]

theorem cert12834_40 : CellCertificate 12834 (441492275711027 / 5000000000000000 : ℝ) (1636618092337459 / 1000000000000000000 : ℝ) (4131332338383 / 125000000000000 : ℝ)
    (cell12834 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · have h := gap_lower (n := 12834) (a := (41347872633307 / 50000000000000 : ℝ)) (b := (160475612613 / 100000000000000 : ℝ)) (q := (2235474167939 / 100000000000000 : ℝ))
      (E := (cell12834 ⟨40, by decide⟩).energy) (xi := (4131332338383 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12834 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12834]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12834])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12834) (a := (41347872633307 / 50000000000000 : ℝ)) (b := (160475612613 / 100000000000000 : ℝ)) (q := (2235474167939 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12834])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12834])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12834]

theorem cert12834_41 : CellCertificate 12834 (441492275711027 / 5000000000000000 : ℝ) (1636618092337459 / 1000000000000000000 : ℝ) (4131332338383 / 125000000000000 : ℝ)
    (cell12834 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · have h := gap_lower (n := 12834) (a := (82661781191907 / 100000000000000 : ℝ)) (b := (160475612613 / 100000000000000 : ℝ)) (q := (223547815239 / 10000000000000 : ℝ))
      (E := (cell12834 ⟨41, by decide⟩).energy) (xi := (4131332338383 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12834 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12834]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12834])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12834) (a := (82661781191907 / 100000000000000 : ℝ)) (b := (160475612613 / 100000000000000 : ℝ)) (q := (223547815239 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12834])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12834])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12834]

theorem cert12834_42 : CellCertificate 12834 (441492275711027 / 5000000000000000 : ℝ) (1636618092337459 / 1000000000000000000 : ℝ) (4131332338383 / 125000000000000 : ℝ)
    (cell12834 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · have h := gap_lower (n := 12834) (a := (82627840674431 / 100000000000000 : ℝ)) (b := (160475612613 / 100000000000000 : ℝ)) (q := (279435272673 / 12500000000000 : ℝ))
      (E := (cell12834 ⟨42, by decide⟩).energy) (xi := (4131332338383 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12834 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12834]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12834])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12834) (a := (82627840674431 / 100000000000000 : ℝ)) (b := (160475612613 / 100000000000000 : ℝ)) (q := (279435272673 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12834])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12834])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12834]

theorem cert12834_43 : CellCertificate 12834 (441492275711027 / 5000000000000000 : ℝ) (1636618092337459 / 1000000000000000000 : ℝ) (4131332338383 / 125000000000000 : ℝ)
    (cell12834 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · have h := gap_lower (n := 12834) (a := (82593923684593 / 100000000000000 : ℝ)) (b := (160475612613 / 100000000000000 : ℝ)) (q := (2235486195127 / 100000000000000 : ℝ))
      (E := (cell12834 ⟨43, by decide⟩).energy) (xi := (4131332338383 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12834 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12834]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12834])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12834) (a := (82593923684593 / 100000000000000 : ℝ)) (b := (160475612613 / 100000000000000 : ℝ)) (q := (2235486195127 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12834])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12834])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12834]

theorem cert12834_44 : CellCertificate 12834 (441492275711027 / 5000000000000000 : ℝ) (1636618092337459 / 1000000000000000000 : ℝ) (4131332338383 / 125000000000000 : ℝ)
    (cell12834 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · have h := gap_lower (n := 12834) (a := (41280015096477 / 50000000000000 : ℝ)) (b := (160475612613 / 100000000000000 : ℝ)) (q := (2235490192361 / 100000000000000 : ℝ))
      (E := (cell12834 ⟨44, by decide⟩).energy) (xi := (4131332338383 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12834 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12834]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12834])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12834) (a := (41280015096477 / 50000000000000 : ℝ)) (b := (160475612613 / 100000000000000 : ℝ)) (q := (2235490192361 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12834])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12834])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12834]

theorem cert12834_45 : CellCertificate 12834 (441492275711027 / 5000000000000000 : ℝ) (1636618092337459 / 1000000000000000000 : ℝ) (4131332338383 / 125000000000000 : ℝ)
    (cell12834 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · have h := gap_lower (n := 12834) (a := (82526160170219 / 100000000000000 : ℝ)) (b := (160475612613 / 100000000000000 : ℝ)) (q := (447098834323 / 20000000000000 : ℝ))
      (E := (cell12834 ⟨45, by decide⟩).energy) (xi := (4131332338383 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12834 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12834]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12834])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12834) (a := (82526160170219 / 100000000000000 : ℝ)) (b := (160475612613 / 100000000000000 : ℝ)) (q := (447098834323 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12834])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12834])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12834]

theorem cert12834_46 : CellCertificate 12834 (441492275711027 / 5000000000000000 : ℝ) (1636618092337459 / 1000000000000000000 : ℝ) (4131332338383 / 125000000000000 : ℝ)
    (cell12834 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · have h := gap_lower (n := 12834) (a := (82492313587243 / 100000000000000 : ℝ)) (b := (160475612613 / 100000000000000 : ℝ)) (q := (2235498190101 / 100000000000000 : ℝ))
      (E := (cell12834 ⟨46, by decide⟩).energy) (xi := (4131332338383 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12834 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12834]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12834])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12834) (a := (82492313587243 / 100000000000000 : ℝ)) (b := (160475612613 / 100000000000000 : ℝ)) (q := (2235498190101 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12834])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12834])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12834]

theorem cert12834_47 : CellCertificate 12834 (441492275711027 / 5000000000000000 : ℝ) (1636618092337459 / 1000000000000000000 : ℝ) (4131332338383 / 125000000000000 : ℝ)
    (cell12834 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · have h := gap_lower (n := 12834) (a := (41229245207513 / 50000000000000 : ℝ)) (b := (160475612613 / 100000000000000 : ℝ)) (q := (2235502187063 / 100000000000000 : ℝ))
      (E := (cell12834 ⟨47, by decide⟩).energy) (xi := (4131332338383 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12834 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12834]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12834])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12834) (a := (41229245207513 / 50000000000000 : ℝ)) (b := (160475612613 / 100000000000000 : ℝ)) (q := (2235502187063 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12834])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12834])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12834]

theorem cert12834_48 : CellCertificate 12834 (441492275711027 / 5000000000000000 : ℝ) (1636618092337459 / 1000000000000000000 : ℝ) (4131332338383 / 125000000000000 : ℝ)
    (cell12834 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · have h := gap_lower (n := 12834) (a := (82424690624713 / 100000000000000 : ℝ)) (b := (160475612613 / 100000000000000 : ℝ)) (q := (2235506219333 / 100000000000000 : ℝ))
      (E := (cell12834 ⟨48, by decide⟩).energy) (xi := (4131332338383 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12834 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12834]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12834])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12834) (a := (82424690624713 / 100000000000000 : ℝ)) (b := (160475612613 / 100000000000000 : ℝ)) (q := (2235506219333 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12834])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12834])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12834]

theorem cert12834_49 : CellCertificate 12834 (441492275711027 / 5000000000000000 : ℝ) (1636618092337459 / 1000000000000000000 : ℝ) (4131332338383 / 125000000000000 : ℝ)
    (cell12834 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · have h := gap_lower (n := 12834) (a := (16478182837519 / 20000000000000 : ℝ)) (b := (160475612613 / 100000000000000 : ℝ)) (q := (27943877821 / 1250000000000 : ℝ))
      (E := (cell12834 ⟨49, by decide⟩).energy) (xi := (4131332338383 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12834 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12834]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12834])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12834) (a := (16478182837519 / 20000000000000 : ℝ)) (b := (160475612613 / 100000000000000 : ℝ)) (q := (27943877821 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12834])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12834])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12834]

theorem cert12834_50 : CellCertificate 12834 (441492275711027 / 5000000000000000 : ℝ) (1636618092337459 / 1000000000000000000 : ℝ) (4131332338383 / 125000000000000 : ℝ)
    (cell12834 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · have h := gap_lower (n := 12834) (a := (41178580537553 / 50000000000000 : ℝ)) (b := (160475612613 / 100000000000000 : ℝ)) (q := (55887855089 / 2500000000000 : ℝ))
      (E := (cell12834 ⟨50, by decide⟩).energy) (xi := (4131332338383 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12834 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12834]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12834])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12834) (a := (41178580537553 / 50000000000000 : ℝ)) (b := (160475612613 / 100000000000000 : ℝ)) (q := (55887855089 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12834])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12834])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12834]

theorem cert12834_51 : CellCertificate 12834 (441492275711027 / 5000000000000000 : ℝ) (1636618092337459 / 1000000000000000000 : ℝ) (4131332338383 / 125000000000000 : ℝ)
    (cell12834 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · have h := gap_lower (n := 12834) (a := (10290428907353 / 12500000000000 : ℝ)) (b := (160475612613 / 100000000000000 : ℝ)) (q := (447103653651 / 20000000000000 : ℝ))
      (E := (cell12834 ⟨51, by decide⟩).energy) (xi := (4131332338383 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12834 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12834]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12834])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12834) (a := (10290428907353 / 12500000000000 : ℝ)) (b := (160475612613 / 100000000000000 : ℝ)) (q := (447103653651 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12834])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12834])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12834]

theorem cert12834_52 : CellCertificate 12834 (441492275711027 / 5000000000000000 : ℝ) (1636618092337459 / 1000000000000000000 : ℝ) (4131332338383 / 125000000000000 : ℝ)
    (cell12834 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · have h := gap_lower (n := 12834) (a := (82289724710467 / 100000000000000 : ℝ)) (b := (160475612613 / 100000000000000 : ℝ)) (q := (2235522239817 / 100000000000000 : ℝ))
      (E := (cell12834 ⟨52, by decide⟩).energy) (xi := (4131332338383 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12834 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12834]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12834])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12834) (a := (82289724710467 / 100000000000000 : ℝ)) (b := (160475612613 / 100000000000000 : ℝ)) (q := (2235522239817 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12834])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12834])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12834]

theorem cert12834_53 : CellCertificate 12834 (441492275711027 / 5000000000000000 : ℝ) (1636618092337459 / 1000000000000000000 : ℝ) (4131332338383 / 125000000000000 : ℝ)
    (cell12834 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · have h := gap_lower (n := 12834) (a := (82256041401897 / 100000000000000 : ℝ)) (b := (160475612613 / 100000000000000 : ℝ)) (q := (279440779141 / 12500000000000 : ℝ))
      (E := (cell12834 ⟨53, by decide⟩).energy) (xi := (4131332338383 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12834 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12834]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12834])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12834) (a := (82256041401897 / 100000000000000 : ℝ)) (b := (160475612613 / 100000000000000 : ℝ)) (q := (279440779141 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12834])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12834])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12834]

theorem cert12834_54 : CellCertificate 12834 (441492275711027 / 5000000000000000 : ℝ) (1636618092337459 / 1000000000000000000 : ℝ) (4131332338383 / 125000000000000 : ℝ)
    (cell12834 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · have h := gap_lower (n := 12834) (a := (16444476261023 / 20000000000000 : ℝ)) (b := (160475612613 / 100000000000000 : ℝ)) (q := (2235530244873 / 100000000000000 : ℝ))
      (E := (cell12834 ⟨54, by decide⟩).energy) (xi := (4131332338383 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12834 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12834]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12834])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12834) (a := (16444476261023 / 20000000000000 : ℝ)) (b := (160475612613 / 100000000000000 : ℝ)) (q := (2235530244873 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12834])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12834])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12834]

theorem cert12834_55 : CellCertificate 12834 (441492275711027 / 5000000000000000 : ℝ) (1636618092337459 / 1000000000000000000 : ℝ) (4131332338383 / 125000000000000 : ℝ)
    (cell12834 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · have h := gap_lower (n := 12834) (a := (41094372196131 / 50000000000000 : ℝ)) (b := (160475612613 / 100000000000000 : ℝ)) (q := (2235534271531 / 100000000000000 : ℝ))
      (E := (cell12834 ⟨55, by decide⟩).energy) (xi := (4131332338383 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12834 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12834]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12834])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12834) (a := (41094372196131 / 50000000000000 : ℝ)) (b := (160475612613 / 100000000000000 : ℝ)) (q := (2235534271531 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12834])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12834])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12834]

theorem cert12834_56 : CellCertificate 12834 (441492275711027 / 5000000000000000 : ℝ) (1636618092337459 / 1000000000000000000 : ℝ) (4131332338383 / 125000000000000 : ℝ)
    (cell12834 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · have h := gap_lower (n := 12834) (a := (82155130635617 / 100000000000000 : ℝ)) (b := (160475612613 / 100000000000000 : ℝ)) (q := (2235538250233 / 100000000000000 : ℝ))
      (E := (cell12834 ⟨56, by decide⟩).energy) (xi := (4131332338383 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12834 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12834]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12834])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12834) (a := (82155130635617 / 100000000000000 : ℝ)) (b := (160475612613 / 100000000000000 : ℝ)) (q := (2235538250233 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12834])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12834])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12834]

theorem cert12834_57 : CellCertificate 12834 (441492275711027 / 5000000000000000 : ℝ) (1636618092337459 / 1000000000000000000 : ℝ) (4131332338383 / 125000000000000 : ℝ)
    (cell12834 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · have h := gap_lower (n := 12834) (a := (82121540007599 / 100000000000000 : ℝ)) (b := (160475612613 / 100000000000000 : ℝ)) (q := (279442786911 / 12500000000000 : ℝ))
      (E := (cell12834 ⟨57, by decide⟩).energy) (xi := (4131332338383 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12834 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12834]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12834])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12834) (a := (82121540007599 / 100000000000000 : ℝ)) (b := (160475612613 / 100000000000000 : ℝ)) (q := (279442786911 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12834])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12834])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12834]

theorem cert12834_58 : CellCertificate 12834 (441492275711027 / 5000000000000000 : ℝ) (1636618092337459 / 1000000000000000000 : ℝ) (4131332338383 / 125000000000000 : ℝ)
    (cell12834 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · have h := gap_lower (n := 12834) (a := (82087972480763 / 100000000000000 : ℝ)) (b := (160475612613 / 100000000000000 : ℝ)) (q := (2235546284257 / 100000000000000 : ℝ))
      (E := (cell12834 ⟨58, by decide⟩).energy) (xi := (4131332338383 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12834 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12834]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12834])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12834) (a := (82087972480763 / 100000000000000 : ℝ)) (b := (160475612613 / 100000000000000 : ℝ)) (q := (2235546284257 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12834])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12834])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12834]

theorem cert12834_59 : CellCertificate 12834 (441492275711027 / 5000000000000000 : ℝ) (1636618092337459 / 1000000000000000000 : ℝ) (4131332338383 / 125000000000000 : ℝ)
    (cell12834 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · have h := gap_lower (n := 12834) (a := (82054428027801 / 100000000000000 : ℝ)) (b := (160475612613 / 100000000000000 : ℝ)) (q := (223555033113 / 10000000000000 : ℝ))
      (E := (cell12834 ⟨59, by decide⟩).energy) (xi := (4131332338383 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12834 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12834]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12834])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12834) (a := (82054428027801 / 100000000000000 : ℝ)) (b := (160475612613 / 100000000000000 : ℝ)) (q := (223555033113 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12834])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12834])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12834]

theorem cert12835_40 : CellCertificate 12835 (110369646736023 / 1250000000000000 : ℝ) (204561317341373 / 125000000000000000 : ℝ) (8262005556957 / 250000000000000 : ℝ)
    (cell12835 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · have h := gap_lower (n := 12835) (a := (82695742711287 / 100000000000000 : ℝ)) (b := (16046296049 / 10000000000000 : ℝ)) (q := (2235355637203 / 100000000000000 : ℝ))
      (E := (cell12835 ⟨40, by decide⟩).energy) (xi := (8262005556957 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12835 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12835]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12835])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12835) (a := (82695742711287 / 100000000000000 : ℝ)) (b := (16046296049 / 10000000000000 : ℝ)) (q := (2235355637203 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12835])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12835])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12835]

theorem cert12835_41 : CellCertificate 12835 (110369646736023 / 1250000000000000 : ℝ) (204561317341373 / 125000000000000000 : ℝ) (8262005556957 / 250000000000000 : ℝ)
    (cell12835 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · have h := gap_lower (n := 12835) (a := (82661778934389 / 100000000000000 : ℝ)) (b := (16046296049 / 10000000000000 : ℝ)) (q := (2235359623151 / 100000000000000 : ℝ))
      (E := (cell12835 ⟨41, by decide⟩).energy) (xi := (8262005556957 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12835 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12835]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12835])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12835) (a := (82661778934389 / 100000000000000 : ℝ)) (b := (16046296049 / 10000000000000 : ℝ)) (q := (2235359623151 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12835])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12835])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12835]

theorem cert12835_42 : CellCertificate 12835 (110369646736023 / 1250000000000000 : ℝ) (204561317341373 / 125000000000000000 : ℝ) (8262005556957 / 250000000000000 : ℝ)
    (cell12835 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · have h := gap_lower (n := 12835) (a := (82627838714309 / 100000000000000 : ℝ)) (b := (16046296049 / 10000000000000 : ℝ)) (q := (2235363654331 / 100000000000000 : ℝ))
      (E := (cell12835 ⟨42, by decide⟩).energy) (xi := (8262005556957 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12835 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12835]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12835])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12835) (a := (82627838714309 / 100000000000000 : ℝ)) (b := (16046296049 / 10000000000000 : ℝ)) (q := (2235363654331 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12835])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12835])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12835]

theorem cert12835_43 : CellCertificate 12835 (110369646736023 / 1250000000000000 : ℝ) (204561317341373 / 125000000000000000 : ℝ) (8262005556957 / 250000000000000 : ℝ)
    (cell12835 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · have h := gap_lower (n := 12835) (a := (82593922021459 / 100000000000000 : ℝ)) (b := (16046296049 / 10000000000000 : ℝ)) (q := (69855239717 / 3125000000000 : ℝ))
      (E := (cell12835 ⟨43, by decide⟩).energy) (xi := (8262005556957 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12835 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12835]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12835])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12835) (a := (82593922021459 / 100000000000000 : ℝ)) (b := (16046296049 / 10000000000000 : ℝ)) (q := (69855239717 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12835])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12835])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12835]

theorem cert12835_44 : CellCertificate 12835 (110369646736023 / 1250000000000000 : ℝ) (204561317341373 / 125000000000000000 : ℝ) (8262005556957 / 250000000000000 : ℝ)
    (cell12835 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · have h := gap_lower (n := 12835) (a := (82560028826399 / 100000000000000 : ℝ)) (b := (16046296049 / 10000000000000 : ℝ)) (q := (558842917933 / 25000000000000 : ℝ))
      (E := (cell12835 ⟨44, by decide⟩).energy) (xi := (8262005556957 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12835 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12835]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12835])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12835) (a := (82560028826399 / 100000000000000 : ℝ)) (b := (16046296049 / 10000000000000 : ℝ)) (q := (558842917933 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12835])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12835])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12835]

theorem cert12835_45 : CellCertificate 12835 (110369646736023 / 1250000000000000 : ℝ) (204561317341373 / 125000000000000000 : ℝ) (8262005556957 / 250000000000000 : ℝ)
    (cell12835 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · have h := gap_lower (n := 12835) (a := (41263079549917 / 50000000000000 : ℝ)) (b := (16046296049 / 10000000000000 : ℝ)) (q := (1117687827613 / 50000000000000 : ℝ))
      (E := (cell12835 ⟨45, by decide⟩).energy) (xi := (8262005556957 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12835 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12835]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12835])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12835) (a := (41263079549917 / 50000000000000 : ℝ)) (b := (16046296049 / 10000000000000 : ℝ)) (q := (1117687827613 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12835])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12835])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12835]

theorem cert12835_46 : CellCertificate 12835 (110369646736023 / 1250000000000000 : ℝ) (204561317341373 / 125000000000000000 : ℝ) (8262005556957 / 250000000000000 : ℝ)
    (cell12835 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · have h := gap_lower (n := 12835) (a := (82492312812621 / 100000000000000 : ℝ)) (b := (16046296049 / 10000000000000 : ℝ)) (q := (558844919659 / 25000000000000 : ℝ))
      (E := (cell12835 ⟨46, by decide⟩).energy) (xi := (8262005556957 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12835 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12835]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12835])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12835) (a := (82492312812621 / 100000000000000 : ℝ)) (b := (16046296049 / 10000000000000 : ℝ)) (q := (558844919659 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12835])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12835])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12835]

theorem cert12835_47 : CellCertificate 12835 (110369646736023 / 1250000000000000 : ℝ) (204561317341373 / 125000000000000000 : ℝ) (8262005556957 / 250000000000000 : ℝ)
    (cell12835 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · have h := gap_lower (n := 12835) (a := (1030731124197 / 1250000000000 : ℝ)) (b := (16046296049 / 10000000000000 : ℝ)) (q := (558845920301 / 25000000000000 : ℝ))
      (E := (cell12835 ⟨47, by decide⟩).energy) (xi := (8262005556957 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12835 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12835]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12835])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12835) (a := (1030731124197 / 1250000000000 : ℝ)) (b := (16046296049 / 10000000000000 : ℝ)) (q := (558845920301 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12835])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12835])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12835]

theorem cert12835_48 : CellCertificate 12835 (110369646736023 / 1250000000000000 : ℝ) (204561317341373 / 125000000000000000 : ℝ) (8262005556957 / 250000000000000 : ℝ)
    (cell12835 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · have h := gap_lower (n := 12835) (a := (82424690440397 / 100000000000000 : ℝ)) (b := (16046296049 / 10000000000000 : ℝ)) (q := (2235387719763 / 100000000000000 : ℝ))
      (E := (cell12835 ⟨48, by decide⟩).energy) (xi := (8262005556957 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12835 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12835]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12835])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12835) (a := (82424690440397 / 100000000000000 : ℝ)) (b := (16046296049 / 10000000000000 : ℝ)) (q := (2235387719763 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12835])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12835])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12835]

theorem cert12835_49 : CellCertificate 12835 (110369646736023 / 1250000000000000 : ℝ) (204561317341373 / 125000000000000000 : ℝ) (8262005556957 / 250000000000000 : ℝ)
    (cell12835 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · have h := gap_lower (n := 12835) (a := (82390914297823 / 100000000000000 : ℝ)) (b := (16046296049 / 10000000000000 : ℝ)) (q := (55884793327 / 2500000000000 : ℝ))
      (E := (cell12835 ⟨49, by decide⟩).energy) (xi := (8262005556957 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12835 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12835]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12835])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12835) (a := (82390914297823 / 100000000000000 : ℝ)) (b := (16046296049 / 10000000000000 : ℝ)) (q := (55884793327 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12835])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12835])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12835]

theorem cert12835_50 : CellCertificate 12835 (110369646736023 / 1250000000000000 : ℝ) (204561317341373 / 125000000000000000 : ℝ) (8262005556957 / 250000000000000 : ℝ)
    (cell12835 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · have h := gap_lower (n := 12835) (a := (41178580739737 / 50000000000000 : ℝ)) (b := (16046296049 / 10000000000000 : ℝ)) (q := (558848929653 / 25000000000000 : ℝ))
      (E := (cell12835 ⟨50, by decide⟩).energy) (xi := (8262005556957 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12835 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12835]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12835])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12835) (a := (41178580739737 / 50000000000000 : ℝ)) (b := (16046296049 / 10000000000000 : ℝ)) (q := (558848929653 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12835])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12835])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12835]

theorem cert12835_51 : CellCertificate 12835 (110369646736023 / 1250000000000000 : ℝ) (204561317341373 / 125000000000000000 : ℝ) (8262005556957 / 250000000000000 : ℝ)
    (cell12835 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · have h := gap_lower (n := 12835) (a := (1286303624327 / 1562500000000 : ℝ)) (b := (16046296049 / 10000000000000 : ℝ)) (q := (111769986631 / 5000000000000 : ℝ))
      (E := (cell12835 ⟨51, by decide⟩).energy) (xi := (8262005556957 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12835 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12835]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12835])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12835) (a := (1286303624327 / 1562500000000 : ℝ)) (b := (16046296049 / 10000000000000 : ℝ)) (q := (111769986631 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12835])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12835])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12835]

theorem cert12835_52 : CellCertificate 12835 (110369646736023 / 1250000000000000 : ℝ) (204561317341373 / 125000000000000000 : ℝ) (8262005556957 / 250000000000000 : ℝ)
    (cell12835 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · have h := gap_lower (n := 12835) (a := (5143107856369 / 6250000000000 : ℝ)) (b := (16046296049 / 10000000000000 : ℝ)) (q := (139712732073 / 6250000000000 : ℝ))
      (E := (cell12835 ⟨52, by decide⟩).energy) (xi := (8262005556957 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12835 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12835]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12835])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12835) (a := (5143107856369 / 6250000000000 : ℝ)) (b := (16046296049 / 10000000000000 : ℝ)) (q := (139712732073 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12835])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12835])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12835]

theorem cert12835_53 : CellCertificate 12835 (110369646736023 / 1250000000000000 : ℝ) (204561317341373 / 125000000000000000 : ℝ) (8262005556957 / 250000000000000 : ℝ)
    (cell12835 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · have h := gap_lower (n := 12835) (a := (10282005335783 / 12500000000000 : ℝ)) (b := (16046296049 / 10000000000000 : ℝ)) (q := (1117703858073 / 50000000000000 : ℝ))
      (E := (cell12835 ⟨53, by decide⟩).energy) (xi := (8262005556957 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12835 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12835]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12835])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12835) (a := (10282005335783 / 12500000000000 : ℝ)) (b := (16046296049 / 10000000000000 : ℝ)) (q := (1117703858073 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12835])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12835])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12835]

theorem cert12835_54 : CellCertificate 12835 (110369646736023 / 1250000000000000 : ℝ) (204561317341373 / 125000000000000000 : ℝ) (8262005556957 / 250000000000000 : ℝ)
    (cell12835 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · have h := gap_lower (n := 12835) (a := (82222382882011 / 100000000000000 : ℝ)) (b := (16046296049 / 10000000000000 : ℝ)) (q := (558852934559 / 25000000000000 : ℝ))
      (E := (cell12835 ⟨54, by decide⟩).energy) (xi := (8262005556957 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12835 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12835]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12835])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12835) (a := (82222382882011 / 100000000000000 : ℝ)) (b := (16046296049 / 10000000000000 : ℝ)) (q := (558852934559 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12835])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12835])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12835]

theorem cert12835_55 : CellCertificate 12835 (110369646736023 / 1250000000000000 : ℝ) (204561317341373 / 125000000000000000 : ℝ) (8262005556957 / 250000000000000 : ℝ)
    (cell12835 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · have h := gap_lower (n := 12835) (a := (16437749252257 / 20000000000000 : ℝ)) (b := (16046296049 / 10000000000000 : ℝ)) (q := (447083155183 / 20000000000000 : ℝ))
      (E := (cell12835 ⟨55, by decide⟩).energy) (xi := (8262005556957 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12835 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12835]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12835])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12835) (a := (16437749252257 / 20000000000000 : ℝ)) (b := (16046296049 / 10000000000000 : ℝ)) (q := (447083155183 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12835])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12835])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12835]

theorem cert12835_56 : CellCertificate 12835 (110369646736023 / 1250000000000000 : ℝ) (204561317341373 / 125000000000000000 : ℝ) (8262005556957 / 250000000000000 : ℝ)
    (cell12835 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · have h := gap_lower (n := 12835) (a := (82155132796367 / 100000000000000 : ℝ)) (b := (16046296049 / 10000000000000 : ℝ)) (q := (558854941579 / 25000000000000 : ℝ))
      (E := (cell12835 ⟨56, by decide⟩).energy) (xi := (8262005556957 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12835 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12835]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12835])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12835) (a := (82155132796367 / 100000000000000 : ℝ)) (b := (16046296049 / 10000000000000 : ℝ)) (q := (558854941579 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12835])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12835])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12835]

theorem cert12835_57 : CellCertificate 12835 (110369646736023 / 1250000000000000 : ℝ) (204561317341373 / 125000000000000000 : ℝ) (8262005556957 / 250000000000000 : ℝ)
    (cell12835 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · have h := gap_lower (n := 12835) (a := (20530385614919 / 25000000000000 : ℝ)) (b := (16046296049 / 10000000000000 : ℝ)) (q := (558855941147 / 25000000000000 : ℝ))
      (E := (cell12835 ⟨57, by decide⟩).energy) (xi := (8262005556957 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12835 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12835]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12835])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12835) (a := (20530385614919 / 25000000000000 : ℝ)) (b := (16046296049 / 10000000000000 : ℝ)) (q := (558855941147 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12835])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12835])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12835]

theorem cert12835_58 : CellCertificate 12835 (110369646736023 / 1250000000000000 : ℝ) (204561317341373 / 125000000000000000 : ℝ) (8262005556957 / 250000000000000 : ℝ)
    (cell12835 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · have h := gap_lower (n := 12835) (a := (10260996902971 / 12500000000000 : ℝ)) (b := (16046296049 / 10000000000000 : ℝ)) (q := (279428470823 / 12500000000000 : ℝ))
      (E := (cell12835 ⟨58, by decide⟩).energy) (xi := (8262005556957 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12835 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12835]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12835])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12835) (a := (10260996902971 / 12500000000000 : ℝ)) (b := (16046296049 / 10000000000000 : ℝ)) (q := (279428470823 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12835])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12835])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12835]

theorem cert12835_59 : CellCertificate 12835 (110369646736023 / 1250000000000000 : ℝ) (204561317341373 / 125000000000000000 : ℝ) (8262005556957 / 250000000000000 : ℝ)
    (cell12835 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · have h := gap_lower (n := 12835) (a := (16410886212267 / 20000000000000 : ℝ)) (b := (16046296049 / 10000000000000 : ℝ)) (q := (447086353591 / 20000000000000 : ℝ))
      (E := (cell12835 ⟨59, by decide⟩).energy) (xi := (8262005556957 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12835 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12835]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12835])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12835) (a := (16410886212267 / 20000000000000 : ℝ)) (b := (16046296049 / 10000000000000 : ℝ)) (q := (447086353591 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12835])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12835])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12835]

theorem cert12836_40 : CellCertificate 12836 (441464900222923 / 5000000000000000 : ℝ) (102272687812833 / 62500000000000000 : ℝ) (330453861739363 / 10000000000000000 : ℝ)
    (cell12836 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · have h := gap_lower (n := 12836) (a := (82695740156799 / 100000000000000 : ℝ)) (b := (160450310373 / 100000000000000 : ℝ)) (q := (558809290543 / 25000000000000 : ℝ))
      (E := (cell12836 ⟨40, by decide⟩).energy) (xi := (330453861739363 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12836 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12836]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12836])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12836) (a := (82695740156799 / 100000000000000 : ℝ)) (b := (160450310373 / 100000000000000 : ℝ)) (q := (558809290543 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12836])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12836])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12836]

theorem cert12836_41 : CellCertificate 12836 (441464900222923 / 5000000000000000 : ℝ) (102272687812833 / 62500000000000000 : ℝ) (330453861739363 / 10000000000000000 : ℝ)
    (cell12836 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · have h := gap_lower (n := 12836) (a := (82661776677673 / 100000000000000 : ℝ)) (b := (160450310373 / 100000000000000 : ℝ)) (q := (1117620574839 / 50000000000000 : ℝ))
      (E := (cell12836 ⟨41, by decide⟩).energy) (xi := (330453861739363 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12836 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12836]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12836])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12836) (a := (82661776677673 / 100000000000000 : ℝ)) (b := (160450310373 / 100000000000000 : ℝ)) (q := (1117620574839 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12836])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12836])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12836]

theorem cert12836_42 : CellCertificate 12836 (441464900222923 / 5000000000000000 : ℝ) (102272687812833 / 62500000000000000 : ℝ) (330453861739363 / 10000000000000000 : ℝ)
    (cell12836 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · have h := gap_lower (n := 12836) (a := (16525567350991 / 20000000000000 : ℝ)) (b := (160450310373 / 100000000000000 : ℝ)) (q := (2235245183103 / 100000000000000 : ℝ))
      (E := (cell12836 ⟨42, by decide⟩).energy) (xi := (330453861739363 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12836 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12836]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12836])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12836) (a := (16525567350991 / 20000000000000 : ℝ)) (b := (160450310373 / 100000000000000 : ℝ)) (q := (2235245183103 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12836])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12836])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12836]

theorem cert12836_43 : CellCertificate 12836 (441464900222923 / 5000000000000000 : ℝ) (102272687812833 / 62500000000000000 : ℝ) (330453861739363 / 10000000000000000 : ℝ)
    (cell12836 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · have h := gap_lower (n := 12836) (a := (82593920359057 / 100000000000000 : ℝ)) (b := (160450310373 / 100000000000000 : ℝ)) (q := (447049828763 / 20000000000000 : ℝ))
      (E := (cell12836 ⟨43, by decide⟩).energy) (xi := (330453861739363 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12836 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12836]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12836])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12836) (a := (82593920359057 / 100000000000000 : ℝ)) (b := (160450310373 / 100000000000000 : ℝ)) (q := (447049828763 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12836])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12836])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12836]

theorem cert12836_44 : CellCertificate 12836 (441464900222923 / 5000000000000000 : ℝ) (102272687812833 / 62500000000000000 : ℝ) (330453861739363 / 10000000000000000 : ℝ)
    (cell12836 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · have h := gap_lower (n := 12836) (a := (82560027460539 / 100000000000000 : ℝ)) (b := (160450310373 / 100000000000000 : ℝ)) (q := (558813287049 / 25000000000000 : ℝ))
      (E := (cell12836 ⟨44, by decide⟩).energy) (xi := (330453861739363 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12836 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12836]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12836])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12836) (a := (82560027460539 / 100000000000000 : ℝ)) (b := (160450310373 / 100000000000000 : ℝ)) (q := (558813287049 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12836])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12836])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12836]

theorem cert12836_45 : CellCertificate 12836 (441464900222923 / 5000000000000000 : ℝ) (102272687812833 / 62500000000000000 : ℝ) (330453861739363 / 10000000000000000 : ℝ)
    (cell12836 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · have h := gap_lower (n := 12836) (a := (8252615803011 / 10000000000000 : ℝ)) (b := (160450310373 / 100000000000000 : ℝ)) (q := (2235257194843 / 100000000000000 : ℝ))
      (E := (cell12836 ⟨45, by decide⟩).energy) (xi := (330453861739363 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12836 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12836]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12836])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12836) (a := (8252615803011 / 10000000000000 : ℝ)) (b := (160450310373 / 100000000000000 : ℝ)) (q := (2235257194843 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12836])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12836])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12836]

theorem cert12836_46 : CellCertificate 12836 (441464900222923 / 5000000000000000 : ℝ) (102272687812833 / 62500000000000000 : ℝ) (330453861739363 / 10000000000000000 : ℝ)
    (cell12836 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · have h := gap_lower (n := 12836) (a := (82492312038623 / 100000000000000 : ℝ)) (b := (160450310373 / 100000000000000 : ℝ)) (q := (447052232867 / 20000000000000 : ℝ))
      (E := (cell12836 ⟨46, by decide⟩).energy) (xi := (330453861739363 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12836 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12836]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12836])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12836) (a := (82492312038623 / 100000000000000 : ℝ)) (b := (160450310373 / 100000000000000 : ℝ)) (q := (447052232867 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12836])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12836])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12836]

theorem cert12836_47 : CellCertificate 12836 (441464900222923 / 5000000000000000 : ℝ) (102272687812833 / 62500000000000000 : ℝ) (330453861739363 / 10000000000000000 : ℝ)
    (cell12836 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · have h := gap_lower (n := 12836) (a := (82458489457083 / 100000000000000 : ℝ)) (b := (160450310373 / 100000000000000 : ℝ)) (q := (1117632586273 / 50000000000000 : ℝ))
      (E := (cell12836 ⟨47, by decide⟩).energy) (xi := (330453861739363 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12836 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12836]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12836])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12836) (a := (82458489457083 / 100000000000000 : ℝ)) (b := (160450310373 / 100000000000000 : ℝ)) (q := (1117632586273 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12836])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12836])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12836]

theorem cert12836_48 : CellCertificate 12836 (441464900222923 / 5000000000000000 : ℝ) (102272687812833 / 62500000000000000 : ℝ) (330453861739363 / 10000000000000000 : ℝ)
    (cell12836 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · have h := gap_lower (n := 12836) (a := (41212345128317 / 50000000000000 : ℝ)) (b := (160450310373 / 100000000000000 : ℝ)) (q := (2235269217431 / 100000000000000 : ℝ))
      (E := (cell12836 ⟨48, by decide⟩).energy) (xi := (330453861739363 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12836 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12836]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12836])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12836) (a := (41212345128317 / 50000000000000 : ℝ)) (b := (160450310373 / 100000000000000 : ℝ)) (q := (2235269217431 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12836])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12836])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12836]

theorem cert12836_49 : CellCertificate 12836 (441464900222923 / 5000000000000000 : ℝ) (102272687812833 / 62500000000000000 : ℝ) (330453861739363 / 10000000000000000 : ℝ)
    (cell12836 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · have h := gap_lower (n := 12836) (a := (8239091440857 / 10000000000000 : ℝ)) (b := (160450310373 / 100000000000000 : ℝ)) (q := (2235273237753 / 100000000000000 : ℝ))
      (E := (cell12836 ⟨49, by decide⟩).energy) (xi := (330453861739363 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12836 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12836]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12836])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12836) (a := (8239091440857 / 10000000000000 : ℝ)) (b := (160450310373 / 100000000000000 : ℝ)) (q := (2235273237753 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12836])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12836])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12836]

theorem cert12836_50 : CellCertificate 12836 (441464900222923 / 5000000000000000 : ℝ) (102272687812833 / 62500000000000000 : ℝ) (330453861739363 / 10000000000000000 : ℝ)
    (cell12836 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · have h := gap_lower (n := 12836) (a := (41178580942163 / 50000000000000 : ℝ)) (b := (160450310373 / 100000000000000 : ℝ)) (q := (2235277230971 / 100000000000000 : ℝ))
      (E := (cell12836 ⟨50, by decide⟩).energy) (xi := (330453861739363 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12836 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12836]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12836])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12836) (a := (41178580942163 / 50000000000000 : ℝ)) (b := (160450310373 / 100000000000000 : ℝ)) (q := (2235277230971 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12836])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12836])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12836]

theorem cert12836_51 : CellCertificate 12836 (441464900222923 / 5000000000000000 : ℝ) (102272687812833 / 62500000000000000 : ℝ) (330453861739363 / 10000000000000000 : ℝ)
    (cell12836 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · have h := gap_lower (n := 12836) (a := (82323432655481 / 100000000000000 : ℝ)) (b := (160450310373 / 100000000000000 : ℝ)) (q := (2235281253347 / 100000000000000 : ℝ))
      (E := (cell12836 ⟨51, by decide⟩).energy) (xi := (330453861739363 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12836 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12836]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12836])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12836) (a := (82323432655481 / 100000000000000 : ℝ)) (b := (160450310373 / 100000000000000 : ℝ)) (q := (2235281253347 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12836])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12836])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12836]

theorem cert12836_52 : CellCertificate 12836 (441464900222923 / 5000000000000000 : ℝ) (102272687812833 / 62500000000000000 : ℝ) (330453861739363 / 10000000000000000 : ℝ)
    (cell12836 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · have h := gap_lower (n := 12836) (a := (41144863346877 / 50000000000000 : ℝ)) (b := (160450310373 / 100000000000000 : ℝ)) (q := (2235285242943 / 100000000000000 : ℝ))
      (E := (cell12836 ⟨52, by decide⟩).energy) (xi := (330453861739363 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12836 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12836]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12836])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12836) (a := (41144863346877 / 50000000000000 : ℝ)) (b := (160450310373 / 100000000000000 : ℝ)) (q := (2235285242943 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12836])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12836])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12836]

theorem cert12836_53 : CellCertificate 12836 (441464900222923 / 5000000000000000 : ℝ) (102272687812833 / 62500000000000000 : ℝ) (330453861739363 / 10000000000000000 : ℝ)
    (cell12836 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · have h := gap_lower (n := 12836) (a := (8225604397101 / 10000000000000 : ℝ)) (b := (160450310373 / 100000000000000 : ℝ)) (q := (447057851129 / 20000000000000 : ℝ))
      (E := (cell12836 ⟨53, by decide⟩).energy) (xi := (330453861739363 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12836 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12836]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12836])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12836) (a := (8225604397101 / 10000000000000 : ℝ)) (b := (160450310373 / 100000000000000 : ℝ)) (q := (447057851129 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12836])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12836])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12836]

theorem cert12836_54 : CellCertificate 12836 (441464900222923 / 5000000000000000 : ℝ) (102272687812833 / 62500000000000000 : ℝ) (330453861739363 / 10000000000000000 : ℝ)
    (cell12836 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · have h := gap_lower (n := 12836) (a := (82222384459249 / 100000000000000 : ℝ)) (b := (160450310373 / 100000000000000 : ℝ)) (q := (558823307263 / 25000000000000 : ℝ))
      (E := (cell12836 ⟨54, by decide⟩).energy) (xi := (330453861739363 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12836 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12836]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12836])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12836) (a := (82222384459249 / 100000000000000 : ℝ)) (b := (160450310373 / 100000000000000 : ℝ)) (q := (558823307263 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12836])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12836])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12836]

theorem cert12836_55 : CellCertificate 12836 (441464900222923 / 5000000000000000 : ℝ) (102272687812833 / 62500000000000000 : ℝ) (330453861739363 / 10000000000000000 : ℝ)
    (cell12836 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · have h := gap_lower (n := 12836) (a := (10273593516327 / 12500000000000 : ℝ)) (b := (160450310373 / 100000000000000 : ℝ)) (q := (2235297277789 / 100000000000000 : ℝ))
      (E := (cell12836 ⟨55, by decide⟩).energy) (xi := (330453861739363 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12836 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12836]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12836])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12836) (a := (10273593516327 / 12500000000000 : ℝ)) (b := (160450310373 / 100000000000000 : ℝ)) (q := (2235297277789 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12836])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12836])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12836]

theorem cert12836_56 : CellCertificate 12836 (441464900222923 / 5000000000000000 : ℝ) (102272687812833 / 62500000000000000 : ℝ) (330453861739363 / 10000000000000000 : ℝ)
    (cell12836 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · have h := gap_lower (n := 12836) (a := (8215513495739 / 10000000000000 : ℝ)) (b := (160450310373 / 100000000000000 : ℝ)) (q := (558825319981 / 25000000000000 : ℝ))
      (E := (cell12836 ⟨56, by decide⟩).energy) (xi := (330453861739363 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12836 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12836]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12836])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12836) (a := (8215513495739 / 10000000000000 : ℝ)) (b := (160450310373 / 100000000000000 : ℝ)) (q := (558825319981 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12836])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12836])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12836]

theorem cert12836_57 : CellCertificate 12836 (441464900222923 / 5000000000000000 : ℝ) (102272687812833 / 62500000000000000 : ℝ) (330453861739363 / 10000000000000000 : ℝ)
    (cell12836 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · have h := gap_lower (n := 12836) (a := (82121544911991 / 100000000000000 : ℝ)) (b := (160450310373 / 100000000000000 : ℝ)) (q := (2235305290607 / 100000000000000 : ℝ))
      (E := (cell12836 ⟨57, by decide⟩).energy) (xi := (330453861739363 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12836 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12836]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12836])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12836) (a := (82121544911991 / 100000000000000 : ℝ)) (b := (160450310373 / 100000000000000 : ℝ)) (q := (2235305290607 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12836])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12836])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12836]

theorem cert12836_58 : CellCertificate 12836 (441464900222923 / 5000000000000000 : ℝ) (102272687812833 / 62500000000000000 : ℝ) (330453861739363 / 10000000000000000 : ℝ)
    (cell12836 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · have h := gap_lower (n := 12836) (a := (641312327867 / 781250000000 : ℝ)) (b := (160450310373 / 100000000000000 : ℝ)) (q := (2235309305691 / 100000000000000 : ℝ))
      (E := (cell12836 ⟨58, by decide⟩).energy) (xi := (330453861739363 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12836 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12836]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12836])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12836) (a := (641312327867 / 781250000000 : ℝ)) (b := (160450310373 / 100000000000000 : ℝ)) (q := (2235309305691 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12836])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12836])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12836]

theorem cert12836_59 : CellCertificate 12836 (441464900222923 / 5000000000000000 : ℝ) (102272687812833 / 62500000000000000 : ℝ) (330453861739363 / 10000000000000000 : ℝ)
    (cell12836 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · have h := gap_lower (n := 12836) (a := (41027217047519 / 50000000000000 : ℝ)) (b := (160450310373 / 100000000000000 : ℝ)) (q := (1117656660411 / 50000000000000 : ℝ))
      (E := (cell12836 ⟨59, by decide⟩).energy) (xi := (330453861739363 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12836 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12836]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12836])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12836) (a := (41027217047519 / 50000000000000 : ℝ)) (b := (160450310373 / 100000000000000 : ℝ)) (q := (1117656660411 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12836])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12836])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12836]

theorem cert12837_40 : CellCertificate 12837 (882902431094077 / 10000000000000000 : ℝ) (818117745577921 / 500000000000000000 : ℝ) (165213752726391 / 5000000000000000 : ℝ)
    (cell12837 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · have h := gap_lower (n := 12837) (a := (1653914752063 / 2000000000000 : ℝ)) (b := (160437662263 / 100000000000000 : ℝ)) (q := (447023736817 / 20000000000000 : ℝ))
      (E := (cell12837 ⟨40, by decide⟩).energy) (xi := (165213752726391 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12837 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12837]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12837])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12837) (a := (1653914752063 / 2000000000000 : ℝ)) (b := (160437662263 / 100000000000000 : ℝ)) (q := (447023736817 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12837])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12837])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12837]

theorem cert12837_41 : CellCertificate 12837 (882902431094077 / 10000000000000000 : ℝ) (818117745577921 / 500000000000000000 : ℝ) (165213752726391 / 5000000000000000 : ℝ)
    (cell12837 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · have h := gap_lower (n := 12837) (a := (82661774421759 / 100000000000000 : ℝ)) (b := (160437662263 / 100000000000000 : ℝ)) (q := (2235122673187 / 100000000000000 : ℝ))
      (E := (cell12837 ⟨41, by decide⟩).energy) (xi := (165213752726391 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12837 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12837]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12837])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12837) (a := (82661774421759 / 100000000000000 : ℝ)) (b := (160437662263 / 100000000000000 : ℝ)) (q := (2235122673187 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12837])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12837])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12837]

theorem cert12837_42 : CellCertificate 12837 (882902431094077 / 10000000000000000 : ℝ) (818117745577921 / 500000000000000000 : ℝ) (165213752726391 / 5000000000000000 : ℝ)
    (cell12837 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · have h := gap_lower (n := 12837) (a := (82627834796367 / 100000000000000 : ℝ)) (b := (160437662263 / 100000000000000 : ℝ)) (q := (2235126708893 / 100000000000000 : ℝ))
      (E := (cell12837 ⟨42, by decide⟩).energy) (xi := (165213752726391 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12837 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12837]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12837])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12837) (a := (82627834796367 / 100000000000000 : ℝ)) (b := (160437662263 / 100000000000000 : ℝ)) (q := (2235126708893 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12837])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12837])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12837]

theorem cert12837_43 : CellCertificate 12837 (882902431094077 / 10000000000000000 : ℝ) (818117745577921 / 500000000000000000 : ℝ) (165213752726391 / 5000000000000000 : ℝ)
    (cell12837 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · have h := gap_lower (n := 12837) (a := (41296959348693 / 50000000000000 : ℝ)) (b := (160437662263 / 100000000000000 : ℝ)) (q := (1117565365701 / 50000000000000 : ℝ))
      (E := (cell12837 ⟨43, by decide⟩).energy) (xi := (165213752726391 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12837 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12837]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12837])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12837) (a := (41296959348693 / 50000000000000 : ℝ)) (b := (160437662263 / 100000000000000 : ℝ)) (q := (1117565365701 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12837])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12837])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12837]

theorem cert12837_44 : CellCertificate 12837 (882902431094077 / 10000000000000000 : ℝ) (818117745577921 / 500000000000000000 : ℝ) (165213752726391 / 5000000000000000 : ℝ)
    (cell12837 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · have h := gap_lower (n := 12837) (a := (660480208763 / 800000000000 : ℝ)) (b := (160437662263 / 100000000000000 : ℝ)) (q := (2235134739459 / 100000000000000 : ℝ))
      (E := (cell12837 ⟨44, by decide⟩).energy) (xi := (165213752726391 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12837 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12837]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12837])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12837) (a := (660480208763 / 800000000000 : ℝ)) (b := (160437662263 / 100000000000000 : ℝ)) (q := (2235134739459 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12837])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12837])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12837]

theorem cert12837_45 : CellCertificate 12837 (882902431094077 / 10000000000000000 : ℝ) (818117745577921 / 500000000000000000 : ℝ) (165213752726391 / 5000000000000000 : ℝ)
    (cell12837 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · have h := gap_lower (n := 12837) (a := (16505231392209 / 20000000000000 : ℝ)) (b := (160437662263 / 100000000000000 : ℝ)) (q := (2235138731587 / 100000000000000 : ℝ))
      (E := (cell12837 ⟨45, by decide⟩).energy) (xi := (165213752726391 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12837 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12837]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12837])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12837) (a := (16505231392209 / 20000000000000 : ℝ)) (b := (160437662263 / 100000000000000 : ℝ)) (q := (2235138731587 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12837])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12837])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12837]

theorem cert12837_46 : CellCertificate 12837 (882902431094077 / 10000000000000000 : ℝ) (818117745577921 / 500000000000000000 : ℝ) (165213752726391 / 5000000000000000 : ℝ)
    (cell12837 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · have h := gap_lower (n := 12837) (a := (82492311265251 / 100000000000000 : ℝ)) (b := (160437662263 / 100000000000000 : ℝ)) (q := (1117571353049 / 50000000000000 : ℝ))
      (E := (cell12837 ⟨46, by decide⟩).energy) (xi := (165213752726391 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12837 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12837]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12837])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12837) (a := (82492311265251 / 100000000000000 : ℝ)) (b := (160437662263 / 100000000000000 : ℝ)) (q := (1117571353049 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12837])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12837])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12837]

theorem cert12837_47 : CellCertificate 12837 (882902431094077 / 10000000000000000 : ℝ) (818117745577921 / 500000000000000000 : ℝ) (165213752726391 / 5000000000000000 : ℝ)
    (cell12837 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · have h := gap_lower (n := 12837) (a := (16491697795799 / 20000000000000 : ℝ)) (b := (160437662263 / 100000000000000 : ℝ)) (q := (2235146720013 / 100000000000000 : ℝ))
      (E := (cell12837 ⟨47, by decide⟩).energy) (xi := (165213752726391 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12837 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12837]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12837])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12837) (a := (16491697795799 / 20000000000000 : ℝ)) (b := (160437662263 / 100000000000000 : ℝ)) (q := (2235146720013 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12837])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12837])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12837]

theorem cert12837_48 : CellCertificate 12837 (882902431094077 / 10000000000000000 : ℝ) (818117745577921 / 500000000000000000 : ℝ) (165213752726391 / 5000000000000000 : ℝ)
    (cell12837 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · have h := gap_lower (n := 12837) (a := (41212345036713 / 50000000000000 : ℝ)) (b := (160437662263 / 100000000000000 : ℝ)) (q := (2235150771281 / 100000000000000 : ℝ))
      (E := (cell12837 ⟨48, by decide⟩).energy) (xi := (165213752726391 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12837 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12837]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12837])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12837) (a := (41212345036713 / 50000000000000 : ℝ)) (b := (160437662263 / 100000000000000 : ℝ)) (q := (2235150771281 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12837])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12837])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12837]

theorem cert12837_49 : CellCertificate 12837 (882902431094077 / 10000000000000000 : ℝ) (818117745577921 / 500000000000000000 : ℝ) (165213752726391 / 5000000000000000 : ℝ)
    (cell12837 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · have h := gap_lower (n := 12837) (a := (20597728629959 / 25000000000000 : ℝ)) (b := (160437662263 / 100000000000000 : ℝ)) (q := (1117577369849 / 50000000000000 : ℝ))
      (E := (cell12837 ⟨49, by decide⟩).energy) (xi := (165213752726391 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12837 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12837]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12837])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12837) (a := (20597728629959 / 25000000000000 : ℝ)) (b := (160437662263 / 100000000000000 : ℝ)) (q := (1117577369849 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12837])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12837])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12837]

theorem cert12837_50 : CellCertificate 12837 (882902431094077 / 10000000000000000 : ℝ) (818117745577921 / 500000000000000000 : ℝ) (165213752726391 / 5000000000000000 : ℝ)
    (cell12837 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · have h := gap_lower (n := 12837) (a := (82357162289661 / 100000000000000 : ℝ)) (b := (160437662263 / 100000000000000 : ℝ)) (q := (13969742129 / 625000000000 : ℝ))
      (E := (cell12837 ⟨50, by decide⟩).energy) (xi := (165213752726391 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12837 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12837]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12837])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12837) (a := (82357162289661 / 100000000000000 : ℝ)) (b := (160437662263 / 100000000000000 : ℝ)) (q := (13969742129 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12837])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12837])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12837]

theorem cert12837_51 : CellCertificate 12837 (882902431094077 / 10000000000000000 : ℝ) (818117745577921 / 500000000000000000 : ℝ) (165213752726391 / 5000000000000000 : ℝ)
    (cell12837 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · have h := gap_lower (n := 12837) (a := (82323433354481 / 100000000000000 : ℝ)) (b := (160437662263 / 100000000000000 : ℝ)) (q := (2235162771419 / 100000000000000 : ℝ))
      (E := (cell12837 ⟨51, by decide⟩).energy) (xi := (165213752726391 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12837 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12837]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12837])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12837) (a := (82323433354481 / 100000000000000 : ℝ)) (b := (160437662263 / 100000000000000 : ℝ)) (q := (2235162771419 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12837])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12837])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12837]

theorem cert12837_52 : CellCertificate 12837 (882902431094077 / 10000000000000000 : ℝ) (818117745577921 / 500000000000000000 : ℝ) (165213752726391 / 5000000000000000 : ℝ)
    (cell12837 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · have h := gap_lower (n := 12837) (a := (41144863843009 / 50000000000000 : ℝ)) (b := (160437662263 / 100000000000000 : ℝ)) (q := (2235166770097 / 100000000000000 : ℝ))
      (E := (cell12837 ⟨52, by decide⟩).energy) (xi := (165213752726391 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12837 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12837]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12837])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12837) (a := (41144863843009 / 50000000000000 : ℝ)) (b := (160437662263 / 100000000000000 : ℝ)) (q := (2235166770097 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12837])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12837])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12837]

theorem cert12837_53 : CellCertificate 12837 (882902431094077 / 10000000000000000 : ℝ) (818117745577921 / 500000000000000000 : ℝ) (165213752726391 / 5000000000000000 : ℝ)
    (cell12837 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · have h := gap_lower (n := 12837) (a := (82256045256133 / 100000000000000 : ℝ)) (b := (160437662263 / 100000000000000 : ℝ)) (q := (1117585396281 / 50000000000000 : ℝ))
      (E := (cell12837 ⟨53, by decide⟩).energy) (xi := (165213752726391 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12837 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12837]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12837])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12837) (a := (82256045256133 / 100000000000000 : ℝ)) (b := (160437662263 / 100000000000000 : ℝ)) (q := (1117585396281 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12837])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12837])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12837]

theorem cert12837_54 : CellCertificate 12837 (882902431094077 / 10000000000000000 : ℝ) (818117745577921 / 500000000000000000 : ℝ) (165213752726391 / 5000000000000000 : ℝ)
    (cell12837 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · have h := gap_lower (n := 12837) (a := (82222386036831 / 100000000000000 : ℝ)) (b := (160437662263 / 100000000000000 : ℝ)) (q := (2235174776407 / 100000000000000 : ℝ))
      (E := (cell12837 ⟨54, by decide⟩).energy) (xi := (165213752726391 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12837 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12837]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12837])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12837) (a := (82222386036831 / 100000000000000 : ℝ)) (b := (160437662263 / 100000000000000 : ℝ)) (q := (2235174776407 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12837])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12837])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12837]

theorem cert12837_55 : CellCertificate 12837 (882902431094077 / 10000000000000000 : ℝ) (818117745577921 / 500000000000000000 : ℝ) (165213752726391 / 5000000000000000 : ℝ)
    (cell12837 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · have h := gap_lower (n := 12837) (a := (16437750000051 / 20000000000000 : ℝ)) (b := (160437662263 / 100000000000000 : ℝ)) (q := (2235178777149 / 100000000000000 : ℝ))
      (E := (cell12837 ⟨55, by decide⟩).energy) (xi := (165213752726391 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12837 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12837]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12837])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12837) (a := (16437750000051 / 20000000000000 : ℝ)) (b := (160437662263 / 100000000000000 : ℝ)) (q := (2235178777149 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12837])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12837])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12837]

theorem cert12837_56 : CellCertificate 12837 (882902431094077 / 10000000000000000 : ℝ) (818117745577921 / 500000000000000000 : ℝ) (165213752726391 / 5000000000000000 : ℝ)
    (cell12837 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · have h := gap_lower (n := 12837) (a := (41077568559343 / 50000000000000 : ℝ)) (b := (160437662263 / 100000000000000 : ℝ)) (q := (139698924441 / 6250000000000 : ℝ))
      (E := (cell12837 ⟨56, by decide⟩).energy) (xi := (165213752726391 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12837 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12837]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12837])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12837) (a := (41077568559343 / 50000000000000 : ℝ)) (b := (160437662263 / 100000000000000 : ℝ)) (q := (139698924441 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12837])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12837])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12837]

theorem cert12837_57 : CellCertificate 12837 (882902431094077 / 10000000000000000 : ℝ) (818117745577921 / 500000000000000000 : ℝ) (165213752726391 / 5000000000000000 : ℝ)
    (cell12837 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · have h := gap_lower (n := 12837) (a := (1283149177571 / 1562500000000 : ℝ)) (b := (160437662263 / 100000000000000 : ℝ)) (q := (1117593407093 / 50000000000000 : ℝ))
      (E := (cell12837 ⟨57, by decide⟩).energy) (xi := (165213752726391 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12837 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12837]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12837])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12837) (a := (1283149177571 / 1562500000000 : ℝ)) (b := (160437662263 / 100000000000000 : ℝ)) (q := (1117593407093 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12837])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12837])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12837]

theorem cert12837_58 : CellCertificate 12837 (882902431094077 / 10000000000000000 : ℝ) (818117745577921 / 500000000000000000 : ℝ) (165213752726391 / 5000000000000000 : ℝ)
    (cell12837 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · have h := gap_lower (n := 12837) (a := (20521995177597 / 25000000000000 : ℝ)) (b := (160437662263 / 100000000000000 : ℝ)) (q := (2235190842391 / 100000000000000 : ℝ))
      (E := (cell12837 ⟨58, by decide⟩).energy) (xi := (165213752726391 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12837 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12837]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12837])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12837) (a := (20521995177597 / 25000000000000 : ℝ)) (b := (160437662263 / 100000000000000 : ℝ)) (q := (2235190842391 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12837])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12837])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12837]

theorem cert12837_59 : CellCertificate 12837 (882902431094077 / 10000000000000000 : ℝ) (818117745577921 / 500000000000000000 : ℝ) (165213752726391 / 5000000000000000 : ℝ)
    (cell12837 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · have h := gap_lower (n := 12837) (a := (8205443712891 / 10000000000000 : ℝ)) (b := (160437662263 / 100000000000000 : ℝ)) (q := (2235194812113 / 100000000000000 : ℝ))
      (E := (cell12837 ⟨59, by decide⟩).energy) (xi := (165213752726391 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12837 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12837]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12837])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12837) (a := (8205443712891 / 10000000000000 : ℝ)) (b := (160437662263 / 100000000000000 : ℝ)) (q := (2235194812113 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12837])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12837])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12837]

theorem cert12838_40 : CellCertificate 12838 (220718766457979 / 2500000000000000 : ℝ) (1636107997177879 / 1000000000000000000 : ℝ) (330401153417431 / 10000000000000000 : ℝ)
    (cell12838 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · have h := gap_lower (n := 12838) (a := (41347867525169 / 50000000000000 : ℝ)) (b := (80212508079 / 50000000000000 : ℝ)) (q := (2235000261707 / 100000000000000 : ℝ))
      (E := (cell12838 ⟨40, by decide⟩).energy) (xi := (330401153417431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12838 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12838]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12838])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12838) (a := (41347867525169 / 50000000000000 : ℝ)) (b := (80212508079 / 50000000000000 : ℝ)) (q := (2235000261707 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12838])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12838])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12838]

theorem cert12838_41 : CellCertificate 12838 (220718766457979 / 2500000000000000 : ℝ) (1636107997177879 / 1000000000000000000 : ℝ) (330401153417431 / 10000000000000000 : ℝ)
    (cell12838 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · have h := gap_lower (n := 12838) (a := (10332721520831 / 12500000000000 : ℝ)) (b := (80212508079 / 50000000000000 : ℝ)) (q := (2235004252463 / 100000000000000 : ℝ))
      (E := (cell12838 ⟨41, by decide⟩).energy) (xi := (330401153417431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12838 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12838]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12838])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12838) (a := (10332721520831 / 12500000000000 : ℝ)) (b := (80212508079 / 50000000000000 : ℝ)) (q := (2235004252463 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12838])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12838])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12838]

theorem cert12838_42 : CellCertificate 12838 (220718766457979 / 2500000000000000 : ℝ) (1636107997177879 / 1000000000000000000 : ℝ) (330401153417431 / 10000000000000000 : ℝ)
    (cell12838 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · have h := gap_lower (n := 12838) (a := (41313916419273 / 50000000000000 : ℝ)) (b := (80212508079 / 50000000000000 : ℝ)) (q := (223500829051 / 10000000000000 : ℝ))
      (E := (cell12838 ⟨42, by decide⟩).energy) (xi := (330401153417431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12838 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12838]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12838])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12838) (a := (41313916419273 / 50000000000000 : ℝ)) (b := (80212508079 / 50000000000000 : ℝ)) (q := (223500829051 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12838])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12838])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12838]

theorem cert12838_43 : CellCertificate 12838 (220718766457979 / 2500000000000000 : ℝ) (1636107997177879 / 1000000000000000000 : ℝ) (330401153417431 / 10000000000000000 : ℝ)
    (cell12838 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · have h := gap_lower (n := 12838) (a := (16518783407289 / 20000000000000 : ℝ)) (b := (80212508079 / 50000000000000 : ℝ)) (q := (34922066519 / 1562500000000 : ℝ))
      (E := (cell12838 ⟨43, by decide⟩).energy) (xi := (330401153417431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12838 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12838]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12838])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12838) (a := (16518783407289 / 20000000000000 : ℝ)) (b := (80212508079 / 50000000000000 : ℝ)) (q := (34922066519 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12838])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12838])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12838]

theorem cert12838_44 : CellCertificate 12838 (220718766457979 / 2500000000000000 : ℝ) (1636107997177879 / 1000000000000000000 : ℝ) (330401153417431 / 10000000000000000 : ℝ)
    (cell12838 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · have h := gap_lower (n := 12838) (a := (82560024730907 / 100000000000000 : ℝ)) (b := (80212508079 / 50000000000000 : ℝ)) (q := (13968851681 / 625000000000 : ℝ))
      (E := (cell12838 ⟨44, by decide⟩).energy) (xi := (330401153417431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12838 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12838]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12838])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12838) (a := (82560024730907 / 100000000000000 : ℝ)) (b := (80212508079 / 50000000000000 : ℝ)) (q := (13968851681 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12838])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12838])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12838]

theorem cert12838_45 : CellCertificate 12838 (220718766457979 / 2500000000000000 : ℝ) (1636107997177879 / 1000000000000000000 : ℝ) (330401153417431 / 10000000000000000 : ℝ)
    (cell12838 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · have h := gap_lower (n := 12838) (a := (515788474329 / 625000000000 : ℝ)) (b := (80212508079 / 50000000000000 : ℝ)) (q := (2235020265461 / 100000000000000 : ℝ))
      (E := (cell12838 ⟨45, by decide⟩).energy) (xi := (330401153417431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12838 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12838]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12838])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12838) (a := (515788474329 / 625000000000 : ℝ)) (b := (80212508079 / 50000000000000 : ℝ)) (q := (2235020265461 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12838])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12838])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12838]

theorem cert12838_46 : CellCertificate 12838 (220718766457979 / 2500000000000000 : ℝ) (1636107997177879 / 1000000000000000000 : ℝ) (330401153417431 / 10000000000000000 : ℝ)
    (cell12838 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · have h := gap_lower (n := 12838) (a := (41246155246251 / 50000000000000 : ℝ)) (b := (80212508079 / 50000000000000 : ℝ)) (q := (223502430393 / 10000000000000 : ℝ))
      (E := (cell12838 ⟨46, by decide⟩).energy) (xi := (330401153417431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12838 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12838]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12838])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12838) (a := (41246155246251 / 50000000000000 : ℝ)) (b := (80212508079 / 50000000000000 : ℝ)) (q := (223502430393 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12838])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12838])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12838]

theorem cert12838_47 : CellCertificate 12838 (220718766457979 / 2500000000000000 : ℝ) (1636107997177879 / 1000000000000000000 : ℝ) (330401153417431 / 10000000000000000 : ℝ)
    (cell12838 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · have h := gap_lower (n := 12838) (a := (82458488501497 / 100000000000000 : ℝ)) (b := (80212508079 / 50000000000000 : ℝ)) (q := (447005664721 / 20000000000000 : ℝ))
      (E := (cell12838 ⟨47, by decide⟩).energy) (xi := (330401153417431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12838 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12838]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12838])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12838) (a := (82458488501497 / 100000000000000 : ℝ)) (b := (80212508079 / 50000000000000 : ℝ)) (q := (447005664721 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12838])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12838])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12838]

theorem cert12838_48 : CellCertificate 12838 (220718766457979 / 2500000000000000 : ℝ) (1636107997177879 / 1000000000000000000 : ℝ) (330401153417431 / 10000000000000000 : ℝ)
    (cell12838 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · have h := gap_lower (n := 12838) (a := (82424689890771 / 100000000000000 : ℝ)) (b := (80212508079 / 50000000000000 : ℝ)) (q := (223503232237 / 10000000000000 : ℝ))
      (E := (cell12838 ⟨48, by decide⟩).energy) (xi := (330401153417431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12838 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12838]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12838])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12838) (a := (82424689890771 / 100000000000000 : ℝ)) (b := (80212508079 / 50000000000000 : ℝ)) (q := (223503232237 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12838])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12838])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12838]

theorem cert12838_49 : CellCertificate 12838 (220718766457979 / 2500000000000000 : ℝ) (1636107997177879 / 1000000000000000000 : ℝ) (330401153417431 / 10000000000000000 : ℝ)
    (cell12838 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · have h := gap_lower (n := 12838) (a := (4119545731581 / 5000000000000 : ℝ)) (b := (80212508079 / 50000000000000 : ℝ)) (q := (2235036297889 / 100000000000000 : ℝ))
      (E := (cell12838 ⟨49, by decide⟩).energy) (xi := (330401153417431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12838 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12838]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12838])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12838) (a := (4119545731581 / 5000000000000 : ℝ)) (b := (80212508079 / 50000000000000 : ℝ)) (q := (2235036297889 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12838])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12838])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12838]

theorem cert12838_50 : CellCertificate 12838 (220718766457979 / 2500000000000000 : ℝ) (1636107997177879 / 1000000000000000000 : ℝ) (330401153417431 / 10000000000000000 : ℝ)
    (cell12838 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · have h := gap_lower (n := 12838) (a := (2058929067387 / 2500000000000 : ℝ)) (b := (80212508079 / 50000000000000 : ℝ)) (q := (558760076653 / 25000000000000 : ℝ))
      (E := (cell12838 ⟨50, by decide⟩).energy) (xi := (330401153417431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12838 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12838]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12838])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12838) (a := (2058929067387 / 2500000000000 : ℝ)) (b := (80212508079 / 50000000000000 : ℝ)) (q := (558760076653 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12838])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12838])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12838]

theorem cert12838_51 : CellCertificate 12838 (220718766457979 / 2500000000000000 : ℝ) (1636107997177879 / 1000000000000000000 : ℝ) (330401153417431 / 10000000000000000 : ℝ)
    (cell12838 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · have h := gap_lower (n := 12838) (a := (8232343405393 / 10000000000000 : ℝ)) (b := (80212508079 / 50000000000000 : ℝ)) (q := (447008869171 / 20000000000000 : ℝ))
      (E := (cell12838 ⟨51, by decide⟩).energy) (xi := (330401153417431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12838 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12838]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12838])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12838) (a := (8232343405393 / 10000000000000 : ℝ)) (b := (80212508079 / 50000000000000 : ℝ)) (q := (447008869171 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12838])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12838])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12838]

theorem cert12838_52 : CellCertificate 12838 (220718766457979 / 2500000000000000 : ℝ) (1636107997177879 / 1000000000000000000 : ℝ) (330401153417431 / 10000000000000000 : ℝ)
    (cell12838 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · have h := gap_lower (n := 12838) (a := (41144864339347 / 50000000000000 : ℝ)) (b := (80212508079 / 50000000000000 : ℝ)) (q := (89401934147 / 4000000000000 : ℝ))
      (E := (cell12838 ⟨52, by decide⟩).energy) (xi := (330401153417431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12838 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12838]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12838])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12838) (a := (41144864339347 / 50000000000000 : ℝ)) (b := (80212508079 / 50000000000000 : ℝ)) (q := (89401934147 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12838])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12838])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12838]

theorem cert12838_53 : CellCertificate 12838 (220718766457979 / 2500000000000000 : ℝ) (1636107997177879 / 1000000000000000000 : ℝ) (330401153417431 / 10000000000000000 : ℝ)
    (cell12838 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · have h := gap_lower (n := 12838) (a := (16451209308327 / 20000000000000 : ℝ)) (b := (80212508079 / 50000000000000 : ℝ)) (q := (447010465379 / 20000000000000 : ℝ))
      (E := (cell12838 ⟨53, by decide⟩).energy) (xi := (330401153417431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12838 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12838]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12838])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12838) (a := (16451209308327 / 20000000000000 : ℝ)) (b := (80212508079 / 50000000000000 : ℝ)) (q := (447010465379 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12838])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12838])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12838]

theorem cert12838_54 : CellCertificate 12838 (220718766457979 / 2500000000000000 : ℝ) (1636107997177879 / 1000000000000000000 : ℝ) (330401153417431 / 10000000000000000 : ℝ)
    (cell12838 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · have h := gap_lower (n := 12838) (a := (20555596903689 / 25000000000000 : ℝ)) (b := (80212508079 / 50000000000000 : ℝ)) (q := (1117528190153 / 50000000000000 : ℝ))
      (E := (cell12838 ⟨54, by decide⟩).energy) (xi := (330401153417431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12838 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12838]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12838])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12838) (a := (20555596903689 / 25000000000000 : ℝ)) (b := (80212508079 / 50000000000000 : ℝ)) (q := (1117528190153 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12838])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12838])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12838]

theorem cert12838_55 : CellCertificate 12838 (220718766457979 / 2500000000000000 : ℝ) (1636107997177879 / 1000000000000000000 : ℝ) (330401153417431 / 10000000000000000 : ℝ)
    (cell12838 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · have h := gap_lower (n := 12838) (a := (41094375935101 / 50000000000000 : ℝ)) (b := (80212508079 / 50000000000000 : ℝ)) (q := (279382541639 / 12500000000000 : ℝ))
      (E := (cell12838 ⟨55, by decide⟩).energy) (xi := (330401153417431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12838 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12838]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12838])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12838) (a := (41094375935101 / 50000000000000 : ℝ)) (b := (80212508079 / 50000000000000 : ℝ)) (q := (279382541639 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12838])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12838])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12838]

theorem cert12838_56 : CellCertificate 12838 (220718766457979 / 2500000000000000 : ℝ) (1636107997177879 / 1000000000000000000 : ℝ) (330401153417431 / 10000000000000000 : ℝ)
    (cell12838 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · have h := gap_lower (n := 12838) (a := (16431027856051 / 20000000000000 : ℝ)) (b := (80212508079 / 50000000000000 : ℝ)) (q := (34922880607 / 1562500000000 : ℝ))
      (E := (cell12838 ⟨56, by decide⟩).energy) (xi := (330401153417431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12838 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12838]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12838])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12838) (a := (16431027856051 / 20000000000000 : ℝ)) (b := (80212508079 / 50000000000000 : ℝ)) (q := (34922880607 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12838])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12838])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12838]

theorem cert12838_57 : CellCertificate 12838 (220718766457979 / 2500000000000000 : ℝ) (1636107997177879 / 1000000000000000000 : ℝ) (330401153417431 / 10000000000000000 : ℝ)
    (cell12838 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · have h := gap_lower (n := 12838) (a := (10265193727167 / 12500000000000 : ℝ)) (b := (80212508079 / 50000000000000 : ℝ)) (q := (558767098621 / 25000000000000 : ℝ))
      (E := (cell12838 ⟨57, by decide⟩).energy) (xi := (330401153417431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12838 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12838]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12838])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12838) (a := (10265193727167 / 12500000000000 : ℝ)) (b := (80212508079 / 50000000000000 : ℝ)) (q := (558767098621 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12838])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12838])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12838]

theorem cert12838_58 : CellCertificate 12838 (220718766457979 / 2500000000000000 : ℝ) (1636107997177879 / 1000000000000000000 : ℝ) (330401153417431 / 10000000000000000 : ℝ)
    (cell12838 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · have h := gap_lower (n := 12838) (a := (82087983454003 / 100000000000000 : ℝ)) (b := (80212508079 / 50000000000000 : ℝ)) (q := (139692023543 / 6250000000000 : ℝ))
      (E := (cell12838 ⟨58, by decide⟩).energy) (xi := (330401153417431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12838 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12838]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12838])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12838) (a := (82087983454003 / 100000000000000 : ℝ)) (b := (80212508079 / 50000000000000 : ℝ)) (q := (139692023543 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12838])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12838])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12838]

theorem cert12838_59 : CellCertificate 12838 (220718766457979 / 2500000000000000 : ℝ) (1636107997177879 / 1000000000000000000 : ℝ) (330401153417431 / 10000000000000000 : ℝ)
    (cell12838 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · have h := gap_lower (n := 12838) (a := (1641088803259 / 2000000000000 : ℝ)) (b := (80212508079 / 50000000000000 : ℝ)) (q := (44701528389 / 2000000000000 : ℝ))
      (E := (cell12838 ⟨59, by decide⟩).energy) (xi := (330401153417431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12838 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12838]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12838])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12838) (a := (1641088803259 / 2000000000000 : ℝ)) (b := (80212508079 / 50000000000000 : ℝ)) (q := (44701528389 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12838])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12838])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12838]

theorem cert12839_40 : CellCertificate 12839 (882847704658403 / 10000000000000000 : ℝ) (408995130766699 / 250000000000000000 : ℝ) (330374805632203 / 10000000000000000 : ℝ)
    (cell12839 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · have h := gap_lower (n := 12839) (a := (82695732498363 / 100000000000000 : ℝ)) (b := (80206186029 / 50000000000000 : ℝ)) (q := (2234881836277 / 100000000000000 : ℝ))
      (E := (cell12839 ⟨40, by decide⟩).energy) (xi := (330374805632203 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12839 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12839]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12839])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12839) (a := (82695732498363 / 100000000000000 : ℝ)) (b := (80206186029 / 50000000000000 : ℝ)) (q := (2234881836277 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12839])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12839])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12839]

theorem cert12839_41 : CellCertificate 12839 (882847704658403 / 10000000000000000 : ℝ) (408995130766699 / 250000000000000000 : ℝ) (330374805632203 / 10000000000000000 : ℝ)
    (cell12839 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · have h := gap_lower (n := 12839) (a := (41330884956169 / 50000000000000 : ℝ)) (b := (80206186029 / 50000000000000 : ℝ)) (q := (558721457181 / 25000000000000 : ℝ))
      (E := (cell12839 ⟨41, by decide⟩).energy) (xi := (330374805632203 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12839 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12839]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12839])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12839) (a := (41330884956169 / 50000000000000 : ℝ)) (b := (80206186029 / 50000000000000 : ℝ)) (q := (558721457181 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12839])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12839])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12839]

theorem cert12839_42 : CellCertificate 12839 (882847704658403 / 10000000000000000 : ℝ) (408995130766699 / 250000000000000000 : ℝ) (330374805632203 / 10000000000000000 : ℝ)
    (cell12839 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · have h := gap_lower (n := 12839) (a := (82627830881491 / 100000000000000 : ℝ)) (b := (80206186029 / 50000000000000 : ℝ)) (q := (558722467287 / 25000000000000 : ℝ))
      (E := (cell12839 ⟨42, by decide⟩).energy) (xi := (330374805632203 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12839 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12839]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12839])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12839) (a := (82627830881491 / 100000000000000 : ℝ)) (b := (80206186029 / 50000000000000 : ℝ)) (q := (558722467287 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12839])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12839])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12839]

theorem cert12839_43 : CellCertificate 12839 (882847704658403 / 10000000000000000 : ℝ) (408995130766699 / 250000000000000000 : ℝ) (330374805632203 / 10000000000000000 : ℝ)
    (cell12839 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · have h := gap_lower (n := 12839) (a := (16518783075247 / 20000000000000 : ℝ)) (b := (80206186029 / 50000000000000 : ℝ)) (q := (2234893838917 / 100000000000000 : ℝ))
      (E := (cell12839 ⟨43, by decide⟩).energy) (xi := (330374805632203 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12839 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12839]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12839])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12839) (a := (16518783075247 / 20000000000000 : ℝ)) (b := (80206186029 / 50000000000000 : ℝ)) (q := (2234893838917 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12839])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12839])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12839]

theorem cert12839_44 : CellCertificate 12839 (882847704658403 / 10000000000000000 : ℝ) (408995130766699 / 250000000000000000 : ℝ) (330374805632203 / 10000000000000000 : ℝ)
    (cell12839 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · have h := gap_lower (n := 12839) (a := (82560023367133 / 100000000000000 : ℝ)) (b := (80206186029 / 50000000000000 : ℝ)) (q := (2234897854409 / 100000000000000 : ℝ))
      (E := (cell12839 ⟨44, by decide⟩).energy) (xi := (330374805632203 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12839 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12839]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12839])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12839) (a := (82560023367133 / 100000000000000 : ℝ)) (b := (80206186029 / 50000000000000 : ℝ)) (q := (2234897854409 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12839])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12839])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12839]

theorem cert12839_45 : CellCertificate 12839 (882847704658403 / 10000000000000000 : ℝ) (408995130766699 / 250000000000000000 : ℝ) (330374805632203 / 10000000000000000 : ℝ)
    (cell12839 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · have h := gap_lower (n := 12839) (a := (16505230964979 / 20000000000000 : ℝ)) (b := (80206186029 / 50000000000000 : ℝ)) (q := (1117450927671 / 50000000000000 : ℝ))
      (E := (cell12839 ⟨45, by decide⟩).energy) (xi := (330374805632203 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12839 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12839]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12839])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12839) (a := (16505230964979 / 20000000000000 : ℝ)) (b := (80206186029 / 50000000000000 : ℝ)) (q := (1117450927671 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12839])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12839])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12839]

theorem cert12839_46 : CellCertificate 12839 (882847704658403 / 10000000000000000 : ℝ) (408995130766699 / 250000000000000000 : ℝ) (330374805632203 / 10000000000000000 : ℝ)
    (cell12839 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · have h := gap_lower (n := 12839) (a := (41246154860189 / 50000000000000 : ℝ)) (b := (80206186029 / 50000000000000 : ℝ)) (q := (1117452949463 / 50000000000000 : ℝ))
      (E := (cell12839 ⟨46, by decide⟩).energy) (xi := (330374805632203 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12839 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12839]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12839])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12839) (a := (41246154860189 / 50000000000000 : ℝ)) (b := (80206186029 / 50000000000000 : ℝ)) (q := (1117452949463 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12839])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12839])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12839]

theorem cert12839_47 : CellCertificate 12839 (882847704658403 / 10000000000000000 : ℝ) (408995130766699 / 250000000000000000 : ℝ) (330374805632203 / 10000000000000000 : ℝ)
    (cell12839 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · have h := gap_lower (n := 12839) (a := (82458488024587 / 100000000000000 : ℝ)) (b := (80206186029 / 50000000000000 : ℝ)) (q := (89396394619 / 4000000000000 : ℝ))
      (E := (cell12839 ⟨47, by decide⟩).energy) (xi := (330374805632203 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12839 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12839]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12839])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12839) (a := (82458488024587 / 100000000000000 : ℝ)) (b := (80206186029 / 50000000000000 : ℝ)) (q := (89396394619 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12839])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12839])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12839]

theorem cert12839_48 : CellCertificate 12839 (882847704658403 / 10000000000000000 : ℝ) (408995130766699 / 250000000000000000 : ℝ) (330374805632203 / 10000000000000000 : ℝ)
    (cell12839 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · have h := gap_lower (n := 12839) (a := (8242468970867 / 10000000000000 : ℝ)) (b := (80206186029 / 50000000000000 : ℝ)) (q := (446982785929 / 20000000000000 : ℝ))
      (E := (cell12839 ⟨48, by decide⟩).energy) (xi := (330374805632203 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12839 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12839]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12839])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12839) (a := (8242468970867 / 10000000000000 : ℝ)) (b := (80206186029 / 50000000000000 : ℝ)) (q := (446982785929 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12839])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12839])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12839]

theorem cert12839_49 : CellCertificate 12839 (882847704658403 / 10000000000000000 : ℝ) (408995130766699 / 250000000000000000 : ℝ) (330374805632203 / 10000000000000000 : ℝ)
    (cell12839 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · have h := gap_lower (n := 12839) (a := (82390914743923 / 100000000000000 : ℝ)) (b := (80206186029 / 50000000000000 : ℝ)) (q := (89396716493 / 4000000000000 : ℝ))
      (E := (cell12839 ⟨49, by decide⟩).energy) (xi := (330374805632203 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12839 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12839]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12839])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12839) (a := (82390914743923 / 100000000000000 : ℝ)) (b := (80206186029 / 50000000000000 : ℝ)) (q := (89396716493 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12839])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12839])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12839]

theorem cert12839_50 : CellCertificate 12839 (882847704658403 / 10000000000000000 : ℝ) (408995130766699 / 250000000000000000 : ℝ) (330374805632203 / 10000000000000000 : ℝ)
    (cell12839 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · have h := gap_lower (n := 12839) (a := (82357163101781 / 100000000000000 : ℝ)) (b := (80206186029 / 50000000000000 : ℝ)) (q := (558730482223 / 25000000000000 : ℝ))
      (E := (cell12839 ⟨50, by decide⟩).energy) (xi := (330374805632203 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12839 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12839]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12839])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12839) (a := (82357163101781 / 100000000000000 : ℝ)) (b := (80206186029 / 50000000000000 : ℝ)) (q := (558730482223 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12839])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12839])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12839]

theorem cert12839_51 : CellCertificate 12839 (882847704658403 / 10000000000000000 : ℝ) (408995130766699 / 250000000000000000 : ℝ) (330374805632203 / 10000000000000000 : ℝ)
    (cell12839 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · have h := gap_lower (n := 12839) (a := (82323434753827 / 100000000000000 : ℝ)) (b := (80206186029 / 50000000000000 : ℝ)) (q := (1117462958819 / 50000000000000 : ℝ))
      (E := (cell12839 ⟨51, by decide⟩).energy) (xi := (330374805632203 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12839 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12839]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12839])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12839) (a := (82323434753827 / 100000000000000 : ℝ)) (b := (80206186029 / 50000000000000 : ℝ)) (q := (1117462958819 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12839])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12839])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12839]

theorem cert12839_52 : CellCertificate 12839 (882847704658403 / 10000000000000000 : ℝ) (408995130766699 / 250000000000000000 : ℝ) (330374805632203 / 10000000000000000 : ℝ)
    (cell12839 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · have h := gap_lower (n := 12839) (a := (82289729671783 / 100000000000000 : ℝ)) (b := (80206186029 / 50000000000000 : ℝ)) (q := (2234929934637 / 100000000000000 : ℝ))
      (E := (cell12839 ⟨52, by decide⟩).energy) (xi := (330374805632203 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12839 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12839]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12839])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12839) (a := (82289729671783 / 100000000000000 : ℝ)) (b := (80206186029 / 50000000000000 : ℝ)) (q := (2234929934637 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12839])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12839])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12839]

theorem cert12839_53 : CellCertificate 12839 (882847704658403 / 10000000000000000 : ℝ) (408995130766699 / 250000000000000000 : ℝ) (330374805632203 / 10000000000000000 : ℝ)
    (cell12839 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · have h := gap_lower (n := 12839) (a := (41128023913757 / 50000000000000 : ℝ)) (b := (80206186029 / 50000000000000 : ℝ)) (q := (2234933917713 / 100000000000000 : ℝ))
      (E := (cell12839 ⟨53, by decide⟩).energy) (xi := (330374805632203 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12839 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12839]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12839])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12839) (a := (41128023913757 / 50000000000000 : ℝ)) (b := (80206186029 / 50000000000000 : ℝ)) (q := (2234933917713 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12839])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12839])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12839]

theorem cert12839_54 : CellCertificate 12839 (882847704658403 / 10000000000000000 : ℝ) (408995130766699 / 250000000000000000 : ℝ) (330374805632203 / 10000000000000000 : ℝ)
    (cell12839 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · have h := gap_lower (n := 12839) (a := (1284724831141 / 1562500000000 : ℝ)) (b := (80206186029 / 50000000000000 : ℝ)) (q := (2234937922569 / 100000000000000 : ℝ))
      (E := (cell12839 ⟨54, by decide⟩).energy) (xi := (330374805632203 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12839 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12839]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12839])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12839) (a := (1284724831141 / 1562500000000 : ℝ)) (b := (80206186029 / 50000000000000 : ℝ)) (q := (2234937922569 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12839])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12839])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12839]

theorem cert12839_55 : CellCertificate 12839 (882847704658403 / 10000000000000000 : ℝ) (408995130766699 / 250000000000000000 : ℝ) (330374805632203 / 10000000000000000 : ℝ)
    (cell12839 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · have h := gap_lower (n := 12839) (a := (82188753740457 / 100000000000000 : ℝ)) (b := (80206186029 / 50000000000000 : ℝ)) (q := (2234941945677 / 100000000000000 : ℝ))
      (E := (cell12839 ⟨55, by decide⟩).energy) (xi := (330374805632203 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12839 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12839]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12839])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12839) (a := (82188753740457 / 100000000000000 : ℝ)) (b := (80206186029 / 50000000000000 : ℝ)) (q := (2234941945677 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12839])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12839])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12839]

theorem cert12839_56 : CellCertificate 12839 (882847704658403 / 10000000000000000 : ℝ) (408995130766699 / 250000000000000000 : ℝ) (330374805632203 / 10000000000000000 : ℝ)
    (cell12839 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · have h := gap_lower (n := 12839) (a := (82155141442097 / 100000000000000 : ℝ)) (b := (80206186029 / 50000000000000 : ℝ)) (q := (2234945983303 / 100000000000000 : ℝ))
      (E := (cell12839 ⟨56, by decide⟩).energy) (xi := (330374805632203 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12839 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12839]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12839])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12839) (a := (82155141442097 / 100000000000000 : ℝ)) (b := (80206186029 / 50000000000000 : ℝ)) (q := (2234945983303 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12839])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12839])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12839]

theorem cert12839_57 : CellCertificate 12839 (882847704658403 / 10000000000000000 : ℝ) (408995130766699 / 250000000000000000 : ℝ) (330374805632203 / 10000000000000000 : ℝ)
    (cell12839 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · have h := gap_lower (n := 12839) (a := (41060776135183 / 50000000000000 : ℝ)) (b := (80206186029 / 50000000000000 : ℝ)) (q := (279368746543 / 12500000000000 : ℝ))
      (E := (cell12839 ⟨57, by decide⟩).energy) (xi := (330374805632203 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12839 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12839]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12839])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12839) (a := (41060776135183 / 50000000000000 : ℝ)) (b := (80206186029 / 50000000000000 : ℝ)) (q := (279368746543 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12839])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12839])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12839]

theorem cert12839_58 : CellCertificate 12839 (882847704658403 / 10000000000000000 : ℝ) (408995130766699 / 250000000000000000 : ℝ) (330374805632203 / 10000000000000000 : ℝ)
    (cell12839 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · have h := gap_lower (n := 12839) (a := (82087986197821 / 100000000000000 : ℝ)) (b := (80206186029 / 50000000000000 : ℝ)) (q := (446990793553 / 20000000000000 : ℝ))
      (E := (cell12839 ⟨58, by decide⟩).energy) (xi := (330374805632203 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12839 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12839]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12839])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12839) (a := (82087986197821 / 100000000000000 : ℝ)) (b := (80206186029 / 50000000000000 : ℝ)) (q := (446990793553 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12839])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12839])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12839]

theorem cert12839_59 : CellCertificate 12839 (882847704658403 / 10000000000000000 : ℝ) (408995130766699 / 250000000000000000 : ℝ) (330374805632203 / 10000000000000000 : ℝ)
    (cell12839 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · have h := gap_lower (n := 12839) (a := (82054443197159 / 100000000000000 : ℝ)) (b := (80206186029 / 50000000000000 : ℝ)) (q := (2234957965213 / 100000000000000 : ℝ))
      (E := (cell12839 ⟨59, by decide⟩).energy) (xi := (330374805632203 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12839 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12839]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12839])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12839) (a := (82054443197159 / 100000000000000 : ℝ)) (b := (80206186029 / 50000000000000 : ℝ)) (q := (2234957965213 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12839])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12839])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12839]

theorem cert12840_40 : CellCertificate 12840 (27588135861643 / 312500000000000 : ℝ) (1635853068817949 / 1000000000000000000 : ℝ) (165174231047997 / 5000000000000000 : ℝ)
    (cell12840 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · have h := gap_lower (n := 12840) (a := (41347864973613 / 50000000000000 : ℝ)) (b := (160399729963 / 100000000000000 : ℝ)) (q := (1117381733277 / 50000000000000 : ℝ))
      (E := (cell12840 ⟨40, by decide⟩).energy) (xi := (165174231047997 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12840 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12840]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12840])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12840) (a := (41347864973613 / 50000000000000 : ℝ)) (b := (160399729963 / 100000000000000 : ℝ)) (q := (1117381733277 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12840])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12840])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12840]

theorem cert12840_41 : CellCertificate 12840 (27588135861643 / 312500000000000 : ℝ) (1635853068817949 / 1000000000000000000 : ℝ) (165174231047997 / 5000000000000000 : ℝ)
    (cell12840 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · have h := gap_lower (n := 12840) (a := (8266176765883 / 10000000000000 : ℝ)) (b := (160399729963 / 100000000000000 : ℝ)) (q := (2234767460753 / 100000000000000 : ℝ))
      (E := (cell12840 ⟨41, by decide⟩).energy) (xi := (165174231047997 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12840 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12840]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12840])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12840) (a := (8266176765883 / 10000000000000 : ℝ)) (b := (160399729963 / 100000000000000 : ℝ)) (q := (2234767460753 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12840])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12840])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12840]

theorem cert12840_42 : CellCertificate 12840 (27588135861643 / 312500000000000 : ℝ) (1635853068817949 / 1000000000000000000 : ℝ) (165174231047997 / 5000000000000000 : ℝ)
    (cell12840 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · have h := gap_lower (n := 12840) (a := (41313914462601 / 50000000000000 : ℝ)) (b := (160399729963 / 100000000000000 : ℝ)) (q := (446954300723 / 20000000000000 : ℝ))
      (E := (cell12840 ⟨42, by decide⟩).energy) (xi := (165174231047997 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12840 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12840]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12840])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12840) (a := (41313914462601 / 50000000000000 : ℝ)) (b := (160399729963 / 100000000000000 : ℝ)) (q := (446954300723 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12840])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12840])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12840]

theorem cert12840_43 : CellCertificate 12840 (27588135861643 / 312500000000000 : ℝ) (1635853068817949 / 1000000000000000000 : ℝ) (165174231047997 / 5000000000000000 : ℝ)
    (cell12840 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · have h := gap_lower (n := 12840) (a := (20648478429189 / 25000000000000 : ℝ)) (b := (160399729963 / 100000000000000 : ℝ)) (q := (1117387738253 / 50000000000000 : ℝ))
      (E := (cell12840 ⟨43, by decide⟩).energy) (xi := (165174231047997 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12840 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12840]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12840])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12840) (a := (20648478429189 / 25000000000000 : ℝ)) (b := (160399729963 / 100000000000000 : ℝ)) (q := (1117387738253 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12840])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12840])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12840]

theorem cert12840_44 : CellCertificate 12840 (27588135861643 / 312500000000000 : ℝ) (1635853068817949 / 1000000000000000000 : ℝ) (165174231047997 / 5000000000000000 : ℝ)
    (cell12840 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · have h := gap_lower (n := 12840) (a := (16512004400811 / 20000000000000 : ℝ)) (b := (160399729963 / 100000000000000 : ℝ)) (q := (1117389747903 / 50000000000000 : ℝ))
      (E := (cell12840 ⟨44, by decide⟩).energy) (xi := (165174231047997 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12840 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12840]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12840])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12840) (a := (16512004400811 / 20000000000000 : ℝ)) (b := (160399729963 / 100000000000000 : ℝ)) (q := (1117389747903 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12840])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12840])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12840]

theorem cert12840_45 : CellCertificate 12840 (27588135861643 / 312500000000000 : ℝ) (1635853068817949 / 1000000000000000000 : ℝ) (165174231047997 / 5000000000000000 : ℝ)
    (cell12840 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · have h := gap_lower (n := 12840) (a := (8252615375781 / 10000000000000 : ℝ)) (b := (160399729963 / 100000000000000 : ℝ)) (q := (2234783501231 / 100000000000000 : ℝ))
      (E := (cell12840 ⟨45, by decide⟩).energy) (xi := (165174231047997 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12840 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12840]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12840])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12840) (a := (8252615375781 / 10000000000000 : ℝ)) (b := (160399729963 / 100000000000000 : ℝ)) (q := (2234783501231 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12840])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12840])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12840]

theorem cert12840_46 : CellCertificate 12840 (27588135861643 / 312500000000000 : ℝ) (1635853068817949 / 1000000000000000000 : ℝ) (165174231047997 / 5000000000000000 : ℝ)
    (cell12840 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · have h := gap_lower (n := 12840) (a := (41246154474439 / 50000000000000 : ℝ)) (b := (160399729963 / 100000000000000 : ℝ)) (q := (2234787491089 / 100000000000000 : ℝ))
      (E := (cell12840 ⟨46, by decide⟩).energy) (xi := (165174231047997 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12840 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12840]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12840])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12840) (a := (41246154474439 / 50000000000000 : ℝ)) (b := (160399729963 / 100000000000000 : ℝ)) (q := (2234787491089 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12840])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12840])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12840]

theorem cert12840_47 : CellCertificate 12840 (27588135861643 / 312500000000000 : ℝ) (1635853068817949 / 1000000000000000000 : ℝ) (165174231047997 / 5000000000000000 : ℝ)
    (cell12840 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · have h := gap_lower (n := 12840) (a := (41229243774133 / 50000000000000 : ℝ)) (b := (160399729963 / 100000000000000 : ℝ)) (q := (1117395761199 / 50000000000000 : ℝ))
      (E := (cell12840 ⟨47, by decide⟩).energy) (xi := (165174231047997 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12840 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12840]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12840])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12840) (a := (41229243774133 / 50000000000000 : ℝ)) (b := (160399729963 / 100000000000000 : ℝ)) (q := (1117395761199 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12840])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12840])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12840]

theorem cert12840_48 : CellCertificate 12840 (27588135861643 / 312500000000000 : ℝ) (1635853068817949 / 1000000000000000000 : ℝ) (165174231047997 / 5000000000000000 : ℝ)
    (cell12840 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · have h := gap_lower (n := 12840) (a := (82424689527123 / 100000000000000 : ℝ)) (b := (160399729963 / 100000000000000 : ℝ)) (q := (1117397767079 / 50000000000000 : ℝ))
      (E := (cell12840 ⟨48, by decide⟩).energy) (xi := (165174231047997 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12840 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12840]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12840])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12840) (a := (82424689527123 / 100000000000000 : ℝ)) (b := (160399729963 / 100000000000000 : ℝ)) (q := (1117397767079 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12840])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12840])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12840]

theorem cert12840_49 : CellCertificate 12840 (27588135861643 / 312500000000000 : ℝ) (1635853068817949 / 1000000000000000000 : ℝ) (165174231047997 / 5000000000000000 : ℝ)
    (cell12840 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · have h := gap_lower (n := 12840) (a := (82390914856743 / 100000000000000 : ℝ)) (b := (160399729963 / 100000000000000 : ℝ)) (q := (2234799524037 / 100000000000000 : ℝ))
      (E := (cell12840 ⟨49, by decide⟩).energy) (xi := (165174231047997 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12840 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12840]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12840])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12840) (a := (82390914856743 / 100000000000000 : ℝ)) (b := (160399729963 / 100000000000000 : ℝ)) (q := (2234799524037 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12840])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12840])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12840]

theorem cert12840_50 : CellCertificate 12840 (27588135861643 / 312500000000000 : ℝ) (1635853068817949 / 1000000000000000000 : ℝ) (165174231047997 / 5000000000000000 : ℝ)
    (cell12840 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · have h := gap_lower (n := 12840) (a := (41178581754283 / 50000000000000 : ℝ)) (b := (160399729963 / 100000000000000 : ℝ)) (q := (2234803548481 / 100000000000000 : ℝ))
      (E := (cell12840 ⟨50, by decide⟩).energy) (xi := (165174231047997 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12840 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12840]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12840])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12840) (a := (41178581754283 / 50000000000000 : ℝ)) (b := (160399729963 / 100000000000000 : ℝ)) (q := (2234803548481 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12840])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12840])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12840]

theorem cert12840_51 : CellCertificate 12840 (27588135861643 / 312500000000000 : ℝ) (1635853068817949 / 1000000000000000000 : ℝ) (165174231047997 / 5000000000000000 : ℝ)
    (cell12840 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · have h := gap_lower (n := 12840) (a := (20580858863543 / 25000000000000 : ℝ)) (b := (160399729963 / 100000000000000 : ℝ)) (q := (1117403772893 / 50000000000000 : ℝ))
      (E := (cell12840 ⟨51, by decide⟩).energy) (xi := (165174231047997 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12840 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12840]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12840])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12840) (a := (20580858863543 / 25000000000000 : ℝ)) (b := (160399729963 / 100000000000000 : ℝ)) (q := (1117403772893 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12840])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12840])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12840]

theorem cert12840_52 : CellCertificate 12840 (27588135861643 / 312500000000000 : ℝ) (1635853068817949 / 1000000000000000000 : ℝ) (165174231047997 / 5000000000000000 : ℝ)
    (cell12840 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · have h := gap_lower (n := 12840) (a := (16457946133057 / 20000000000000 : ℝ)) (b := (160399729963 / 100000000000000 : ℝ)) (q := (1117405786011 / 50000000000000 : ℝ))
      (E := (cell12840 ⟨52, by decide⟩).energy) (xi := (165174231047997 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12840 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12840]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12840])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12840) (a := (16457946133057 / 20000000000000 : ℝ)) (b := (160399729963 / 100000000000000 : ℝ)) (q := (1117405786011 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12840])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12840])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12840]

theorem cert12840_53 : CellCertificate 12840 (27588135861643 / 312500000000000 : ℝ) (1635853068817949 / 1000000000000000000 : ℝ) (165174231047997 / 5000000000000000 : ℝ)
    (cell12840 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · have h := gap_lower (n := 12840) (a := (82256049113771 / 100000000000000 : ℝ)) (b := (160399729963 / 100000000000000 : ℝ)) (q := (446963113003 / 20000000000000 : ℝ))
      (E := (cell12840 ⟨53, by decide⟩).energy) (xi := (165174231047997 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12840 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12840]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12840])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12840) (a := (82256049113771 / 100000000000000 : ℝ)) (b := (160399729963 / 100000000000000 : ℝ)) (q := (446963113003 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12840])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12840])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12840]

theorem cert12840_54 : CellCertificate 12840 (27588135861643 / 312500000000000 : ℝ) (1635853068817949 / 1000000000000000000 : ℝ) (165174231047997 / 5000000000000000 : ℝ)
    (cell12840 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · have h := gap_lower (n := 12840) (a := (41111195385817 / 50000000000000 : ℝ)) (b := (160399729963 / 100000000000000 : ℝ)) (q := (446963916093 / 20000000000000 : ℝ))
      (E := (cell12840 ⟨54, by decide⟩).energy) (xi := (165174231047997 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12840 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12840]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12840])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12840) (a := (41111195385817 / 50000000000000 : ℝ)) (b := (160399729963 / 100000000000000 : ℝ)) (q := (446963916093 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12840])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12840])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12840]

theorem cert12840_55 : CellCertificate 12840 (27588135861643 / 312500000000000 : ℝ) (1635853068817949 / 1000000000000000000 : ℝ) (165174231047997 / 5000000000000000 : ℝ)
    (cell12840 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · have h := gap_lower (n := 12840) (a := (82188755611019 / 100000000000000 : ℝ)) (b := (160399729963 / 100000000000000 : ℝ)) (q := (2234823555733 / 100000000000000 : ℝ))
      (E := (cell12840 ⟨55, by decide⟩).energy) (xi := (165174231047997 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12840 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12840]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12840])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12840) (a := (82188755611019 / 100000000000000 : ℝ)) (b := (160399729963 / 100000000000000 : ℝ)) (q := (2234823555733 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12840])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12840])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12840]

theorem cert12840_56 : CellCertificate 12840 (27588135861643 / 312500000000000 : ℝ) (1635853068817949 / 1000000000000000000 : ℝ) (165174231047997 / 5000000000000000 : ℝ)
    (cell12840 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · have h := gap_lower (n := 12840) (a := (20538785901053 / 25000000000000 : ℝ)) (b := (160399729963 / 100000000000000 : ℝ)) (q := (2234827605283 / 100000000000000 : ℝ))
      (E := (cell12840 ⟨56, by decide⟩).energy) (xi := (165174231047997 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12840 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12840]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12840])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12840) (a := (20538785901053 / 25000000000000 : ℝ)) (b := (160399729963 / 100000000000000 : ℝ)) (q := (2234827605283 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12840])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12840])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12840]

theorem cert12840_57 : CellCertificate 12840 (27588135861643 / 312500000000000 : ℝ) (1635853068817949 / 1000000000000000000 : ℝ) (165174231047997 / 5000000000000000 : ℝ)
    (cell12840 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · have h := gap_lower (n := 12840) (a := (82121554723633 / 100000000000000 : ℝ)) (b := (160399729963 / 100000000000000 : ℝ)) (q := (89393264277 / 4000000000000 : ℝ))
      (E := (cell12840 ⟨57, by decide⟩).energy) (xi := (165174231047997 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12840 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12840]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12840])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12840) (a := (82121554723633 / 100000000000000 : ℝ)) (b := (160399729963 / 100000000000000 : ℝ)) (q := (89393264277 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12840])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12840])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12840]

theorem cert12840_58 : CellCertificate 12840 (27588135861643 / 312500000000000 : ℝ) (1635853068817949 / 1000000000000000000 : ℝ) (165174231047997 / 5000000000000000 : ℝ)
    (cell12840 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · have h := gap_lower (n := 12840) (a := (41043994470921 / 50000000000000 : ℝ)) (b := (160399729963 / 100000000000000 : ℝ)) (q := (2234835615623 / 100000000000000 : ℝ))
      (E := (cell12840 ⟨58, by decide⟩).energy) (xi := (165174231047997 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12840 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12840]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12840])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12840) (a := (41043994470921 / 50000000000000 : ℝ)) (b := (160399729963 / 100000000000000 : ℝ)) (q := (2234835615623 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12840])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12840])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12840]

theorem cert12840_59 : CellCertificate 12840 (27588135861643 / 312500000000000 : ℝ) (1635853068817949 / 1000000000000000000 : ℝ) (165174231047997 / 5000000000000000 : ℝ)
    (cell12840 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · have h := gap_lower (n := 12840) (a := (5128402889471 / 6250000000000 : ℝ)) (b := (160399729963 / 100000000000000 : ℝ)) (q := (2234839627021 / 100000000000000 : ℝ))
      (E := (cell12840 ⟨59, by decide⟩).energy) (xi := (165174231047997 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12840 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12840]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12840])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12840) (a := (5128402889471 / 6250000000000 : ℝ)) (b := (160399729963 / 100000000000000 : ℝ)) (q := (2234839627021 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12840])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12840])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12840]

theorem cert12841_40 : CellCertificate 12841 (220698248643369 / 2500000000000000 : ℝ) (1635725634426697 / 1000000000000000000 : ℝ) (330322122807699 / 10000000000000000 : ℝ)
    (cell12841 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · have h := gap_lower (n := 12841) (a := (82695727396927 / 100000000000000 : ℝ)) (b := (160387089871 / 100000000000000 : ℝ)) (q := (2234645093781 / 100000000000000 : ℝ))
      (E := (cell12841 ⟨40, by decide⟩).energy) (xi := (330322122807699 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12841 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12841]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12841])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12841) (a := (82695727396927 / 100000000000000 : ℝ)) (b := (160387089871 / 100000000000000 : ℝ)) (q := (2234645093781 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12841])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12841])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12841]

theorem cert12841_41 : CellCertificate 12841 (220698248643369 / 2500000000000000 : ℝ) (1635725634426697 / 1000000000000000000 : ℝ) (330322122807699 / 10000000000000000 : ℝ)
    (cell12841 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · have h := gap_lower (n := 12841) (a := (20665441351531 / 25000000000000 : ℝ)) (b := (160387089871 / 100000000000000 : ℝ)) (q := (2234649148553 / 100000000000000 : ℝ))
      (E := (cell12841 ⟨41, by decide⟩).energy) (xi := (330322122807699 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12841 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12841]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12841])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12841) (a := (20665441351531 / 25000000000000 : ℝ)) (b := (160387089871 / 100000000000000 : ℝ)) (q := (2234649148553 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12841])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12841])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12841]

theorem cert12841_42 : CellCertificate 12841 (220698248643369 / 2500000000000000 : ℝ) (1635725634426697 / 1000000000000000000 : ℝ) (330322122807699 / 10000000000000000 : ℝ)
    (cell12841 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · have h := gap_lower (n := 12841) (a := (82627826969679 / 100000000000000 : ℝ)) (b := (160387089871 / 100000000000000 : ℝ)) (q := (446930627021 / 20000000000000 : ℝ))
      (E := (cell12841 ⟨42, by decide⟩).energy) (xi := (330322122807699 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12841 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12841]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12841])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12841) (a := (82627826969679 / 100000000000000 : ℝ)) (b := (160387089871 / 100000000000000 : ℝ)) (q := (446930627021 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12841])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12841])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12841]

theorem cert12841_43 : CellCertificate 12841 (220698248643369 / 2500000000000000 : ℝ) (1635725634426697 / 1000000000000000000 : ℝ) (330322122807699 / 10000000000000000 : ℝ)
    (cell12841 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · have h := gap_lower (n := 12841) (a := (82593912058007 / 100000000000000 : ℝ)) (b := (160387089871 / 100000000000000 : ℝ)) (q := (558664277789 / 25000000000000 : ℝ))
      (E := (cell12841 ⟨43, by decide⟩).energy) (xi := (330322122807699 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12841 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12841]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12841])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12841) (a := (82593912058007 / 100000000000000 : ℝ)) (b := (160387089871 / 100000000000000 : ℝ)) (q := (558664277789 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12841])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12841])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12841]

theorem cert12841_44 : CellCertificate 12841 (220698248643369 / 2500000000000000 : ℝ) (1635725634426697 / 1000000000000000000 : ℝ) (330322122807699 / 10000000000000000 : ℝ)
    (cell12841 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · have h := gap_lower (n := 12841) (a := (82560020641671 / 100000000000000 : ℝ)) (b := (160387089871 / 100000000000000 : ℝ)) (q := (22346611343 / 1000000000000 : ℝ))
      (E := (cell12841 ⟨44, by decide⟩).energy) (xi := (330322122807699 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12841 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12841]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12841])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12841) (a := (82560020641671 / 100000000000000 : ℝ)) (b := (160387089871 / 100000000000000 : ℝ)) (q := (22346611343 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12841])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12841])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12841]

theorem cert12841_45 : CellCertificate 12841 (220698248643369 / 2500000000000000 : ℝ) (1635725634426697 / 1000000000000000000 : ℝ) (330322122807699 / 10000000000000000 : ℝ)
    (cell12841 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · have h := gap_lower (n := 12841) (a := (82526152691383 / 100000000000000 : ℝ)) (b := (160387089871 / 100000000000000 : ℝ)) (q := (2234665144253 / 100000000000000 : ℝ))
      (E := (cell12841 ⟨45, by decide⟩).energy) (xi := (330322122807699 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12841 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12841]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12841])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12841) (a := (82526152691383 / 100000000000000 : ℝ)) (b := (160387089871 / 100000000000000 : ℝ)) (q := (2234665144253 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12841])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12841])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12841]

theorem cert12841_46 : CellCertificate 12841 (220698248643369 / 2500000000000000 : ℝ) (1635725634426697 / 1000000000000000000 : ℝ) (330322122807699 / 10000000000000000 : ℝ)
    (cell12841 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · have h := gap_lower (n := 12841) (a := (41246154089001 / 50000000000000 : ℝ)) (b := (160387089871 / 100000000000000 : ℝ)) (q := (1117334569661 / 50000000000000 : ℝ))
      (E := (cell12841 ⟨46, by decide⟩).energy) (xi := (330322122807699 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12841 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12841]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12841])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12841) (a := (41246154089001 / 50000000000000 : ℝ)) (b := (160387089871 / 100000000000000 : ℝ)) (q := (1117334569661 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12841])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12841])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12841]

theorem cert12841_47 : CellCertificate 12841 (220698248643369 / 2500000000000000 : ℝ) (1635725634426697 / 1000000000000000000 : ℝ) (330322122807699 / 10000000000000000 : ℝ)
    (cell12841 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · have h := gap_lower (n := 12841) (a := (41229243536267 / 50000000000000 : ℝ)) (b := (160387089871 / 100000000000000 : ℝ)) (q := (558668294131 / 25000000000000 : ℝ))
      (E := (cell12841 ⟨47, by decide⟩).energy) (xi := (330322122807699 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12841 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12841]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12841])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12841) (a := (41229243536267 / 50000000000000 : ℝ)) (b := (160387089871 / 100000000000000 : ℝ)) (q := (558668294131 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12841])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12841])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12841]

theorem cert12841_48 : CellCertificate 12841 (220698248643369 / 2500000000000000 : ℝ) (1635725634426697 / 1000000000000000000 : ℝ) (330322122807699 / 10000000000000000 : ℝ)
    (cell12841 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · have h := gap_lower (n := 12841) (a := (5151543084133 / 6250000000000 : ℝ)) (b := (160387089871 / 100000000000000 : ℝ)) (q := (1117338597431 / 50000000000000 : ℝ))
      (E := (cell12841 ⟨48, by decide⟩).energy) (xi := (330322122807699 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12841 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12841]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12841])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12841) (a := (5151543084133 / 6250000000000 : ℝ)) (b := (160387089871 / 100000000000000 : ℝ)) (q := (1117338597431 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12841])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12841])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12841]

theorem cert12841_49 : CellCertificate 12841 (220698248643369 / 2500000000000000 : ℝ) (1635725634426697 / 1000000000000000000 : ℝ) (330322122807699 / 10000000000000000 : ℝ)
    (cell12841 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · have h := gap_lower (n := 12841) (a := (41195457485041 / 50000000000000 : ℝ)) (b := (160387089871 / 100000000000000 : ℝ)) (q := (2234681191997 / 100000000000000 : ℝ))
      (E := (cell12841 ⟨49, by decide⟩).energy) (xi := (330322122807699 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12841 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12841]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12841])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12841) (a := (41195457485041 / 50000000000000 : ℝ)) (b := (160387089871 / 100000000000000 : ℝ)) (q := (2234681191997 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12841])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12841])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12841]

theorem cert12841_50 : CellCertificate 12841 (220698248643369 / 2500000000000000 : ℝ) (1635725634426697 / 1000000000000000000 : ℝ) (330322122807699 / 10000000000000000 : ℝ)
    (cell12841 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · have h := gap_lower (n := 12841) (a := (82357163915833 / 100000000000000 : ℝ)) (b := (160387089871 / 100000000000000 : ℝ)) (q := (279335645673 / 12500000000000 : ℝ))
      (E := (cell12841 ⟨50, by decide⟩).energy) (xi := (330322122807699 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12841 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12841]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12841])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12841) (a := (82357163915833 / 100000000000000 : ℝ)) (b := (160387089871 / 100000000000000 : ℝ)) (q := (279335645673 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12841])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12841])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12841]

theorem cert12841_51 : CellCertificate 12841 (220698248643369 / 2500000000000000 : ℝ) (1635725634426697 / 1000000000000000000 : ℝ) (330322122807699 / 10000000000000000 : ℝ)
    (cell12841 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · have h := gap_lower (n := 12841) (a := (20580859038741 / 25000000000000 : ℝ)) (b := (160387089871 / 100000000000000 : ℝ)) (q := (2234689171283 / 100000000000000 : ℝ))
      (E := (cell12841 ⟨51, by decide⟩).energy) (xi := (330322122807699 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12841 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12841]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12841])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12841) (a := (20580859038741 / 25000000000000 : ℝ)) (b := (160387089871 / 100000000000000 : ℝ)) (q := (2234689171283 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12841])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12841])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12841]

theorem cert12841_52 : CellCertificate 12841 (220698248643369 / 2500000000000000 : ℝ) (1635725634426697 / 1000000000000000000 : ℝ) (330322122807699 / 10000000000000000 : ℝ)
    (cell12841 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · have h := gap_lower (n := 12841) (a := (82289731659199 / 100000000000000 : ℝ)) (b := (160387089871 / 100000000000000 : ℝ)) (q := (2234693206793 / 100000000000000 : ℝ))
      (E := (cell12841 ⟨52, by decide⟩).energy) (xi := (330322122807699 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12841 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12841]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12841])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12841) (a := (82289731659199 / 100000000000000 : ℝ)) (b := (160387089871 / 100000000000000 : ℝ)) (q := (2234693206793 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12841])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12841])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12841]

theorem cert12841_53 : CellCertificate 12841 (220698248643369 / 2500000000000000 : ℝ) (1635725634426697 / 1000000000000000000 : ℝ) (330322122807699 / 10000000000000000 : ℝ)
    (cell12841 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · have h := gap_lower (n := 12841) (a := (16451210080081 / 20000000000000 : ℝ)) (b := (160387089871 / 100000000000000 : ℝ)) (q := (1117348604869 / 50000000000000 : ℝ))
      (E := (cell12841 ⟨53, by decide⟩).energy) (xi := (330322122807699 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12841 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12841]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12841])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12841) (a := (16451210080081 / 20000000000000 : ℝ)) (b := (160387089871 / 100000000000000 : ℝ)) (q := (1117348604869 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12841])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12841])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12841]

theorem cert12841_54 : CellCertificate 12841 (220698248643369 / 2500000000000000 : ℝ) (1635725634426697 / 1000000000000000000 : ℝ) (330322122807699 / 10000000000000000 : ℝ)
    (cell12841 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · have h := gap_lower (n := 12841) (a := (41111196175293 / 50000000000000 : ℝ)) (b := (160387089871 / 100000000000000 : ℝ)) (q := (2234701235819 / 100000000000000 : ℝ))
      (E := (cell12841 ⟨54, by decide⟩).energy) (xi := (330322122807699 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12841 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12841]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12841])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12841) (a := (41111196175293 / 50000000000000 : ℝ)) (b := (160387089871 / 100000000000000 : ℝ)) (q := (2234701235819 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12841])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12841])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12841]

theorem cert12841_55 : CellCertificate 12841 (220698248643369 / 2500000000000000 : ℝ) (1635725634426697 / 1000000000000000000 : ℝ) (330322122807699 / 10000000000000000 : ℝ)
    (cell12841 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · have h := gap_lower (n := 12841) (a := (8218875748189 / 10000000000000 : ℝ)) (b := (160387089871 / 100000000000000 : ℝ)) (q := (279338152799 / 12500000000000 : ℝ))
      (E := (cell12841 ⟨55, by decide⟩).energy) (xi := (330322122807699 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12841 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12841]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12841])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12841) (a := (8218875748189 / 10000000000000 : ℝ)) (b := (160387089871 / 100000000000000 : ℝ)) (q := (279338152799 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12841])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12841])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12841]

theorem cert12841_56 : CellCertificate 12841 (220698248643369 / 2500000000000000 : ℝ) (1635725634426697 / 1000000000000000000 : ℝ) (330322122807699 / 10000000000000000 : ℝ)
    (cell12841 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · have h := gap_lower (n := 12841) (a := (82155145766599 / 100000000000000 : ℝ)) (b := (160387089871 / 100000000000000 : ℝ)) (q := (2234709224791 / 100000000000000 : ℝ))
      (E := (cell12841 ⟨56, by decide⟩).energy) (xi := (330322122807699 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12841 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12841]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12841])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12841) (a := (82155145766599 / 100000000000000 : ℝ)) (b := (160387089871 / 100000000000000 : ℝ)) (q := (2234709224791 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12841])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12841])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12841]

theorem cert12841_57 : CellCertificate 12841 (220698248643369 / 2500000000000000 : ℝ) (1635725634426697 / 1000000000000000000 : ℝ) (330322122807699 / 10000000000000000 : ℝ)
    (cell12841 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · have h := gap_lower (n := 12841) (a := (41060778588569 / 50000000000000 : ℝ)) (b := (160387089871 / 100000000000000 : ℝ)) (q := (223471323907 / 10000000000000 : ℝ))
      (E := (cell12841 ⟨57, by decide⟩).energy) (xi := (330322122807699 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12841 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12841]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12841])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12841) (a := (41060778588569 / 50000000000000 : ℝ)) (b := (160387089871 / 100000000000000 : ℝ)) (q := (223471323907 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12841])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12841])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12841]

theorem cert12841_58 : CellCertificate 12841 (220698248643369 / 2500000000000000 : ℝ) (1635725634426697 / 1000000000000000000 : ℝ) (330322122807699 / 10000000000000000 : ℝ)
    (cell12841 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · have h := gap_lower (n := 12841) (a := (82087991686067 / 100000000000000 : ℝ)) (b := (160387089871 / 100000000000000 : ℝ)) (q := (2234717261079 / 100000000000000 : ℝ))
      (E := (cell12841 ⟨58, by decide⟩).energy) (xi := (330322122807699 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12841 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12841]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12841])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12841) (a := (82087991686067 / 100000000000000 : ℝ)) (b := (160387089871 / 100000000000000 : ℝ)) (q := (2234717261079 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12841])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12841])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12841]

theorem cert12841_59 : CellCertificate 12841 (220698248643369 / 2500000000000000 : ℝ) (1635725634426697 / 1000000000000000000 : ℝ) (330322122807699 / 10000000000000000 : ℝ)
    (cell12841 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · have h := gap_lower (n := 12841) (a := (82054449266081 / 100000000000000 : ℝ)) (b := (160387089871 / 100000000000000 : ℝ)) (q := (446944257293 / 20000000000000 : ℝ))
      (E := (cell12841 ⟨59, by decide⟩).energy) (xi := (330322122807699 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12841 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12841]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12841])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12841) (a := (82054449266081 / 100000000000000 : ℝ)) (b := (160387089871 / 100000000000000 : ℝ)) (q := (446944257293 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12841])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12841])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12841]

theorem cert12842_40 : CellCertificate 12842 (441382822830071 / 5000000000000000 : ℝ) (1635598219888397 / 1000000000000000000 : ℝ) (330295787766213 / 10000000000000000 : ℝ)
    (cell12842 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · have h := gap_lower (n := 12842) (a := (10336965605933 / 12500000000000 : ℝ)) (b := (20046806473 / 12500000000000 : ℝ)) (q := (1117263388359 / 50000000000000 : ℝ))
      (E := (cell12842 ⟨40, by decide⟩).energy) (xi := (330295787766213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12842 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12842]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12842])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12842) (a := (10336965605933 / 12500000000000 : ℝ)) (b := (20046806473 / 12500000000000 : ℝ)) (q := (1117263388359 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12842])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12842])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12842]

theorem cert12842_41 : CellCertificate 12842 (441382822830071 / 5000000000000000 : ℝ) (1635598219888397 / 1000000000000000000 : ℝ) (330295787766213 / 10000000000000000 : ℝ)
    (cell12842 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · have h := gap_lower (n := 12842) (a := (82661763154219 / 100000000000000 : ℝ)) (b := (20046806473 / 12500000000000 : ℝ)) (q := (2234530774553 / 100000000000000 : ℝ))
      (E := (cell12842 ⟨41, by decide⟩).energy) (xi := (330295787766213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12842 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12842]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12842])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12842) (a := (82661763154219 / 100000000000000 : ℝ)) (b := (20046806473 / 12500000000000 : ℝ)) (q := (2234530774553 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12842])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12842])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12842]

theorem cert12842_42 : CellCertificate 12842 (441382822830071 / 5000000000000000 : ℝ) (1635598219888397 / 1000000000000000000 : ℝ) (330295787766213 / 10000000000000000 : ℝ)
    (cell12842 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · have h := gap_lower (n := 12842) (a := (41313912507461 / 50000000000000 : ℝ)) (b := (20046806473 / 12500000000000 : ℝ)) (q := (2234534822423 / 100000000000000 : ℝ))
      (E := (cell12842 ⟨42, by decide⟩).energy) (xi := (330295787766213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12842 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12842]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12842])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12842) (a := (41313912507461 / 50000000000000 : ℝ)) (b := (20046806473 / 12500000000000 : ℝ)) (q := (2234534822423 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12842])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12842])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12842]

theorem cert12842_43 : CellCertificate 12842 (441382822830071 / 5000000000000000 : ℝ) (1635598219888397 / 1000000000000000000 : ℝ) (330295787766213 / 10000000000000000 : ℝ)
    (cell12842 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · have h := gap_lower (n := 12842) (a := (20648477599997 / 25000000000000 : ℝ)) (b := (20046806473 / 12500000000000 : ℝ)) (q := (1117269400847 / 50000000000000 : ℝ))
      (E := (cell12842 ⟨43, by decide⟩).energy) (xi := (330295787766213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12842 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12842]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12842])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12842) (a := (20648477599997 / 25000000000000 : ℝ)) (b := (20046806473 / 12500000000000 : ℝ)) (q := (1117269400847 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12842])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12842])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12842]

theorem cert12842_44 : CellCertificate 12842 (441382822830071 / 5000000000000000 : ℝ) (1635598219888397 / 1000000000000000000 : ℝ) (330295787766213 / 10000000000000000 : ℝ)
    (cell12842 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · have h := gap_lower (n := 12842) (a := (41280009639991 / 50000000000000 : ℝ)) (b := (20046806473 / 12500000000000 : ℝ)) (q := (1117271414371 / 50000000000000 : ℝ))
      (E := (cell12842 ⟨44, by decide⟩).energy) (xi := (330295787766213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12842 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12842]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12842])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12842) (a := (41280009639991 / 50000000000000 : ℝ)) (b := (20046806473 / 12500000000000 : ℝ)) (q := (1117271414371 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12842])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12842])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12842]

theorem cert12842_45 : CellCertificate 12842 (441382822830071 / 5000000000000000 : ℝ) (1635598219888397 / 1000000000000000000 : ℝ) (330295787766213 / 10000000000000000 : ℝ)
    (cell12842 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · have h := gap_lower (n := 12842) (a := (5157884476601 / 6250000000000 : ℝ)) (b := (20046806473 / 12500000000000 : ℝ)) (q := (2234546843283 / 100000000000000 : ℝ))
      (E := (cell12842 ⟨45, by decide⟩).energy) (xi := (330295787766213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12842 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12842]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12842])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12842) (a := (5157884476601 / 6250000000000 : ℝ)) (b := (20046806473 / 12500000000000 : ℝ)) (q := (2234546843283 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12842])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12842])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12842]

theorem cert12842_46 : CellCertificate 12842 (441382822830071 / 5000000000000000 : ℝ) (1635598219888397 / 1000000000000000000 : ℝ) (330295787766213 / 10000000000000000 : ℝ)
    (cell12842 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · have h := gap_lower (n := 12842) (a := (329969229631 / 400000000000 : ℝ)) (b := (20046806473 / 12500000000000 : ℝ)) (q := (2234550843623 / 100000000000000 : ℝ))
      (E := (cell12842 ⟨46, by decide⟩).energy) (xi := (330295787766213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12842 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12842]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12842])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12842) (a := (329969229631 / 400000000000 : ℝ)) (b := (20046806473 / 12500000000000 : ℝ)) (q := (2234550843623 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12842])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12842])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12842]

theorem cert12842_47 : CellCertificate 12842 (441382822830071 / 5000000000000000 : ℝ) (1635598219888397 / 1000000000000000000 : ℝ) (330295787766213 / 10000000000000000 : ℝ)
    (cell12842 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · have h := gap_lower (n := 12842) (a := (8245848659739 / 10000000000000 : ℝ)) (b := (20046806473 / 12500000000000 : ℝ)) (q := (1117277413927 / 50000000000000 : ℝ))
      (E := (cell12842 ⟨47, by decide⟩).energy) (xi := (330295787766213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12842 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12842]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12842])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12842) (a := (8245848659739 / 10000000000000 : ℝ)) (b := (20046806473 / 12500000000000 : ℝ)) (q := (1117277413927 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12842])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12842])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12842]

theorem cert12842_48 : CellCertificate 12842 (441382822830071 / 5000000000000000 : ℝ) (1635598219888397 / 1000000000000000000 : ℝ) (330295787766213 / 10000000000000000 : ℝ)
    (cell12842 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · have h := gap_lower (n := 12842) (a := (82424689165687 / 100000000000000 : ℝ)) (b := (20046806473 / 12500000000000 : ℝ)) (q := (558639713201 / 25000000000000 : ℝ))
      (E := (cell12842 ⟨48, by decide⟩).energy) (xi := (330295787766213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12842 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12842]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12842])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12842) (a := (82424689165687 / 100000000000000 : ℝ)) (b := (20046806473 / 12500000000000 : ℝ)) (q := (558639713201 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12842])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12842])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12842]

theorem cert12842_49 : CellCertificate 12842 (441382822830071 / 5000000000000000 : ℝ) (1635598219888397 / 1000000000000000000 : ℝ) (330295787766213 / 10000000000000000 : ℝ)
    (cell12842 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · have h := gap_lower (n := 12842) (a := (41195457541969 / 50000000000000 : ℝ)) (b := (20046806473 / 12500000000000 : ℝ)) (q := (2234562857233 / 100000000000000 : ℝ))
      (E := (cell12842 ⟨49, by decide⟩).energy) (xi := (330295787766213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12842 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12842]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12842])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12842) (a := (41195457541969 / 50000000000000 : ℝ)) (b := (20046806473 / 12500000000000 : ℝ)) (q := (2234562857233 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12842])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12842])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12842]

theorem cert12842_50 : CellCertificate 12842 (441382822830071 / 5000000000000000 : ℝ) (1635598219888397 / 1000000000000000000 : ℝ) (330295787766213 / 10000000000000000 : ℝ)
    (cell12842 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · have h := gap_lower (n := 12842) (a := (82357164323583 / 100000000000000 : ℝ)) (b := (20046806473 / 12500000000000 : ℝ)) (q := (1117283419297 / 50000000000000 : ℝ))
      (E := (cell12842 ⟨50, by decide⟩).energy) (xi := (330295787766213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12842 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12842]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12842])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12842) (a := (82357164323583 / 100000000000000 : ℝ)) (b := (20046806473 / 12500000000000 : ℝ)) (q := (1117283419297 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12842])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12842])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12842]

theorem cert12842_51 : CellCertificate 12842 (441382822830071 / 5000000000000000 : ℝ) (1635598219888397 / 1000000000000000000 : ℝ) (330295787766213 / 10000000000000000 : ℝ)
    (cell12842 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · have h := gap_lower (n := 12842) (a := (20580859214051 / 25000000000000 : ℝ)) (b := (20046806473 / 12500000000000 : ℝ)) (q := (1117285426573 / 50000000000000 : ℝ))
      (E := (cell12842 ⟨51, by decide⟩).energy) (xi := (330295787766213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12842 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12842]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12842])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12842) (a := (20580859214051 / 25000000000000 : ℝ)) (b := (20046806473 / 12500000000000 : ℝ)) (q := (1117285426573 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12842])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12842])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12842]

theorem cert12842_52 : CellCertificate 12842 (441382822830071 / 5000000000000000 : ℝ) (1635598219888397 / 1000000000000000000 : ℝ) (330295787766213 / 10000000000000000 : ℝ)
    (cell12842 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · have h := gap_lower (n := 12842) (a := (41144866326763 / 50000000000000 : ℝ)) (b := (20046806473 / 12500000000000 : ℝ)) (q := (2234574897989 / 100000000000000 : ℝ))
      (E := (cell12842 ⟨52, by decide⟩).energy) (xi := (330295787766213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12842 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12842]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12842])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12842) (a := (41144866326763 / 50000000000000 : ℝ)) (b := (20046806473 / 12500000000000 : ℝ)) (q := (2234574897989 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12842])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12842])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12842]

theorem cert12842_53 : CellCertificate 12842 (441382822830071 / 5000000000000000 : ℝ) (1635598219888397 / 1000000000000000000 : ℝ) (330295787766213 / 10000000000000000 : ℝ)
    (cell12842 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · have h := gap_lower (n := 12842) (a := (10282006460927 / 12500000000000 : ℝ)) (b := (20046806473 / 12500000000000 : ℝ)) (q := (1117289455473 / 50000000000000 : ℝ))
      (E := (cell12842 ⟨53, by decide⟩).energy) (xi := (330295787766213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12842 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12842]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12842])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12842) (a := (10282006460927 / 12500000000000 : ℝ)) (b := (20046806473 / 12500000000000 : ℝ)) (q := (1117289455473 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12842])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12842])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12842]

theorem cert12842_54 : CellCertificate 12842 (441382822830071 / 5000000000000000 : ℝ) (1635598219888397 / 1000000000000000000 : ℝ) (330295787766213 / 10000000000000000 : ℝ)
    (cell12842 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · have h := gap_lower (n := 12842) (a := (82222393929881 / 100000000000000 : ℝ)) (b := (20046806473 / 12500000000000 : ℝ)) (q := (2234582888627 / 100000000000000 : ℝ))
      (E := (cell12842 ⟨54, by decide⟩).energy) (xi := (330295787766213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12842 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12842]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12842])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12842) (a := (82222393929881 / 100000000000000 : ℝ)) (b := (20046806473 / 12500000000000 : ℝ)) (q := (2234582888627 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12842])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12842])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12842]

theorem cert12842_55 : CellCertificate 12842 (441382822830071 / 5000000000000000 : ℝ) (1635598219888397 / 1000000000000000000 : ℝ) (330295787766213 / 10000000000000000 : ℝ)
    (cell12842 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · have h := gap_lower (n := 12842) (a := (82188759353067 / 100000000000000 : ℝ)) (b := (20046806473 / 12500000000000 : ℝ)) (q := (139661680409 / 6250000000000 : ℝ))
      (E := (cell12842 ⟨55, by decide⟩).energy) (xi := (330295787766213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12842 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12842]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12842])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12842) (a := (82188759353067 / 100000000000000 : ℝ)) (b := (20046806473 / 12500000000000 : ℝ)) (q := (139661680409 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12842])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12842])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12842]

theorem cert12842_56 : CellCertificate 12842 (441382822830071 / 5000000000000000 : ℝ) (1635598219888397 / 1000000000000000000 : ℝ) (330295787766213 / 10000000000000000 : ℝ)
    (cell12842 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · have h := gap_lower (n := 12842) (a := (82155147929259 / 100000000000000 : ℝ)) (b := (20046806473 / 12500000000000 : ℝ)) (q := (1117295450481 / 50000000000000 : ℝ))
      (E := (cell12842 ⟨56, by decide⟩).energy) (xi := (330295787766213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12842 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12842]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12842])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12842) (a := (82155147929259 / 100000000000000 : ℝ)) (b := (20046806473 / 12500000000000 : ℝ)) (q := (1117295450481 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12842])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12842])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12842]

theorem cert12842_57 : CellCertificate 12842 (441382822830071 / 5000000000000000 : ℝ) (1635598219888397 / 1000000000000000000 : ℝ) (330295787766213 / 10000000000000000 : ℝ)
    (cell12842 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · have h := gap_lower (n := 12842) (a := (82121559630881 / 100000000000000 : ℝ)) (b := (20046806473 / 12500000000000 : ℝ)) (q := (2234594927937 / 100000000000000 : ℝ))
      (E := (cell12842 ⟨57, by decide⟩).energy) (xi := (330295787766213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12842 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12842]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12842])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12842) (a := (82121559630881 / 100000000000000 : ℝ)) (b := (20046806473 / 12500000000000 : ℝ)) (q := (2234594927937 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12842])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12842])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12842]

theorem cert12842_58 : CellCertificate 12842 (441382822830071 / 5000000000000000 : ℝ) (1635598219888397 / 1000000000000000000 : ℝ) (330295787766213 / 10000000000000000 : ℝ)
    (cell12842 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · have h := gap_lower (n := 12842) (a := (41043997215247 / 50000000000000 : ℝ)) (b := (20046806473 / 12500000000000 : ℝ)) (q := (1117299452067 / 50000000000000 : ℝ))
      (E := (cell12842 ⟨58, by decide⟩).energy) (xi := (330295787766213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12842 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12842]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12842])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12842) (a := (41043997215247 / 50000000000000 : ℝ)) (b := (20046806473 / 12500000000000 : ℝ)) (q := (1117299452067 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12842])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12842])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12842]

theorem cert12842_59 : CellCertificate 12842 (441382822830071 / 5000000000000000 : ℝ) (1635598219888397 / 1000000000000000000 : ℝ) (330295787766213 / 10000000000000000 : ℝ)
    (cell12842 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · have h := gap_lower (n := 12842) (a := (16410890460159 / 20000000000000 : ℝ)) (b := (20046806473 / 12500000000000 : ℝ)) (q := (2234602943541 / 100000000000000 : ℝ))
      (E := (cell12842 ⟨59, by decide⟩).energy) (xi := (330295787766213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12842 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12842]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12842])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12842) (a := (16410890460159 / 20000000000000 : ℝ)) (b := (20046806473 / 12500000000000 : ℝ)) (q := (2234602943541 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12842])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12842])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12842]

theorem cert12843_40 : CellCertificate 12843 (441369150415807 / 5000000000000000 : ℝ) (1635470825198413 / 1000000000000000000 : ℝ) (5160460265163 / 156250000000000 : ℝ)
    (cell12843 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · have h := gap_lower (n := 12843) (a := (82695722298837 / 100000000000000 : ℝ)) (b := (160361815699 / 100000000000000 : ℝ)) (q := (2234408515369 / 100000000000000 : ℝ))
      (E := (cell12843 ⟨40, by decide⟩).energy) (xi := (5160460265163 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12843 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12843]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12843])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12843) (a := (82695722298837 / 100000000000000 : ℝ)) (b := (160361815699 / 100000000000000 : ℝ)) (q := (2234408515369 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12843])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12843])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12843]

theorem cert12843_41 : CellCertificate 12843 (441369150415807 / 5000000000000000 : ℝ) (1635470825198413 / 1000000000000000000 : ℝ) (5160460265163 / 156250000000000 : ℝ)
    (cell12843 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · have h := gap_lower (n := 12843) (a := (16532352180623 / 20000000000000 : ℝ)) (b := (160361815699 / 100000000000000 : ℝ)) (q := (2234412515111 / 100000000000000 : ℝ))
      (E := (cell12843 ⟨41, by decide⟩).energy) (xi := (5160460265163 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12843 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12843]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12843])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12843) (a := (16532352180623 / 20000000000000 : ℝ)) (b := (160361815699 / 100000000000000 : ℝ)) (q := (2234412515111 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12843])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12843])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12843]

theorem cert12843_42 : CellCertificate 12843 (441369150415807 / 5000000000000000 : ℝ) (1635470825198413 / 1000000000000000000 : ℝ) (5160460265163 / 156250000000000 : ℝ)
    (cell12843 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · have h := gap_lower (n := 12843) (a := (8262782306093 / 10000000000000 : ℝ)) (b := (160361815699 / 100000000000000 : ℝ)) (q := (2234416506767 / 100000000000000 : ℝ))
      (E := (cell12843 ⟨42, by decide⟩).energy) (xi := (5160460265163 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12843 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12843]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12843])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12843) (a := (8262782306093 / 10000000000000 : ℝ)) (b := (160361815699 / 100000000000000 : ℝ)) (q := (2234416506767 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12843])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12843])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12843]

theorem cert12843_43 : CellCertificate 12843 (441369150415807 / 5000000000000000 : ℝ) (1635470825198413 / 1000000000000000000 : ℝ) (5160460265163 / 156250000000000 : ℝ)
    (cell12843 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · have h := gap_lower (n := 12843) (a := (82593908742699 / 100000000000000 : ℝ)) (b := (160361815699 / 100000000000000 : ℝ)) (q := (3575072877 / 160000000000 : ℝ))
      (E := (cell12843 ⟨43, by decide⟩).energy) (xi := (5160460265163 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12843 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12843]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12843])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12843) (a := (82593908742699 / 100000000000000 : ℝ)) (b := (160361815699 / 100000000000000 : ℝ)) (q := (3575072877 / 160000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12843])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12843])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12843]

theorem cert12843_44 : CellCertificate 12843 (441369150415807 / 5000000000000000 : ℝ) (1635470825198413 / 1000000000000000000 : ℝ) (5160460265163 / 156250000000000 : ℝ)
    (cell12843 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · have h := gap_lower (n := 12843) (a := (82560017918987 / 100000000000000 : ℝ)) (b := (160361815699 / 100000000000000 : ℝ)) (q := (1117212260141 / 50000000000000 : ℝ))
      (E := (cell12843 ⟨44, by decide⟩).energy) (xi := (5160460265163 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12843 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12843]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12843])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12843) (a := (82560017918987 / 100000000000000 : ℝ)) (b := (160361815699 / 100000000000000 : ℝ)) (q := (1117212260141 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12843])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12843])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12843]

theorem cert12843_45 : CellCertificate 12843 (441369150415807 / 5000000000000000 : ℝ) (1635470825198413 / 1000000000000000000 : ℝ) (5160460265163 / 156250000000000 : ℝ)
    (cell12843 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · have h := gap_lower (n := 12843) (a := (20631537640127 / 25000000000000 : ℝ)) (b := (160361815699 / 100000000000000 : ℝ)) (q := (2234428539447 / 100000000000000 : ℝ))
      (E := (cell12843 ⟨45, by decide⟩).energy) (xi := (5160460265163 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12843 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12843]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12843])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12843) (a := (20631537640127 / 25000000000000 : ℝ)) (b := (160361815699 / 100000000000000 : ℝ)) (q := (2234428539447 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12843])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12843])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12843]

theorem cert12843_46 : CellCertificate 12843 (441369150415807 / 5000000000000000 : ℝ) (1635470825198413 / 1000000000000000000 : ℝ) (5160460265163 / 156250000000000 : ℝ)
    (cell12843 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · have h := gap_lower (n := 12843) (a := (82492306638121 / 100000000000000 : ℝ)) (b := (160361815699 / 100000000000000 : ℝ)) (q := (446886509019 / 20000000000000 : ℝ))
      (E := (cell12843 ⟨46, by decide⟩).energy) (xi := (5160460265163 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12843 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12843]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12843])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12843) (a := (82492306638121 / 100000000000000 : ℝ)) (b := (160361815699 / 100000000000000 : ℝ)) (q := (446886509019 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12843])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12843])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12843]

theorem cert12843_47 : CellCertificate 12843 (441369150415807 / 5000000000000000 : ℝ) (1635470825198413 / 1000000000000000000 : ℝ) (5160460265163 / 156250000000000 : ℝ)
    (cell12843 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · have h := gap_lower (n := 12843) (a := (41229243061417 / 50000000000000 : ℝ)) (b := (160361815699 / 100000000000000 : ℝ)) (q := (558609133829 / 25000000000000 : ℝ))
      (E := (cell12843 ⟨47, by decide⟩).energy) (xi := (5160460265163 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12843 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12843]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12843])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12843) (a := (41229243061417 / 50000000000000 : ℝ)) (b := (160361815699 / 100000000000000 : ℝ)) (q := (558609133829 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12843])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12843])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12843]

theorem cert12843_48 : CellCertificate 12843 (441369150415807 / 5000000000000000 : ℝ) (1635470825198413 / 1000000000000000000 : ℝ) (5160460265163 / 156250000000000 : ℝ)
    (cell12843 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · have h := gap_lower (n := 12843) (a := (82424688985799 / 100000000000000 : ℝ)) (b := (160361815699 / 100000000000000 : ℝ)) (q := (279305070867 / 12500000000000 : ℝ))
      (E := (cell12843 ⟨48, by decide⟩).energy) (xi := (5160460265163 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12843 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12843]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12843])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12843) (a := (82424688985799 / 100000000000000 : ℝ)) (b := (160361815699 / 100000000000000 : ℝ)) (q := (279305070867 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12843])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12843])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12843]

theorem cert12843_49 : CellCertificate 12843 (441369150415807 / 5000000000000000 : ℝ) (1635470825198413 / 1000000000000000000 : ℝ) (5160460265163 / 156250000000000 : ℝ)
    (cell12843 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · have h := gap_lower (n := 12843) (a := (10298864399789 / 12500000000000 : ℝ)) (b := (160361815699 / 100000000000000 : ℝ)) (q := (2234444578719 / 100000000000000 : ℝ))
      (E := (cell12843 ⟨49, by decide⟩).energy) (xi := (5160460265163 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12843 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12843]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12843])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12843) (a := (10298864399789 / 12500000000000 : ℝ)) (b := (160361815699 / 100000000000000 : ℝ)) (q := (2234444578719 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12843])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12843])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12843]

theorem cert12843_50 : CellCertificate 12843 (441369150415807 / 5000000000000000 : ℝ) (1635470825198413 / 1000000000000000000 : ℝ) (5160460265163 / 156250000000000 : ℝ)
    (cell12843 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · have h := gap_lower (n := 12843) (a := (16471432946363 / 20000000000000 : ℝ)) (b := (160361815699 / 100000000000000 : ℝ)) (q := (2234448568113 / 100000000000000 : ℝ))
      (E := (cell12843 ⟨50, by decide⟩).energy) (xi := (5160460265163 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12843 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12843]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12843])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12843) (a := (16471432946363 / 20000000000000 : ℝ)) (b := (160361815699 / 100000000000000 : ℝ)) (q := (2234448568113 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12843])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12843])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12843]

theorem cert12843_51 : CellCertificate 12843 (441369150415807 / 5000000000000000 : ℝ) (1635470825198413 / 1000000000000000000 : ℝ) (5160460265163 / 156250000000000 : ℝ)
    (cell12843 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · have h := gap_lower (n := 12843) (a := (82323437557891 / 100000000000000 : ℝ)) (b := (160361815699 / 100000000000000 : ℝ)) (q := (2234452591379 / 100000000000000 : ℝ))
      (E := (cell12843 ⟨51, by decide⟩).energy) (xi := (5160460265163 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12843 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12843]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12843])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12843) (a := (82323437557891 / 100000000000000 : ℝ)) (b := (160361815699 / 100000000000000 : ℝ)) (q := (2234452591379 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12843])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12843])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12843]

theorem cert12843_52 : CellCertificate 12843 (441369150415807 / 5000000000000000 : ℝ) (1635470825198413 / 1000000000000000000 : ℝ) (5160460265163 / 156250000000000 : ℝ)
    (cell12843 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · have h := gap_lower (n := 12843) (a := (16457946729653 / 20000000000000 : ℝ)) (b := (160361815699 / 100000000000000 : ℝ)) (q := (558614146643 / 25000000000000 : ℝ))
      (E := (cell12843 ⟨52, by decide⟩).energy) (xi := (5160460265163 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12843 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12843]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12843])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12843) (a := (16457946729653 / 20000000000000 : ℝ)) (b := (160361815699 / 100000000000000 : ℝ)) (q := (558614146643 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12843])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12843])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12843]

theorem cert12843_53 : CellCertificate 12843 (441369150415807 / 5000000000000000 : ℝ) (1635470825198413 / 1000000000000000000 : ℝ) (5160460265163 / 156250000000000 : ℝ)
    (cell12843 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · have h := gap_lower (n := 12843) (a := (16451210594961 / 20000000000000 : ℝ)) (b := (160361815699 / 100000000000000 : ℝ)) (q := (279307576197 / 12500000000000 : ℝ))
      (E := (cell12843 ⟨53, by decide⟩).energy) (xi := (5160460265163 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12843 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12843]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12843])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12843) (a := (16451210594961 / 20000000000000 : ℝ)) (b := (160361815699 / 100000000000000 : ℝ)) (q := (279307576197 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12843])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12843])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12843]

theorem cert12843_54 : CellCertificate 12843 (441369150415807 / 5000000000000000 : ℝ) (1635470825198413 / 1000000000000000000 : ℝ) (5160460265163 / 156250000000000 : ℝ)
    (cell12843 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · have h := gap_lower (n := 12843) (a := (41111197754759 / 50000000000000 : ℝ)) (b := (160361815699 / 100000000000000 : ℝ)) (q := (1117232298991 / 50000000000000 : ℝ))
      (E := (cell12843 ⟨54, by decide⟩).energy) (xi := (5160460265163 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12843 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12843]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12843])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12843) (a := (41111197754759 / 50000000000000 : ℝ)) (b := (160361815699 / 100000000000000 : ℝ)) (q := (1117232298991 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12843])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12843])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12843]

theorem cert12843_55 : CellCertificate 12843 (441369150415807 / 5000000000000000 : ℝ) (1635470825198413 / 1000000000000000000 : ℝ) (5160460265163 / 156250000000000 : ℝ)
    (cell12843 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · have h := gap_lower (n := 12843) (a := (10273595153069 / 12500000000000 : ℝ)) (b := (160361815699 / 100000000000000 : ℝ)) (q := (1117234303651 / 50000000000000 : ℝ))
      (E := (cell12843 ⟨55, by decide⟩).energy) (xi := (5160460265163 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12843 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12843]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12843])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12843) (a := (10273595153069 / 12500000000000 : ℝ)) (b := (160361815699 / 100000000000000 : ℝ)) (q := (1117234303651 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12843])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12843])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12843]

theorem cert12843_56 : CellCertificate 12843 (441369150415807 / 5000000000000000 : ℝ) (1635470825198413 / 1000000000000000000 : ℝ) (5160460265163 / 156250000000000 : ℝ)
    (cell12843 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · have h := gap_lower (n := 12843) (a := (2567348440381 / 3125000000000 : ℝ)) (b := (160361815699 / 100000000000000 : ℝ)) (q := (1117236316899 / 50000000000000 : ℝ))
      (E := (cell12843 ⟨56, by decide⟩).energy) (xi := (5160460265163 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12843 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12843]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12843])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12843) (a := (2567348440381 / 3125000000000 : ℝ)) (b := (160361815699 / 100000000000000 : ℝ)) (q := (1117236316899 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12843])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12843])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12843]

theorem cert12843_57 : CellCertificate 12843 (441369150415807 / 5000000000000000 : ℝ) (1635470825198413 / 1000000000000000000 : ℝ) (5160460265163 / 156250000000000 : ℝ)
    (cell12843 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · have h := gap_lower (n := 12843) (a := (41060781042431 / 50000000000000 : ℝ)) (b := (160361815699 / 100000000000000 : ℝ)) (q := (69827394199 / 3125000000000 : ℝ))
      (E := (cell12843 ⟨57, by decide⟩).energy) (xi := (5160460265163 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12843 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12843]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12843])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12843) (a := (41060781042431 / 50000000000000 : ℝ)) (b := (160361815699 / 100000000000000 : ℝ)) (q := (69827394199 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12843])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12843])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12843]

theorem cert12843_58 : CellCertificate 12843 (441369150415807 / 5000000000000000 : ℝ) (1635470825198413 / 1000000000000000000 : ℝ) (5160460265163 / 156250000000000 : ℝ)
    (cell12843 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · have h := gap_lower (n := 12843) (a := (20521999293781 / 25000000000000 : ℝ)) (b := (160361815699 / 100000000000000 : ℝ)) (q := (558620165789 / 25000000000000 : ℝ))
      (E := (cell12843 ⟨58, by decide⟩).energy) (xi := (5160460265163 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12843 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12843]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12843])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12843) (a := (20521999293781 / 25000000000000 : ℝ)) (b := (160361815699 / 100000000000000 : ℝ)) (q := (558620165789 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12843])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12843])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12843]

theorem cert12843_59 : CellCertificate 12843 (441369150415807 / 5000000000000000 : ℝ) (1635470825198413 / 1000000000000000000 : ℝ) (5160460265163 / 156250000000000 : ℝ)
    (cell12843 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · have h := gap_lower (n := 12843) (a := (20513613833919 / 25000000000000 : ℝ)) (b := (160361815699 / 100000000000000 : ℝ)) (q := (2234484657461 / 100000000000000 : ℝ))
      (E := (cell12843 ⟨59, by decide⟩).energy) (xi := (5160460265163 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12843 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12843]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12843])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12843) (a := (20513613833919 / 25000000000000 : ℝ)) (b := (160361815699 / 100000000000000 : ℝ)) (q := (2234484657461 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12843])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12843])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12843]

theorem cert12844_40 : CellCertificate 12844 (882710960086933 / 10000000000000000 : ℝ) (817671725176053 / 500000000000000000 : ℝ) (165121565209627 / 5000000000000000 : ℝ)
    (cell12844 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · have h := gap_lower (n := 12844) (a := (82695719751047 / 100000000000000 : ℝ)) (b := (160349181617 / 100000000000000 : ℝ)) (q := (223429025097 / 10000000000000 : ℝ))
      (E := (cell12844 ⟨40, by decide⟩).energy) (xi := (165121565209627 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12844 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12844]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12844])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12844) (a := (82695719751047 / 100000000000000 : ℝ)) (b := (160349181617 / 100000000000000 : ℝ)) (q := (223429025097 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12844])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12844])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12844]

theorem cert12844_41 : CellCertificate 12844 (882710960086933 / 10000000000000000 : ℝ) (817671725176053 / 500000000000000000 : ℝ) (165121565209627 / 5000000000000000 : ℝ)
    (cell12844 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · have h := gap_lower (n := 12844) (a := (82661758652811 / 100000000000000 : ℝ)) (b := (160349181617 / 100000000000000 : ℝ)) (q := (2234294252657 / 100000000000000 : ℝ))
      (E := (cell12844 ⟨41, by decide⟩).energy) (xi := (165121565209627 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12844 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12844]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12844])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12844) (a := (82661758652811 / 100000000000000 : ℝ)) (b := (160349181617 / 100000000000000 : ℝ)) (q := (2234294252657 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12844])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12844])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12844]

theorem cert12844_42 : CellCertificate 12844 (882710960086933 / 10000000000000000 : ℝ) (817671725176053 / 500000000000000000 : ℝ) (165121565209627 / 5000000000000000 : ℝ)
    (cell12844 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · have h := gap_lower (n := 12844) (a := (82627821107703 / 100000000000000 : ℝ)) (b := (160349181617 / 100000000000000 : ℝ)) (q := (2234298246943 / 100000000000000 : ℝ))
      (E := (cell12844 ⟨42, by decide⟩).energy) (xi := (165121565209627 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12844 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12844]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12844])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12844) (a := (82627821107703 / 100000000000000 : ℝ)) (b := (160349181617 / 100000000000000 : ℝ)) (q := (2234298246943 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12844])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12844])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12844]

theorem cert12844_43 : CellCertificate 12844 (882710960086933 / 10000000000000000 : ℝ) (817671725176053 / 500000000000000000 : ℝ) (165121565209627 / 5000000000000000 : ℝ)
    (cell12844 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · have h := gap_lower (n := 12844) (a := (4129695354307 / 5000000000000 : ℝ)) (b := (160349181617 / 100000000000000 : ℝ)) (q := (139643889549 / 6250000000000 : ℝ))
      (E := (cell12844 ⟨43, by decide⟩).energy) (xi := (165121565209627 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12844 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12844]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12844])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12844) (a := (4129695354307 / 5000000000000 : ℝ)) (b := (160349181617 / 100000000000000 : ℝ)) (q := (139643889549 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12844])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12844])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12844]

theorem cert12844_44 : CellCertificate 12844 (882710960086933 / 10000000000000000 : ℝ) (817671725176053 / 500000000000000000 : ℝ) (165121565209627 / 5000000000000000 : ℝ)
    (cell12844 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · have h := gap_lower (n := 12844) (a := (82560016558687 / 100000000000000 : ℝ)) (b := (160349181617 / 100000000000000 : ℝ)) (q := (2234306267773 / 100000000000000 : ℝ))
      (E := (cell12844 ⟨44, by decide⟩).energy) (xi := (165121565209627 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12844 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12844]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12844])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12844) (a := (82560016558687 / 100000000000000 : ℝ)) (b := (160349181617 / 100000000000000 : ℝ)) (q := (2234306267773 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12844])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12844])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12844]

theorem cert12844_45 : CellCertificate 12844 (882710960086933 / 10000000000000000 : ℝ) (817671725176053 / 500000000000000000 : ℝ) (165121565209627 / 5000000000000000 : ℝ)
    (cell12844 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · have h := gap_lower (n := 12844) (a := (41263074748029 / 50000000000000 : ℝ)) (b := (160349181617 / 100000000000000 : ℝ)) (q := (1117155145811 / 50000000000000 : ℝ))
      (E := (cell12844 ⟨45, by decide⟩).energy) (xi := (165121565209627 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12844 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12844]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12844])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12844) (a := (41263074748029 / 50000000000000 : ℝ)) (b := (160349181617 / 100000000000000 : ℝ)) (q := (1117155145811 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12844])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12844])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12844]

theorem cert12844_46 : CellCertificate 12844 (882710960086933 / 10000000000000000 : ℝ) (817671725176053 / 500000000000000000 : ℝ) (165121565209627 / 5000000000000000 : ℝ)
    (cell12844 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · have h := gap_lower (n := 12844) (a := (16498461173823 / 20000000000000 : ℝ)) (b := (160349181617 / 100000000000000 : ℝ)) (q := (1117157151319 / 50000000000000 : ℝ))
      (E := (cell12844 ⟨46, by decide⟩).energy) (xi := (165121565209627 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12844 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12844]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12844])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12844) (a := (16498461173823 / 20000000000000 : ℝ)) (b := (160349181617 / 100000000000000 : ℝ)) (q := (1117157151319 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12844])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12844])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12844]

theorem cert12844_47 : CellCertificate 12844 (882710960086933 / 10000000000000000 : ℝ) (817671725176053 / 500000000000000000 : ℝ) (165121565209627 / 5000000000000000 : ℝ)
    (cell12844 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · have h := gap_lower (n := 12844) (a := (41229242824433 / 50000000000000 : ℝ)) (b := (160349181617 / 100000000000000 : ℝ)) (q := (558579574727 / 25000000000000 : ℝ))
      (E := (cell12844 ⟨47, by decide⟩).energy) (xi := (165121565209627 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12844 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12844]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12844])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12844) (a := (41229242824433 / 50000000000000 : ℝ)) (b := (160349181617 / 100000000000000 : ℝ)) (q := (558579574727 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12844])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12844])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12844]

theorem cert12844_48 : CellCertificate 12844 (882710960086933 / 10000000000000000 : ℝ) (817671725176053 / 500000000000000000 : ℝ) (165121565209627 / 5000000000000000 : ℝ)
    (cell12844 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · have h := gap_lower (n := 12844) (a := (82424688806463 / 100000000000000 : ℝ)) (b := (160349181617 / 100000000000000 : ℝ)) (q := (279290284789 / 12500000000000 : ℝ))
      (E := (cell12844 ⟨48, by decide⟩).energy) (xi := (165121565209627 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12844 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12844]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12844])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12844) (a := (82424688806463 / 100000000000000 : ℝ)) (b := (160349181617 / 100000000000000 : ℝ)) (q := (279290284789 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12844])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12844])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12844]

theorem cert12844_49 : CellCertificate 12844 (882710960086933 / 10000000000000000 : ℝ) (817671725176053 / 500000000000000000 : ℝ) (165121565209627 / 5000000000000000 : ℝ)
    (cell12844 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · have h := gap_lower (n := 12844) (a := (82390915313203 / 100000000000000 : ℝ)) (b := (160349181617 / 100000000000000 : ℝ)) (q := (2234326297483 / 100000000000000 : ℝ))
      (E := (cell12844 ⟨49, by decide⟩).energy) (xi := (165121565209627 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12844 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12844]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12844])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12844) (a := (82390915313203 / 100000000000000 : ℝ)) (b := (160349181617 / 100000000000000 : ℝ)) (q := (2234326297483 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12844])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12844])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12844]

theorem cert12844_50 : CellCertificate 12844 (882710960086933 / 10000000000000000 : ℝ) (817671725176053 / 500000000000000000 : ℝ) (165121565209627 / 5000000000000000 : ℝ)
    (cell12844 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · have h := gap_lower (n := 12844) (a := (82357165140529 / 100000000000000 : ℝ)) (b := (160349181617 / 100000000000000 : ℝ)) (q := (2234330294947 / 100000000000000 : ℝ))
      (E := (cell12844 ⟨50, by decide⟩).energy) (xi := (165121565209627 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12844 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12844]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12844])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12844) (a := (82357165140529 / 100000000000000 : ℝ)) (b := (160349181617 / 100000000000000 : ℝ)) (q := (2234330294947 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12844])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12844])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12844]

theorem cert12844_51 : CellCertificate 12844 (882710960086933 / 10000000000000000 : ℝ) (817671725176053 / 500000000000000000 : ℝ) (165121565209627 / 5000000000000000 : ℝ)
    (cell12844 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · have h := gap_lower (n := 12844) (a := (3292937530401 / 4000000000000 : ℝ)) (b := (160349181617 / 100000000000000 : ℝ)) (q := (2234334326961 / 100000000000000 : ℝ))
      (E := (cell12844 ⟨51, by decide⟩).energy) (xi := (165121565209627 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12844 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12844]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12844])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12844) (a := (3292937530401 / 4000000000000 : ℝ)) (b := (160349181617 / 100000000000000 : ℝ)) (q := (2234334326961 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12844])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12844])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12844]

theorem cert12844_52 : CellCertificate 12844 (882710960086933 / 10000000000000000 : ℝ) (817671725176053 / 500000000000000000 : ℝ) (165121565209627 / 5000000000000000 : ℝ)
    (cell12844 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · have h := gap_lower (n := 12844) (a := (10286216830427 / 12500000000000 : ℝ)) (b := (160349181617 / 100000000000000 : ℝ)) (q := (2234338331583 / 100000000000000 : ℝ))
      (E := (cell12844 ⟨52, by decide⟩).energy) (xi := (165121565209627 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12844 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12844]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12844])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12844) (a := (10286216830427 / 12500000000000 : ℝ)) (b := (160349181617 / 100000000000000 : ℝ)) (q := (2234338331583 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12844])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12844])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12844]

theorem cert12844_53 : CellCertificate 12844 (882710960086933 / 10000000000000000 : ℝ) (817671725176053 / 500000000000000000 : ℝ) (165121565209627 / 5000000000000000 : ℝ)
    (cell12844 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · have h := gap_lower (n := 12844) (a := (82256054262571 / 100000000000000 : ℝ)) (b := (160349181617 / 100000000000000 : ℝ)) (q := (558585576407 / 25000000000000 : ℝ))
      (E := (cell12844 ⟨53, by decide⟩).energy) (xi := (165121565209627 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12844 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12844]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12844])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12844) (a := (82256054262571 / 100000000000000 : ℝ)) (b := (160349181617 / 100000000000000 : ℝ)) (q := (558585576407 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12844])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12844])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12844]

theorem cert12844_54 : CellCertificate 12844 (882710960086933 / 10000000000000000 : ℝ) (817671725176053 / 500000000000000000 : ℝ) (165121565209627 / 5000000000000000 : ℝ)
    (cell12844 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · have h := gap_lower (n := 12844) (a := (82222397089497 / 100000000000000 : ℝ)) (b := (160349181617 / 100000000000000 : ℝ)) (q := (558586590971 / 25000000000000 : ℝ))
      (E := (cell12844 ⟨54, by decide⟩).energy) (xi := (165121565209627 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12844 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12844]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12844])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12844) (a := (82222397089497 / 100000000000000 : ℝ)) (b := (160349181617 / 100000000000000 : ℝ)) (q := (558586590971 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12844])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12844])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12844]

theorem cert12844_55 : CellCertificate 12844 (882710960086933 / 10000000000000000 : ℝ) (817671725176053 / 500000000000000000 : ℝ) (165121565209627 / 5000000000000000 : ℝ)
    (cell12844 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · have h := gap_lower (n := 12844) (a := (82188763096343 / 100000000000000 : ℝ)) (b := (160349181617 / 100000000000000 : ℝ)) (q := (2234350325553 / 100000000000000 : ℝ))
      (E := (cell12844 ⟨55, by decide⟩).energy) (xi := (165121565209627 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12844 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12844]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12844])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12844) (a := (82188763096343 / 100000000000000 : ℝ)) (b := (160349181617 / 100000000000000 : ℝ)) (q := (2234350325553 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12844])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12844])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12844]

theorem cert12844_56 : CellCertificate 12844 (882710960086933 / 10000000000000000 : ℝ) (817671725176053 / 500000000000000000 : ℝ) (165121565209627 / 5000000000000000 : ℝ)
    (cell12844 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · have h := gap_lower (n := 12844) (a := (20538788063849 / 25000000000000 : ℝ)) (b := (160349181617 / 100000000000000 : ℝ)) (q := (446870872833 / 20000000000000 : ℝ))
      (E := (cell12844 ⟨56, by decide⟩).energy) (xi := (165121565209627 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12844 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12844]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12844])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12844) (a := (20538788063849 / 25000000000000 : ℝ)) (b := (160349181617 / 100000000000000 : ℝ)) (q := (446870872833 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12844])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12844])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12844]

theorem cert12844_57 : CellCertificate 12844 (882710960086933 / 10000000000000000 : ℝ) (817671725176053 / 500000000000000000 : ℝ) (165121565209627 / 5000000000000000 : ℝ)
    (cell12844 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · have h := gap_lower (n := 12844) (a := (2053039113477 / 2500000000000 : ℝ)) (b := (160349181617 / 100000000000000 : ℝ)) (q := (558589589381 / 25000000000000 : ℝ))
      (E := (cell12844 ⟨57, by decide⟩).energy) (xi := (165121565209627 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12844 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12844]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12844])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12844) (a := (2053039113477 / 2500000000000 : ℝ)) (b := (160349181617 / 100000000000000 : ℝ)) (q := (558589589381 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12844])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12844])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12844]

theorem cert12844_58 : CellCertificate 12844 (882710960086933 / 10000000000000000 : ℝ) (817671725176053 / 500000000000000000 : ℝ) (165121565209627 / 5000000000000000 : ℝ)
    (cell12844 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · have h := gap_lower (n := 12844) (a := (82087999919957 / 100000000000000 : ℝ)) (b := (160349181617 / 100000000000000 : ℝ)) (q := (1117181180297 / 50000000000000 : ℝ))
      (E := (cell12844 ⟨58, by decide⟩).energy) (xi := (165121565209627 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12844 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12844]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12844])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12844) (a := (82087999919957 / 100000000000000 : ℝ)) (b := (160349181617 / 100000000000000 : ℝ)) (q := (1117181180297 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12844])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12844])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12844]

theorem cert12844_59 : CellCertificate 12844 (882710960086933 / 10000000000000000 : ℝ) (817671725176053 / 500000000000000000 : ℝ) (165121565209627 / 5000000000000000 : ℝ)
    (cell12844 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · have h := gap_lower (n := 12844) (a := (3282178334829 / 4000000000000 : ℝ)) (b := (160349181617 / 100000000000000 : ℝ)) (q := (2234366369017 / 100000000000000 : ℝ))
      (E := (cell12844 ⟨59, by decide⟩).energy) (xi := (165121565209627 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12844 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12844]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12844])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12844) (a := (3282178334829 / 4000000000000 : ℝ)) (b := (160349181617 / 100000000000000 : ℝ)) (q := (2234366369017 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12844])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12844])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12844]

theorem cert12845_40 : CellCertificate 12845 (882683623425141 / 10000000000000000 : ℝ) (40880402383621 / 25000000000000000 : ℝ) (13208672324463 / 400000000000000 : ℝ)
    (cell12845 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · have h := gap_lower (n := 12845) (a := (41347858602047 / 50000000000000 : ℝ)) (b := (160336549537 / 100000000000000 : ℝ)) (q := (558542995881 / 25000000000000 : ℝ))
      (E := (cell12845 ⟨40, by decide⟩).energy) (xi := (13208672324463 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12845 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12845]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12845])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12845) (a := (41347858602047 / 50000000000000 : ℝ)) (b := (160336549537 / 100000000000000 : ℝ)) (q := (558542995881 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12845])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12845])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12845]

theorem cert12845_41 : CellCertificate 12845 (882683623425141 / 10000000000000000 : ℝ) (40880402383621 / 25000000000000000 : ℝ) (13208672324463 / 400000000000000 : ℝ)
    (cell12845 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · have h := gap_lower (n := 12845) (a := (82661756403309 / 100000000000000 : ℝ)) (b := (160336549537 / 100000000000000 : ℝ)) (q := (2234175987191 / 100000000000000 : ℝ))
      (E := (cell12845 ⟨41, by decide⟩).energy) (xi := (13208672324463 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12845 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12845]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12845])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12845) (a := (82661756403309 / 100000000000000 : ℝ)) (b := (160336549537 / 100000000000000 : ℝ)) (q := (2234175987191 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12845])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12845])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12845]

theorem cert12845_42 : CellCertificate 12845 (882683623425141 / 10000000000000000 : ℝ) (40880402383621 / 25000000000000000 : ℝ) (13208672324463 / 400000000000000 : ℝ)
    (cell12845 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · have h := gap_lower (n := 12845) (a := (82627819155241 / 100000000000000 : ℝ)) (b := (160336549537 / 100000000000000 : ℝ)) (q := (2234180042953 / 100000000000000 : ℝ))
      (E := (cell12845 ⟨42, by decide⟩).energy) (xi := (13208672324463 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12845 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12845]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12845])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12845) (a := (82627819155241 / 100000000000000 : ℝ)) (b := (160336549537 / 100000000000000 : ℝ)) (q := (2234180042953 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12845])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12845])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12845]

theorem cert12845_43 : CellCertificate 12845 (882683623425141 / 10000000000000000 : ℝ) (40880402383621 / 25000000000000000 : ℝ) (13208672324463 / 400000000000000 : ℝ)
    (cell12845 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · have h := gap_lower (n := 12845) (a := (82593905430309 / 100000000000000 : ℝ)) (b := (160336549537 / 100000000000000 : ℝ)) (q := (223418403217 / 10000000000000 : ℝ))
      (E := (cell12845 ⟨43, by decide⟩).energy) (xi := (13208672324463 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12845 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12845]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12845])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12845) (a := (82593905430309 / 100000000000000 : ℝ)) (b := (160336549537 / 100000000000000 : ℝ)) (q := (223418403217 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12845])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12845])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12845]

theorem cert12845_44 : CellCertificate 12845 (882683623425141 / 10000000000000000 : ℝ) (40880402383621 / 25000000000000000 : ℝ) (13208672324463 / 400000000000000 : ℝ)
    (cell12845 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · have h := gap_lower (n := 12845) (a := (2064000379977 / 2500000000000 : ℝ)) (b := (160336549537 / 100000000000000 : ℝ)) (q := (2234188012363 / 100000000000000 : ℝ))
      (E := (cell12845 ⟨44, by decide⟩).energy) (xi := (13208672324463 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12845 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12845]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12845])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12845) (a := (2064000379977 / 2500000000000 : ℝ)) (b := (160336549537 / 100000000000000 : ℝ)) (q := (2234188012363 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12845])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12845])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12845]

theorem cert12845_45 : CellCertificate 12845 (882683623425141 / 10000000000000000 : ℝ) (40880402383621 / 25000000000000000 : ℝ) (13208672324463 / 400000000000000 : ℝ)
    (cell12845 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · have h := gap_lower (n := 12845) (a := (82526148432267 / 100000000000000 : ℝ)) (b := (160336549537 / 100000000000000 : ℝ)) (q := (558548010233 / 25000000000000 : ℝ))
      (E := (cell12845 ⟨45, by decide⟩).energy) (xi := (13208672324463 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12845 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12845]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12845])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12845) (a := (82526148432267 / 100000000000000 : ℝ)) (b := (160336549537 / 100000000000000 : ℝ)) (q := (558548010233 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12845])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12845])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12845]

theorem cert12845_46 : CellCertificate 12845 (882683623425141 / 10000000000000000 : ℝ) (40880402383621 / 25000000000000000 : ℝ) (13208672324463 / 400000000000000 : ℝ)
    (cell12845 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · have h := gap_lower (n := 12845) (a := (82492305100733 / 100000000000000 : ℝ)) (b := (160336549537 / 100000000000000 : ℝ)) (q := (2234196057351 / 100000000000000 : ℝ))
      (E := (cell12845 ⟨46, by decide⟩).energy) (xi := (13208672324463 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12845 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12845]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12845])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12845) (a := (82492305100733 / 100000000000000 : ℝ)) (b := (160336549537 / 100000000000000 : ℝ)) (q := (2234196057351 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12845])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12845])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12845]

theorem cert12845_47 : CellCertificate 12845 (882683623425141 / 10000000000000000 : ℝ) (40880402383621 / 25000000000000000 : ℝ) (13208672324463 / 400000000000000 : ℝ)
    (cell12845 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · have h := gap_lower (n := 12845) (a := (41229242587743 / 50000000000000 : ℝ)) (b := (160336549537 / 100000000000000 : ℝ)) (q := (2234200059707 / 100000000000000 : ℝ))
      (E := (cell12845 ⟨47, by decide⟩).energy) (xi := (13208672324463 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12845 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12845]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12845])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12845) (a := (41229242587743 / 50000000000000 : ℝ)) (b := (160336549537 / 100000000000000 : ℝ)) (q := (2234200059707 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12845])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12845])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12845]

theorem cert12845_48 : CellCertificate 12845 (882683623425141 / 10000000000000000 : ℝ) (40880402383621 / 25000000000000000 : ℝ) (13208672324463 / 400000000000000 : ℝ)
    (cell12845 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · have h := gap_lower (n := 12845) (a := (82424688627679 / 100000000000000 : ℝ)) (b := (160336549537 / 100000000000000 : ℝ)) (q := (2234204045879 / 100000000000000 : ℝ))
      (E := (cell12845 ⟨48, by decide⟩).energy) (xi := (13208672324463 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12845 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12845]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12845])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12845) (a := (82424688627679 / 100000000000000 : ℝ)) (b := (160336549537 / 100000000000000 : ℝ)) (q := (2234204045879 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12845])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12845])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12845]

theorem cert12845_49 : CellCertificate 12845 (882683623425141 / 10000000000000000 : ℝ) (40880402383621 / 25000000000000000 : ℝ) (13208672324463 / 400000000000000 : ℝ)
    (cell12845 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · have h := gap_lower (n := 12845) (a := (20597728857153 / 25000000000000 : ℝ)) (b := (160336549537 / 100000000000000 : ℝ)) (q := (1117104036249 / 50000000000000 : ℝ))
      (E := (cell12845 ⟨49, by decide⟩).energy) (xi := (13208672324463 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12845 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12845]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12845])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12845) (a := (20597728857153 / 25000000000000 : ℝ)) (b := (160336549537 / 100000000000000 : ℝ)) (q := (1117104036249 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12845])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12845])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12845]

theorem cert12845_50 : CellCertificate 12845 (882683623425141 / 10000000000000000 : ℝ) (40880402383621 / 25000000000000000 : ℝ) (13208672324463 / 400000000000000 : ℝ)
    (cell12845 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · have h := gap_lower (n := 12845) (a := (41178582774863 / 50000000000000 : ℝ)) (b := (160336549537 / 100000000000000 : ℝ)) (q := (2234212078091 / 100000000000000 : ℝ))
      (E := (cell12845 ⟨50, by decide⟩).energy) (xi := (13208672324463 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12845 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12845]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12845])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12845) (a := (41178582774863 / 50000000000000 : ℝ)) (b := (160336549537 / 100000000000000 : ℝ)) (q := (2234212078091 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12845])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12845])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12845]

theorem cert12845_51 : CellCertificate 12845 (882683623425141 / 10000000000000000 : ℝ) (40880402383621 / 25000000000000000 : ℝ) (13208672324463 / 400000000000000 : ℝ)
    (cell12845 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · have h := gap_lower (n := 12845) (a := (41161719481303 / 50000000000000 : ℝ)) (b := (160336549537 / 100000000000000 : ℝ)) (q := (446843211979 / 20000000000000 : ℝ))
      (E := (cell12845 ⟨51, by decide⟩).energy) (xi := (13208672324463 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12845 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12845]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12845])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12845) (a := (41161719481303 / 50000000000000 : ℝ)) (b := (160336549537 / 100000000000000 : ℝ)) (q := (446843211979 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12845])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12845])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12845]

theorem cert12845_52 : CellCertificate 12845 (882683623425141 / 10000000000000000 : ℝ) (40880402383621 / 25000000000000000 : ℝ) (13208672324463 / 400000000000000 : ℝ)
    (cell12845 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · have h := gap_lower (n := 12845) (a := (82289735638979 / 100000000000000 : ℝ)) (b := (160336549537 / 100000000000000 : ℝ)) (q := (111711003699 / 5000000000000 : ℝ))
      (E := (cell12845 ⟨52, by decide⟩).energy) (xi := (13208672324463 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12845 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12845]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12845])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12845) (a := (82289735638979 / 100000000000000 : ℝ)) (b := (160336549537 / 100000000000000 : ℝ)) (q := (111711003699 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12845])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12845])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12845]

theorem cert12845_53 : CellCertificate 12845 (882683623425141 / 10000000000000000 : ℝ) (40880402383621 / 25000000000000000 : ℝ) (13208672324463 / 400000000000000 : ℝ)
    (cell12845 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · have h := gap_lower (n := 12845) (a := (82256055550713 / 100000000000000 : ℝ)) (b := (160336549537 / 100000000000000 : ℝ)) (q := (446844823447 / 20000000000000 : ℝ))
      (E := (cell12845 ⟨53, by decide⟩).energy) (xi := (13208672324463 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12845 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12845]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12845])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12845) (a := (82256055550713 / 100000000000000 : ℝ)) (b := (160336549537 / 100000000000000 : ℝ)) (q := (446844823447 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12845])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12845])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12845]

theorem cert12845_54 : CellCertificate 12845 (882683623425141 / 10000000000000000 : ℝ) (40880402383621 / 25000000000000000 : ℝ) (13208672324463 / 400000000000000 : ℝ)
    (cell12845 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · have h := gap_lower (n := 12845) (a := (41111199334909 / 50000000000000 : ℝ)) (b := (160336549537 / 100000000000000 : ℝ)) (q := (446845625449 / 20000000000000 : ℝ))
      (E := (cell12845 ⟨54, by decide⟩).energy) (xi := (13208672324463 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12845 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12845]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12845])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12845) (a := (41111199334909 / 50000000000000 : ℝ)) (b := (160336549537 / 100000000000000 : ℝ)) (q := (446845625449 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12845])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12845])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12845]

theorem cert12845_55 : CellCertificate 12845 (882683623425141 / 10000000000000000 : ℝ) (40880402383621 / 25000000000000000 : ℝ) (13208672324463 / 400000000000000 : ℝ)
    (cell12845 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · have h := gap_lower (n := 12845) (a := (41094382484221 / 50000000000000 : ℝ)) (b := (160336549537 / 100000000000000 : ℝ)) (q := (2234232100411 / 100000000000000 : ℝ))
      (E := (cell12845 ⟨55, by decide⟩).energy) (xi := (13208672324463 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12845 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12845]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12845])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12845) (a := (41094382484221 / 50000000000000 : ℝ)) (b := (160336549537 / 100000000000000 : ℝ)) (q := (2234232100411 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12845])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12845])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12845]

theorem cert12845_56 : CellCertificate 12845 (882683623425141 / 10000000000000000 : ℝ) (40880402383621 / 25000000000000000 : ℝ) (13208672324463 / 400000000000000 : ℝ)
    (cell12845 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · have h := gap_lower (n := 12845) (a := (82155154418873 / 100000000000000 : ℝ)) (b := (160336549537 / 100000000000000 : ℝ)) (q := (111711804603 / 5000000000000 : ℝ))
      (E := (cell12845 ⟨56, by decide⟩).energy) (xi := (13208672324463 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12845 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12845]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12845])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12845) (a := (82155154418873 / 100000000000000 : ℝ)) (b := (160336549537 / 100000000000000 : ℝ)) (q := (111711804603 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12845])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12845])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12845]

theorem cert12845_57 : CellCertificate 12845 (882683623425141 / 10000000000000000 : ℝ) (40880402383621 / 25000000000000000 : ℝ) (13208672324463 / 400000000000000 : ℝ)
    (cell12845 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · have h := gap_lower (n := 12845) (a := (16424313398707 / 20000000000000 : ℝ)) (b := (160336549537 / 100000000000000 : ℝ)) (q := (1117120078703 / 50000000000000 : ℝ))
      (E := (cell12845 ⟨57, by decide⟩).energy) (xi := (13208672324463 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12845 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12845]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12845])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12845) (a := (16424313398707 / 20000000000000 : ℝ)) (b := (160336549537 / 100000000000000 : ℝ)) (q := (1117120078703 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12845])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12845])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12845]

theorem cert12845_58 : CellCertificate 12845 (882683623425141 / 10000000000000000 : ℝ) (40880402383621 / 25000000000000000 : ℝ) (13208672324463 / 400000000000000 : ℝ)
    (cell12845 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · have h := gap_lower (n := 12845) (a := (2565250083281 / 3125000000000 : ℝ)) (b := (160336549537 / 100000000000000 : ℝ)) (q := (2234244114817 / 100000000000000 : ℝ))
      (E := (cell12845 ⟨58, by decide⟩).energy) (xi := (13208672324463 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12845 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12845]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12845])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12845) (a := (2565250083281 / 3125000000000 : ℝ)) (b := (160336549537 / 100000000000000 : ℝ)) (q := (2234244114817 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12845])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12845])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12845]

theorem cert12845_59 : CellCertificate 12845 (882683623425141 / 10000000000000000 : ℝ) (40880402383621 / 25000000000000000 : ℝ) (13208672324463 / 400000000000000 : ℝ)
    (cell12845 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · have h := gap_lower (n := 12845) (a := (82054461405943 / 100000000000000 : ℝ)) (b := (160336549537 / 100000000000000 : ℝ)) (q := (446849627483 / 20000000000000 : ℝ))
      (E := (cell12845 ⟨59, by decide⟩).energy) (xi := (13208672324463 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12845 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12845]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12845])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12845) (a := (82054461405943 / 100000000000000 : ℝ)) (b := (160336549537 / 100000000000000 : ℝ)) (q := (446849627483 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12845])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12845])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12845]

theorem cert12846_40 : CellCertificate 12846 (882656290845277 / 10000000000000000 : ℝ) (81754438008599 / 50000000000000000 : ℝ) (82547622511573 / 2500000000000000 : ℝ)
    (cell12846 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · have h := gap_lower (n := 12846) (a := (10336964332247 / 12500000000000 : ℝ)) (b := (160323919459 / 100000000000000 : ℝ)) (q := (139628360737 / 6250000000000 : ℝ))
      (E := (cell12846 ⟨40, by decide⟩).energy) (xi := (82547622511573 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12846 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12846]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12846])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12846) (a := (10336964332247 / 12500000000000 : ℝ)) (b := (160323919459 / 100000000000000 : ℝ)) (q := (139628360737 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12846])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12846])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12846]

theorem cert12846_41 : CellCertificate 12846 (882656290845277 / 10000000000000000 : ℝ) (81754438008599 / 50000000000000000 : ℝ) (82547622511573 / 2500000000000000 : ℝ)
    (cell12846 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · have h := gap_lower (n := 12846) (a := (41330877077303 / 50000000000000 : ℝ)) (b := (160323919459 / 100000000000000 : ℝ)) (q := (893623111 / 40000000000 : ℝ))
      (E := (cell12846 ⟨41, by decide⟩).energy) (xi := (82547622511573 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12846 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12846]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12846])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12846) (a := (41330877077303 / 50000000000000 : ℝ)) (b := (160323919459 / 100000000000000 : ℝ)) (q := (893623111 / 40000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12846])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12846])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12846]

theorem cert12846_42 : CellCertificate 12846 (882656290845277 / 10000000000000000 : ℝ) (81754438008599 / 50000000000000000 : ℝ) (82547622511573 / 2500000000000000 : ℝ)
    (cell12846 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · have h := gap_lower (n := 12846) (a := (10328477150443 / 12500000000000 : ℝ)) (b := (160323919459 / 100000000000000 : ℝ)) (q := (111703088859 / 5000000000000 : ℝ))
      (E := (cell12846 ⟨42, by decide⟩).energy) (xi := (82547622511573 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12846 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12846]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12846])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12846) (a := (10328477150443 / 12500000000000 : ℝ)) (b := (160323919459 / 100000000000000 : ℝ)) (q := (111703088859 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12846])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12846])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12846]

theorem cert12846_43 : CellCertificate 12846 (882656290845277 / 10000000000000000 : ℝ) (81754438008599 / 50000000000000000 : ℝ) (82547622511573 / 2500000000000000 : ℝ)
    (cell12846 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · have h := gap_lower (n := 12846) (a := (10324237971901 / 12500000000000 : ℝ)) (b := (160323919459 / 100000000000000 : ℝ)) (q := (2234065828617 / 100000000000000 : ℝ))
      (E := (cell12846 ⟨43, by decide⟩).energy) (xi := (82547622511573 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12846 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12846]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12846])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12846) (a := (10324237971901 / 12500000000000 : ℝ)) (b := (160323919459 / 100000000000000 : ℝ)) (q := (2234065828617 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12846])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12846])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12846]

theorem cert12846_44 : CellCertificate 12846 (882656290845277 / 10000000000000000 : ℝ) (81754438008599 / 50000000000000000 : ℝ) (82547622511573 / 2500000000000000 : ℝ)
    (cell12846 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · have h := gap_lower (n := 12846) (a := (41280006920083 / 50000000000000 : ℝ)) (b := (160323919459 / 100000000000000 : ℝ)) (q := (2234069812907 / 100000000000000 : ℝ))
      (E := (cell12846 ⟨44, by decide⟩).energy) (xi := (82547622511573 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12846 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12846]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12846])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12846) (a := (41280006920083 / 50000000000000 : ℝ)) (b := (160323919459 / 100000000000000 : ℝ)) (q := (2234069812907 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12846])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12846])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12846]

theorem cert12846_45 : CellCertificate 12846 (882656290845277 / 10000000000000000 : ℝ) (81754438008599 / 50000000000000000 : ℝ) (82547622511573 / 2500000000000000 : ℝ)
    (cell12846 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · have h := gap_lower (n := 12846) (a := (41263073684567 / 50000000000000 : ℝ)) (b := (160323919459 / 100000000000000 : ℝ)) (q := (139629615391 / 6250000000000 : ℝ))
      (E := (cell12846 ⟨45, by decide⟩).energy) (xi := (82547622511573 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12846 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12846]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12846])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12846) (a := (41263073684567 / 50000000000000 : ℝ)) (b := (160323919459 / 100000000000000 : ℝ)) (q := (139629615391 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12846])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12846])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12846]

theorem cert12846_46 : CellCertificate 12846 (882656290845277 / 10000000000000000 : ℝ) (81754438008599 / 50000000000000000 : ℝ) (82547622511573 / 2500000000000000 : ℝ)
    (cell12846 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · have h := gap_lower (n := 12846) (a := (82492304332973 / 100000000000000 : ℝ)) (b := (160323919459 / 100000000000000 : ℝ)) (q := (446815561847 / 20000000000000 : ℝ))
      (E := (cell12846 ⟨46, by decide⟩).energy) (xi := (82547622511573 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12846 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12846]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12846])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12846) (a := (82492304332973 / 100000000000000 : ℝ)) (b := (160323919459 / 100000000000000 : ℝ)) (q := (446815561847 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12846])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12846])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12846]

theorem cert12846_47 : CellCertificate 12846 (882656290845277 / 10000000000000000 : ℝ) (81754438008599 / 50000000000000000 : ℝ) (82547622511573 / 2500000000000000 : ℝ)
    (cell12846 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · have h := gap_lower (n := 12846) (a := (82458484702693 / 100000000000000 : ℝ)) (b := (160323919459 / 100000000000000 : ℝ)) (q := (1117040908857 / 50000000000000 : ℝ))
      (E := (cell12846 ⟨47, by decide⟩).energy) (xi := (82547622511573 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12846 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12846]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12846])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12846) (a := (82458484702693 / 100000000000000 : ℝ)) (b := (160323919459 / 100000000000000 : ℝ)) (q := (1117040908857 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12846])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12846])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12846]

theorem cert12846_48 : CellCertificate 12846 (882656290845277 / 10000000000000000 : ℝ) (81754438008599 / 50000000000000000 : ℝ) (82547622511573 / 2500000000000000 : ℝ)
    (cell12846 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · have h := gap_lower (n := 12846) (a := (10303086056181 / 12500000000000 : ℝ)) (b := (160323919459 / 100000000000000 : ℝ)) (q := (1117042934819 / 50000000000000 : ℝ))
      (E := (cell12846 ⟨48, by decide⟩).energy) (xi := (82547622511573 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12846 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12846]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12846])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12846) (a := (10303086056181 / 12500000000000 : ℝ)) (b := (160323919459 / 100000000000000 : ℝ)) (q := (1117042934819 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12846])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12846])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12846]

theorem cert12846_49 : CellCertificate 12846 (882656290845277 / 10000000000000000 : ℝ) (81754438008599 / 50000000000000000 : ℝ) (82547622511573 / 2500000000000000 : ℝ)
    (cell12846 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · have h := gap_lower (n := 12846) (a := (41195457772269 / 50000000000000 : ℝ)) (b := (160323919459 / 100000000000000 : ℝ)) (q := (2234089844793 / 100000000000000 : ℝ))
      (E := (cell12846 ⟨49, by decide⟩).energy) (xi := (82547622511573 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12846 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12846]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12846])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12846) (a := (41195457772269 / 50000000000000 : ℝ)) (b := (160323919459 / 100000000000000 : ℝ)) (q := (2234089844793 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12846])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12846])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12846]

theorem cert12846_50 : CellCertificate 12846 (882656290845277 / 10000000000000000 : ℝ) (81754438008599 / 50000000000000000 : ℝ) (82547622511573 / 2500000000000000 : ℝ)
    (cell12846 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · have h := gap_lower (n := 12846) (a := (20589291489851 / 25000000000000 : ℝ)) (b := (160323919459 / 100000000000000 : ℝ)) (q := (2234093858551 / 100000000000000 : ℝ))
      (E := (cell12846 ⟨50, by decide⟩).energy) (xi := (82547622511573 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12846 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12846]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12846])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12846) (a := (20589291489851 / 25000000000000 : ℝ)) (b := (160323919459 / 100000000000000 : ℝ)) (q := (2234093858551 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12846])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12846])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12846]

theorem cert12846_51 : CellCertificate 12846 (882656290845277 / 10000000000000000 : ℝ) (81754438008599 / 50000000000000000 : ℝ) (82547622511573 / 2500000000000000 : ℝ)
    (cell12846 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · have h := gap_lower (n := 12846) (a := (82323439665633 / 100000000000000 : ℝ)) (b := (160323919459 / 100000000000000 : ℝ)) (q := (5585244623 / 250000000000 : ℝ))
      (E := (cell12846 ⟨51, by decide⟩).energy) (xi := (82547622511573 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12846 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12846]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12846])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12846) (a := (82323439665633 / 100000000000000 : ℝ)) (b := (160323919459 / 100000000000000 : ℝ)) (q := (5585244623 / 250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12846])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12846])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12846]

theorem cert12846_52 : CellCertificate 12846 (882656290845277 / 10000000000000000 : ℝ) (81754438008599 / 50000000000000000 : ℝ) (82547622511573 / 2500000000000000 : ℝ)
    (cell12846 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · have h := gap_lower (n := 12846) (a := (82289736634953 / 100000000000000 : ℝ)) (b := (160323919459 / 100000000000000 : ℝ)) (q := (2234101872809 / 100000000000000 : ℝ))
      (E := (cell12846 ⟨52, by decide⟩).energy) (xi := (82547622511573 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12846 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12846]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12846])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12846) (a := (82289736634953 / 100000000000000 : ℝ)) (b := (160323919459 / 100000000000000 : ℝ)) (q := (2234101872809 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12846])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12846])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12846]

theorem cert12846_53 : CellCertificate 12846 (882656290845277 / 10000000000000000 : ℝ) (81754438008599 / 50000000000000000 : ℝ) (82547622511573 / 2500000000000000 : ℝ)
    (cell12846 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · have h := gap_lower (n := 12846) (a := (1285250888113 / 1562500000000 : ℝ)) (b := (160323919459 / 100000000000000 : ℝ)) (q := (2234105867199 / 100000000000000 : ℝ))
      (E := (cell12846 ⟨53, by decide⟩).energy) (xi := (82547622511573 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12846 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12846]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12846])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12846) (a := (1285250888113 / 1562500000000 : ℝ)) (b := (160323919459 / 100000000000000 : ℝ)) (q := (2234105867199 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12846])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12846])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12846]

theorem cert12846_54 : CellCertificate 12846 (882656290845277 / 10000000000000000 : ℝ) (81754438008599 / 50000000000000000 : ℝ) (82547622511573 / 2500000000000000 : ℝ)
    (cell12846 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · have h := gap_lower (n := 12846) (a := (82222400250481 / 100000000000000 : ℝ)) (b := (160323919459 / 100000000000000 : ℝ)) (q := (446821977613 / 20000000000000 : ℝ))
      (E := (cell12846 ⟨54, by decide⟩).energy) (xi := (82547622511573 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12846 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12846]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12846])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12846) (a := (82222400250481 / 100000000000000 : ℝ)) (b := (160323919459 / 100000000000000 : ℝ)) (q := (446821977613 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12846])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12846])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12846]

theorem cert12846_55 : CellCertificate 12846 (882656290845277 / 10000000000000000 : ℝ) (81754438008599 / 50000000000000000 : ℝ) (82547622511573 / 2500000000000000 : ℝ)
    (cell12846 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · have h := gap_lower (n := 12846) (a := (5136797927553 / 6250000000000 : ℝ)) (b := (160323919459 / 100000000000000 : ℝ)) (q := (2234113931877 / 100000000000000 : ℝ))
      (E := (cell12846 ⟨55, by decide⟩).energy) (xi := (82547622511573 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12846 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12846]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12846])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12846) (a := (5136797927553 / 6250000000000 : ℝ)) (b := (160323919459 / 100000000000000 : ℝ)) (q := (2234113931877 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12846])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12846])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12846]

theorem cert12846_56 : CellCertificate 12846 (882656290845277 / 10000000000000000 : ℝ) (81754438008599 / 50000000000000000 : ℝ) (82547622511573 / 2500000000000000 : ℝ)
    (cell12846 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · have h := gap_lower (n := 12846) (a := (82155156582621 / 100000000000000 : ℝ)) (b := (160323919459 / 100000000000000 : ℝ)) (q := (27926474197 / 1250000000000 : ℝ))
      (E := (cell12846 ⟨56, by decide⟩).energy) (xi := (82547622511573 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12846 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12846]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12846])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12846) (a := (82155156582621 / 100000000000000 : ℝ)) (b := (160323919459 / 100000000000000 : ℝ)) (q := (27926474197 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12846])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12846])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12846]

theorem cert12846_57 : CellCertificate 12846 (882656290845277 / 10000000000000000 : ℝ) (81754438008599 / 50000000000000000 : ℝ) (82547622511573 / 2500000000000000 : ℝ)
    (cell12846 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · have h := gap_lower (n := 12846) (a := (82121569448227 / 100000000000000 : ℝ)) (b := (160323919459 / 100000000000000 : ℝ)) (q := (1117060947847 / 50000000000000 : ℝ))
      (E := (cell12846 ⟨57, by decide⟩).energy) (xi := (82547622511573 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12846 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12846]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12846])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12846) (a := (82121569448227 / 100000000000000 : ℝ)) (b := (160323919459 / 100000000000000 : ℝ)) (q := (1117060947847 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12846])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12846])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12846]

theorem cert12846_58 : CellCertificate 12846 (882656290845277 / 10000000000000000 : ℝ) (81754438008599 / 50000000000000000 : ℝ) (82547622511573 / 2500000000000000 : ℝ)
    (cell12846 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · have h := gap_lower (n := 12846) (a := (82088005410229 / 100000000000000 : ℝ)) (b := (160323919459 / 100000000000000 : ℝ)) (q := (1117062962913 / 50000000000000 : ℝ))
      (E := (cell12846 ⟨58, by decide⟩).energy) (xi := (82547622511573 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12846 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12846]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12846])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12846) (a := (82088005410229 / 100000000000000 : ℝ)) (b := (160323919459 / 100000000000000 : ℝ)) (q := (1117062962913 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12846])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12846])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12846]

theorem cert12846_59 : CellCertificate 12846 (882656290845277 / 10000000000000000 : ℝ) (81754438008599 / 50000000000000000 : ℝ) (82547622511573 / 2500000000000000 : ℝ)
    (cell12846 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · have h := gap_lower (n := 12846) (a := (82054464441327 / 100000000000000 : ℝ)) (b := (160323919459 / 100000000000000 : ℝ)) (q := (2234129962659 / 100000000000000 : ℝ))
      (E := (cell12846 ⟨59, by decide⟩).energy) (xi := (82547622511573 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12846 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12846]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12846])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12846) (a := (82054464441327 / 100000000000000 : ℝ)) (b := (160323919459 / 100000000000000 : ℝ)) (q := (2234129962659 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12846])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12846])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12846]

theorem cert12847_40 : CellCertificate 12847 (55164310146649 / 625000000000000 : ℝ) (817480722414447 / 500000000000000000 : ℝ) (10317630506947 / 312500000000000 : ℝ)
    (cell12847 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · have h := gap_lower (n := 12847) (a := (82695712112693 / 100000000000000 : ℝ)) (b := (160311291381 / 100000000000000 : ℝ)) (q := (2233935615777 / 100000000000000 : ℝ))
      (E := (cell12847 ⟨40, by decide⟩).energy) (xi := (10317630506947 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12847 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12847]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12847])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12847) (a := (82695712112693 / 100000000000000 : ℝ)) (b := (160311291381 / 100000000000000 : ℝ)) (q := (2233935615777 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12847])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12847])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12847]

theorem cert12847_41 : CellCertificate 12847 (55164310146649 / 625000000000000 : ℝ) (817480722414447 / 500000000000000000 : ℝ) (10317630506947 / 312500000000000 : ℝ)
    (cell12847 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · have h := gap_lower (n := 12847) (a := (82661751906703 / 100000000000000 : ℝ)) (b := (160311291381 / 100000000000000 : ℝ)) (q := (1116969811793 / 50000000000000 : ℝ))
      (E := (cell12847 ⟨41, by decide⟩).energy) (xi := (10317630506947 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12847 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12847]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12847])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12847) (a := (82661751906703 / 100000000000000 : ℝ)) (b := (160311291381 / 100000000000000 : ℝ)) (q := (1116969811793 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12847])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12847])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12847]

theorem cert12847_42 : CellCertificate 12847 (55164310146649 / 625000000000000 : ℝ) (817480722414447 / 500000000000000000 : ℝ) (10317630506947 / 312500000000000 : ℝ)
    (cell12847 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · have h := gap_lower (n := 12847) (a := (82627815252611 / 100000000000000 : ℝ)) (b := (160311291381 / 100000000000000 : ℝ)) (q := (558485906513 / 25000000000000 : ℝ))
      (E := (cell12847 ⟨42, by decide⟩).energy) (xi := (10317630506947 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12847 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12847]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12847])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12847) (a := (82627815252611 / 100000000000000 : ℝ)) (b := (160311291381 / 100000000000000 : ℝ)) (q := (558485906513 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12847])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12847])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12847]

theorem cert12847_43 : CellCertificate 12847 (55164310146649 / 625000000000000 : ℝ) (817480722414447 / 500000000000000000 : ℝ) (10317630506947 / 312500000000000 : ℝ)
    (cell12847 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · have h := gap_lower (n := 12847) (a := (20648475530209 / 25000000000000 : ℝ)) (b := (160311291381 / 100000000000000 : ℝ)) (q := (2233947622129 / 100000000000000 : ℝ))
      (E := (cell12847 ⟨43, by decide⟩).energy) (xi := (10317630506947 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12847 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12847]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12847])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12847) (a := (20648475530209 / 25000000000000 : ℝ)) (b := (160311291381 / 100000000000000 : ℝ)) (q := (2233947622129 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12847])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12847])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12847]

theorem cert12847_44 : CellCertificate 12847 (55164310146649 / 625000000000000 : ℝ) (817480722414447 / 500000000000000000 : ℝ) (10317630506947 / 312500000000000 : ℝ)
    (cell12847 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · have h := gap_lower (n := 12847) (a := (82560012481947 / 100000000000000 : ℝ)) (b := (160311291381 / 100000000000000 : ℝ)) (q := (2233951610551 / 100000000000000 : ℝ))
      (E := (cell12847 ⟨44, by decide⟩).energy) (xi := (10317630506947 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12847 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12847]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12847])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12847) (a := (82560012481947 / 100000000000000 : ℝ)) (b := (160311291381 / 100000000000000 : ℝ)) (q := (2233951610551 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12847])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12847])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12847]

theorem cert12847_45 : CellCertificate 12847 (55164310146649 / 625000000000000 : ℝ) (817480722414447 / 500000000000000000 : ℝ) (10317630506947 / 312500000000000 : ℝ)
    (cell12847 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · have h := gap_lower (n := 12847) (a := (82526146306659 / 100000000000000 : ℝ)) (b := (160311291381 / 100000000000000 : ℝ)) (q := (2233955648717 / 100000000000000 : ℝ))
      (E := (cell12847 ⟨45, by decide⟩).energy) (xi := (10317630506947 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12847 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12847]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12847])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12847) (a := (82526146306659 / 100000000000000 : ℝ)) (b := (160311291381 / 100000000000000 : ℝ)) (q := (2233955648717 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12847])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12847])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12847]

theorem cert12847_46 : CellCertificate 12847 (55164310146649 / 625000000000000 : ℝ) (817480722414447 / 500000000000000000 : ℝ) (10317630506947 / 312500000000000 : ℝ)
    (cell12847 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · have h := gap_lower (n := 12847) (a := (20623075891459 / 25000000000000 : ℝ)) (b := (160311291381 / 100000000000000 : ℝ)) (q := (2233959676097 / 100000000000000 : ℝ))
      (E := (cell12847 ⟨46, by decide⟩).energy) (xi := (10317630506947 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12847 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12847]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12847])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12847) (a := (20623075891459 / 25000000000000 : ℝ)) (b := (160311291381 / 100000000000000 : ℝ)) (q := (2233959676097 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12847])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12847])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12847]

theorem cert12847_47 : CellCertificate 12847 (55164310146649 / 625000000000000 : ℝ) (817480722414447 / 500000000000000000 : ℝ) (10317630506947 / 312500000000000 : ℝ)
    (cell12847 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · have h := gap_lower (n := 12847) (a := (10307310528811 / 12500000000000 : ℝ)) (b := (160311291381 / 100000000000000 : ℝ)) (q := (446792726371 / 20000000000000 : ℝ))
      (E := (cell12847 ⟨47, by decide⟩).energy) (xi := (10317630506947 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12847 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12847]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12847])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12847) (a := (10307310528811 / 12500000000000 : ℝ)) (b := (160311291381 / 100000000000000 : ℝ)) (q := (446792726371 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12847])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12847])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12847]

theorem cert12847_48 : CellCertificate 12847 (55164310146649 / 625000000000000 : ℝ) (817480722414447 / 500000000000000000 : ℝ) (10317630506947 / 312500000000000 : ℝ)
    (cell12847 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · have h := gap_lower (n := 12847) (a := (82424688271769 / 100000000000000 : ℝ)) (b := (160311291381 / 100000000000000 : ℝ)) (q := (1116983845321 / 50000000000000 : ℝ))
      (E := (cell12847 ⟨48, by decide⟩).energy) (xi := (10317630506947 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12847 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12847]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12847])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12847) (a := (82424688271769 / 100000000000000 : ℝ)) (b := (160311291381 / 100000000000000 : ℝ)) (q := (1116983845321 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12847])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12847])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12847]

theorem cert12847_49 : CellCertificate 12847 (55164310146649 / 625000000000000 : ℝ) (817480722414447 / 500000000000000000 : ℝ) (10317630506947 / 312500000000000 : ℝ)
    (cell12847 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · have h := gap_lower (n := 12847) (a := (4119545783049 / 5000000000000 : ℝ)) (b := (160311291381 / 100000000000000 : ℝ)) (q := (1116985836671 / 50000000000000 : ℝ))
      (E := (cell12847 ⟨49, by decide⟩).energy) (xi := (10317630506947 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12847 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12847]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12847])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12847) (a := (4119545783049 / 5000000000000 : ℝ)) (b := (160311291381 / 100000000000000 : ℝ)) (q := (1116985836671 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12847])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12847])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12847]

theorem cert12847_50 : CellCertificate 12847 (55164310146649 / 625000000000000 : ℝ) (817480722414447 / 500000000000000000 : ℝ) (10317630506947 / 312500000000000 : ℝ)
    (cell12847 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · have h := gap_lower (n := 12847) (a := (20589291592391 / 25000000000000 : ℝ)) (b := (160311291381 / 100000000000000 : ℝ)) (q := (558493923831 / 25000000000000 : ℝ))
      (E := (cell12847 ⟨50, by decide⟩).energy) (xi := (10317630506947 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12847 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12847]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12847])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12847) (a := (20589291592391 / 25000000000000 : ℝ)) (b := (160311291381 / 100000000000000 : ℝ)) (q := (558493923831 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12847])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12847])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12847]

theorem cert12847_51 : CellCertificate 12847 (55164310146649 / 625000000000000 : ℝ) (817480722414447 / 500000000000000000 : ℝ) (10317630506947 / 312500000000000 : ℝ)
    (cell12847 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · have h := gap_lower (n := 12847) (a := (20580860092277 / 25000000000000 : ℝ)) (b := (160311291381 / 100000000000000 : ℝ)) (q := (2233979694877 / 100000000000000 : ℝ))
      (E := (cell12847 ⟨51, by decide⟩).energy) (xi := (10317630506947 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12847 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12847]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12847])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12847) (a := (20580860092277 / 25000000000000 : ℝ)) (b := (160311291381 / 100000000000000 : ℝ)) (q := (2233979694877 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12847])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12847])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12847]

theorem cert12847_52 : CellCertificate 12847 (55164310146649 / 625000000000000 : ℝ) (817480722414447 / 500000000000000000 : ℝ) (10317630506947 / 312500000000000 : ℝ)
    (cell12847 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · have h := gap_lower (n := 12847) (a := (82289737631339 / 100000000000000 : ℝ)) (b := (160311291381 / 100000000000000 : ℝ)) (q := (1116991834513 / 50000000000000 : ℝ))
      (E := (cell12847 ⟨52, by decide⟩).energy) (xi := (10317630506947 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12847 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12847]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12847])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12847) (a := (82289737631339 / 100000000000000 : ℝ)) (b := (160311291381 / 100000000000000 : ℝ)) (q := (1116991834513 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12847])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12847])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12847]

theorem cert12847_53 : CellCertificate 12847 (55164310146649 / 625000000000000 : ℝ) (817480722414447 / 500000000000000000 : ℝ) (10317630506947 / 312500000000000 : ℝ)
    (cell12847 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · have h := gap_lower (n := 12847) (a := (321312727063 / 390625000000 : ℝ)) (b := (160311291381 / 100000000000000 : ℝ)) (q := (27924846659 / 1250000000000 : ℝ))
      (E := (cell12847 ⟨53, by decide⟩).energy) (xi := (10317630506947 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12847 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12847]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12847])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12847) (a := (321312727063 / 390625000000 : ℝ)) (b := (160311291381 / 100000000000000 : ℝ)) (q := (27924846659 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12847])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12847])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12847]

theorem cert12847_54 : CellCertificate 12847 (55164310146649 / 625000000000000 : ℝ) (817480722414447 / 500000000000000000 : ℝ) (10317630506947 / 312500000000000 : ℝ)
    (cell12847 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · have h := gap_lower (n := 12847) (a := (16444480366297 / 20000000000000 : ℝ)) (b := (160311291381 / 100000000000000 : ℝ)) (q := (558497926359 / 25000000000000 : ℝ))
      (E := (cell12847 ⟨54, by decide⟩).energy) (xi := (10317630506947 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12847 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12847]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12847])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12847) (a := (16444480366297 / 20000000000000 : ℝ)) (b := (160311291381 / 100000000000000 : ℝ)) (q := (558497926359 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12847])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12847])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12847]

theorem cert12847_55 : CellCertificate 12847 (55164310146649 / 625000000000000 : ℝ) (817480722414447 / 500000000000000000 : ℝ) (10317630506947 / 312500000000000 : ℝ)
    (cell12847 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · have h := gap_lower (n := 12847) (a := (2054719217839 / 2500000000000 : ℝ)) (b := (160311291381 / 100000000000000 : ℝ)) (q := (2233995701727 / 100000000000000 : ℝ))
      (E := (cell12847 ⟨55, by decide⟩).energy) (xi := (10317630506947 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12847 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12847]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12847])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12847) (a := (2054719217839 / 2500000000000 : ℝ)) (b := (160311291381 / 100000000000000 : ℝ)) (q := (2233995701727 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12847])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12847])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12847]

theorem cert12847_56 : CellCertificate 12847 (55164310146649 / 625000000000000 : ℝ) (817480722414447 / 500000000000000000 : ℝ) (10317630506947 / 312500000000000 : ℝ)
    (cell12847 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · have h := gap_lower (n := 12847) (a := (82155158746641 / 100000000000000 : ℝ)) (b := (160311291381 / 100000000000000 : ℝ)) (q := (446799943571 / 20000000000000 : ℝ))
      (E := (cell12847 ⟨56, by decide⟩).energy) (xi := (10317630506947 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12847 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12847]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12847])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12847) (a := (82155158746641 / 100000000000000 : ℝ)) (b := (160311291381 / 100000000000000 : ℝ)) (q := (446799943571 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12847])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12847])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12847]

theorem cert12847_57 : CellCertificate 12847 (55164310146649 / 625000000000000 : ℝ) (817480722414447 / 500000000000000000 : ℝ) (10317630506947 / 312500000000000 : ℝ)
    (cell12847 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · have h := gap_lower (n := 12847) (a := (20530392975789 / 25000000000000 : ℝ)) (b := (160311291381 / 100000000000000 : ℝ)) (q := (2234003749871 / 100000000000000 : ℝ))
      (E := (cell12847 ⟨57, by decide⟩).energy) (xi := (10317630506947 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12847 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12847]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12847])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12847) (a := (20530392975789 / 25000000000000 : ℝ)) (b := (160311291381 / 100000000000000 : ℝ)) (q := (2234003749871 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12847])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12847])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12847]

theorem cert12847_58 : CellCertificate 12847 (55164310146649 / 625000000000000 : ℝ) (817480722414447 / 500000000000000000 : ℝ) (10317630506947 / 312500000000000 : ℝ)
    (cell12847 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · have h := gap_lower (n := 12847) (a := (82088008155669 / 100000000000000 : ℝ)) (b := (160311291381 / 100000000000000 : ℝ)) (q := (1117003867219 / 50000000000000 : ℝ))
      (E := (cell12847 ⟨58, by decide⟩).energy) (xi := (10317630506947 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12847 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12847]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12847])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12847) (a := (82088008155669 / 100000000000000 : ℝ)) (b := (160311291381 / 100000000000000 : ℝ)) (q := (1117003867219 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12847])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12847])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12847]

theorem cert12847_59 : CellCertificate 12847 (55164310146649 / 625000000000000 : ℝ) (817480722414447 / 500000000000000000 : ℝ) (10317630506947 / 312500000000000 : ℝ)
    (cell12847 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · have h := gap_lower (n := 12847) (a := (1025680843461 / 1250000000000 : ℝ)) (b := (160311291381 / 100000000000000 : ℝ)) (q := (2234011785541 / 100000000000000 : ℝ))
      (E := (cell12847 ⟨59, by decide⟩).energy) (xi := (10317630506947 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12847 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12847]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12847])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12847) (a := (1025680843461 / 1250000000000 : ℝ)) (b := (160311291381 / 100000000000000 : ℝ)) (q := (2234011785541 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12847])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12847])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12847]

theorem cert12848_40 : CellCertificate 12848 (55162602370469 / 625000000000000 : ℝ) (1634834149310949 / 1000000000000000000 : ℝ) (330137866638509 / 10000000000000000 : ℝ)
    (cell12848 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · have h := gap_lower (n := 12848) (a := (41347854784123 / 50000000000000 : ℝ)) (b := (32059733061 / 20000000000000 : ℝ)) (q := (446763491343 / 20000000000000 : ℝ))
      (E := (cell12848 ⟨40, by decide⟩).energy) (xi := (330137866638509 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12848 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12848]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12848])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12848) (a := (41347854784123 / 50000000000000 : ℝ)) (b := (32059733061 / 20000000000000 : ℝ)) (q := (446763491343 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12848])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12848])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12848]

theorem cert12848_41 : CellCertificate 12848 (55162602370469 / 625000000000000 : ℝ) (1634834149310949 / 1000000000000000000 : ℝ) (330137866638509 / 10000000000000000 : ℝ)
    (cell12848 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · have h := gap_lower (n := 12848) (a := (206654374149 / 250000000000 : ℝ)) (b := (32059733061 / 20000000000000 : ℝ)) (q := (1116910733331 / 50000000000000 : ℝ))
      (E := (cell12848 ⟨41, by decide⟩).energy) (xi := (330137866638509 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12848 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12848]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12848])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12848) (a := (206654374149 / 250000000000 : ℝ)) (b := (32059733061 / 20000000000000 : ℝ)) (q := (1116910733331 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12848])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12848])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12848]

theorem cert12848_42 : CellCertificate 12848 (55162602370469 / 625000000000000 : ℝ) (1634834149310949 / 1000000000000000000 : ℝ) (330137866638509 / 10000000000000000 : ℝ)
    (cell12848 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · have h := gap_lower (n := 12848) (a := (41313906651221 / 50000000000000 : ℝ)) (b := (32059733061 / 20000000000000 : ℝ)) (q := (2233825471951 / 100000000000000 : ℝ))
      (E := (cell12848 ⟨42, by decide⟩).energy) (xi := (330137866638509 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12848 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12848]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12848])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12848) (a := (41313906651221 / 50000000000000 : ℝ)) (b := (32059733061 / 20000000000000 : ℝ)) (q := (2233825471951 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12848])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12848])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12848]

theorem cert12848_43 : CellCertificate 12848 (55162602370469 / 625000000000000 : ℝ) (1634834149310949 / 1000000000000000000 : ℝ) (330137866638509 / 10000000000000000 : ℝ)
    (cell12848 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · have h := gap_lower (n := 12848) (a := (82593900467193 / 100000000000000 : ℝ)) (b := (32059733061 / 20000000000000 : ℝ)) (q := (446765894307 / 20000000000000 : ℝ))
      (E := (cell12848 ⟨43, by decide⟩).energy) (xi := (330137866638509 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12848 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12848]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12848])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12848) (a := (82593900467193 / 100000000000000 : ℝ)) (b := (32059733061 / 20000000000000 : ℝ)) (q := (446765894307 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12848])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12848])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12848]

theorem cert12848_44 : CellCertificate 12848 (55162602370469 / 625000000000000 : ℝ) (1634834149310949 / 1000000000000000000 : ℝ) (330137866638509 / 10000000000000000 : ℝ)
    (cell12848 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · have h := gap_lower (n := 12848) (a := (4128000556221 / 5000000000000 : ℝ)) (b := (32059733061 / 20000000000000 : ℝ)) (q := (44676669283 / 2000000000000 : ℝ))
      (E := (cell12848 ⟨44, by decide⟩).energy) (xi := (330137866638509 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12848 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12848]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12848])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12848) (a := (4128000556221 / 5000000000000 : ℝ)) (b := (32059733061 / 20000000000000 : ℝ)) (q := (44676669283 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12848])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12848])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12848]

theorem cert12848_45 : CellCertificate 12848 (55162602370469 / 625000000000000 : ℝ) (1634834149310949 / 1000000000000000000 : ℝ) (330137866638509 / 10000000000000000 : ℝ)
    (cell12848 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · have h := gap_lower (n := 12848) (a := (41263072622421 / 50000000000000 : ℝ)) (b := (32059733061 / 20000000000000 : ℝ)) (q := (2233837507191 / 100000000000000 : ℝ))
      (E := (cell12848 ⟨45, by decide⟩).energy) (xi := (330137866638509 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12848 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12848]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12848])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12848) (a := (41263072622421 / 50000000000000 : ℝ)) (b := (32059733061 / 20000000000000 : ℝ)) (q := (2233837507191 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12848])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12848])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12848]

theorem cert12848_46 : CellCertificate 12848 (55162602370469 / 625000000000000 : ℝ) (1634834149310949 / 1000000000000000000 : ℝ) (330137866638509 / 10000000000000000 : ℝ)
    (cell12848 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · have h := gap_lower (n := 12848) (a := (82492302799321 / 100000000000000 : ℝ)) (b := (32059733061 / 20000000000000 : ℝ)) (q := (2233841481229 / 100000000000000 : ℝ))
      (E := (cell12848 ⟨46, by decide⟩).energy) (xi := (330137866638509 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12848 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12848]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12848])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12848) (a := (82492302799321 / 100000000000000 : ℝ)) (b := (32059733061 / 20000000000000 : ℝ)) (q := (2233841481229 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12848])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12848])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12848]

theorem cert12848_47 : CellCertificate 12848 (55162602370469 / 625000000000000 : ℝ) (1634834149310949 / 1000000000000000000 : ℝ) (330137866638509 / 10000000000000000 : ℝ)
    (cell12848 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · have h := gap_lower (n := 12848) (a := (82458483758869 / 100000000000000 : ℝ)) (b := (32059733061 / 20000000000000 : ℝ)) (q := (2233845502131 / 100000000000000 : ℝ))
      (E := (cell12848 ⟨47, by decide⟩).energy) (xi := (330137866638509 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12848 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12848]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12848])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12848) (a := (82458483758869 / 100000000000000 : ℝ)) (b := (32059733061 / 20000000000000 : ℝ)) (q := (2233845502131 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12848])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12848])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12848]

theorem cert12848_48 : CellCertificate 12848 (55162602370469 / 625000000000000 : ℝ) (1634834149310949 / 1000000000000000000 : ℝ) (330137866638509 / 10000000000000000 : ℝ)
    (cell12848 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · have h := gap_lower (n := 12848) (a := (41212344047321 / 50000000000000 : ℝ)) (b := (32059733061 / 20000000000000 : ℝ)) (q := (2233849508891 / 100000000000000 : ℝ))
      (E := (cell12848 ⟨48, by decide⟩).energy) (xi := (330137866638509 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12848 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12848]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12848])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12848) (a := (41212344047321 / 50000000000000 : ℝ)) (b := (32059733061 / 20000000000000 : ℝ)) (q := (2233849508891 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12848])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12848])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12848]

theorem cert12848_49 : CellCertificate 12848 (55162602370469 / 625000000000000 : ℝ) (1634834149310949 / 1000000000000000000 : ℝ) (330137866638509 / 10000000000000000 : ℝ)
    (cell12848 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · have h := gap_lower (n := 12848) (a := (82390915777939 / 100000000000000 : ℝ)) (b := (32059733061 / 20000000000000 : ℝ)) (q := (2233853499171 / 100000000000000 : ℝ))
      (E := (cell12848 ⟨49, by decide⟩).energy) (xi := (330137866638509 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12848 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12848]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12848])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12848) (a := (82390915777939 / 100000000000000 : ℝ)) (b := (32059733061 / 20000000000000 : ℝ)) (q := (2233853499171 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12848])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12848])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12848]

theorem cert12848_50 : CellCertificate 12848 (55162602370469 / 625000000000000 : ℝ) (1634834149310949 / 1000000000000000000 : ℝ) (330137866638509 / 10000000000000000 : ℝ)
    (cell12848 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · have h := gap_lower (n := 12848) (a := (41178583390103 / 50000000000000 : ℝ)) (b := (32059733061 / 20000000000000 : ℝ)) (q := (2233857529413 / 100000000000000 : ℝ))
      (E := (cell12848 ⟨50, by decide⟩).energy) (xi := (330137866638509 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12848 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12848]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12848])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12848) (a := (41178583390103 / 50000000000000 : ℝ)) (b := (32059733061 / 20000000000000 : ℝ)) (q := (2233857529413 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12848])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12848])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12848]

theorem cert12848_51 : CellCertificate 12848 (55162602370469 / 625000000000000 : ℝ) (1634834149310949 / 1000000000000000000 : ℝ) (330137866638509 / 10000000000000000 : ℝ)
    (cell12848 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · have h := gap_lower (n := 12848) (a := (20580860268257 / 25000000000000 : ℝ)) (b := (32059733061 / 20000000000000 : ℝ)) (q := (2233861537907 / 100000000000000 : ℝ))
      (E := (cell12848 ⟨51, by decide⟩).energy) (xi := (330137866638509 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12848 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12848]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12848])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12848) (a := (20580860268257 / 25000000000000 : ℝ)) (b := (32059733061 / 20000000000000 : ℝ)) (q := (2233861537907 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12848])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12848])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12848]

theorem cert12848_52 : CellCertificate 12848 (55162602370469 / 625000000000000 : ℝ) (1634834149310949 / 1000000000000000000 : ℝ) (330137866638509 / 10000000000000000 : ℝ)
    (cell12848 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · have h := gap_lower (n := 12848) (a := (10286217328517 / 12500000000000 : ℝ)) (b := (32059733061 / 20000000000000 : ℝ)) (q := (1116932760837 / 50000000000000 : ℝ))
      (E := (cell12848 ⟨52, by decide⟩).energy) (xi := (330137866638509 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12848 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12848]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12848])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12848) (a := (10286217328517 / 12500000000000 : ℝ)) (b := (32059733061 / 20000000000000 : ℝ)) (q := (1116932760837 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12848])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12848])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12848]

theorem cert12848_53 : CellCertificate 12848 (55162602370469 / 625000000000000 : ℝ) (1634834149310949 / 1000000000000000000 : ℝ) (330137866638509 / 10000000000000000 : ℝ)
    (cell12848 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · have h := gap_lower (n := 12848) (a := (411280297087 / 500000000000 : ℝ)) (b := (32059733061 / 20000000000000 : ℝ)) (q := (2233869536599 / 100000000000000 : ℝ))
      (E := (cell12848 ⟨53, by decide⟩).energy) (xi := (330137866638509 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12848 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12848]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12848])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12848) (a := (411280297087 / 500000000000 : ℝ)) (b := (32059733061 / 20000000000000 : ℝ)) (q := (2233869536599 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12848])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12848])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12848]

theorem cert12848_54 : CellCertificate 12848 (55162602370469 / 625000000000000 : ℝ) (1634834149310949 / 1000000000000000000 : ℝ) (330137866638509 / 10000000000000000 : ℝ)
    (cell12848 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · have h := gap_lower (n := 12848) (a := (82222403412831 / 100000000000000 : ℝ)) (b := (32059733061 / 20000000000000 : ℝ)) (q := (446774715871 / 20000000000000 : ℝ))
      (E := (cell12848 ⟨54, by decide⟩).energy) (xi := (330137866638509 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12848 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12848]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12848])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12848) (a := (82222403412831 / 100000000000000 : ℝ)) (b := (32059733061 / 20000000000000 : ℝ)) (q := (446774715871 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12848])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12848])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12848]

theorem cert12848_55 : CellCertificate 12848 (55162602370469 / 625000000000000 : ℝ) (1634834149310949 / 1000000000000000000 : ℝ) (330137866638509 / 10000000000000000 : ℝ)
    (cell12848 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · have h := gap_lower (n := 12848) (a := (82188770586579 / 100000000000000 : ℝ)) (b := (32059733061 / 20000000000000 : ℝ)) (q := (1116938793649 / 50000000000000 : ℝ))
      (E := (cell12848 ⟨55, by decide⟩).energy) (xi := (330137866638509 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12848 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12848]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12848])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12848) (a := (82188770586579 / 100000000000000 : ℝ)) (b := (32059733061 / 20000000000000 : ℝ)) (q := (1116938793649 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12848])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12848])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12848]

theorem cert12848_56 : CellCertificate 12848 (55162602370469 / 625000000000000 : ℝ) (1634834149310949 / 1000000000000000000 : ℝ) (330137866638509 / 10000000000000000 : ℝ)
    (cell12848 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · have h := gap_lower (n := 12848) (a := (82155160910933 / 100000000000000 : ℝ)) (b := (32059733061 / 20000000000000 : ℝ)) (q := (2233881556617 / 100000000000000 : ℝ))
      (E := (cell12848 ⟨56, by decide⟩).energy) (xi := (330137866638509 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12848 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12848]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12848])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12848) (a := (82155160910933 / 100000000000000 : ℝ)) (b := (32059733061 / 20000000000000 : ℝ)) (q := (2233881556617 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12848])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12848])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12848]

theorem cert12848_57 : CellCertificate 12848 (55162602370469 / 625000000000000 : ℝ) (1634834149310949 / 1000000000000000000 : ℝ) (330137866638509 / 10000000000000000 : ℝ)
    (cell12848 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · have h := gap_lower (n := 12848) (a := (41060787179161 / 50000000000000 : ℝ)) (b := (32059733061 / 20000000000000 : ℝ)) (q := (1116942800807 / 50000000000000 : ℝ))
      (E := (cell12848 ⟨57, by decide⟩).energy) (xi := (330137866638509 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12848 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12848]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12848])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12848) (a := (41060787179161 / 50000000000000 : ℝ)) (b := (32059733061 / 20000000000000 : ℝ)) (q := (1116942800807 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12848])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12848])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12848]

theorem cert12848_58 : CellCertificate 12848 (55162602370469 / 625000000000000 : ℝ) (1634834149310949 / 1000000000000000000 : ℝ) (330137866638509 / 10000000000000000 : ℝ)
    (cell12848 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · have h := gap_lower (n := 12848) (a := (82088010901311 / 100000000000000 : ℝ)) (b := (32059733061 / 20000000000000 : ℝ)) (q := (446777919967 / 20000000000000 : ℝ))
      (E := (cell12848 ⟨58, by decide⟩).energy) (xi := (330137866638509 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12848 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12848]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12848])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12848) (a := (82088010901311 / 100000000000000 : ℝ)) (b := (32059733061 / 20000000000000 : ℝ)) (q := (446777919967 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12848])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12848])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12848]

theorem cert12848_59 : CellCertificate 12848 (55162602370469 / 625000000000000 : ℝ) (1634834149310949 / 1000000000000000000 : ℝ) (330137866638509 / 10000000000000000 : ℝ)
    (cell12848 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · have h := gap_lower (n := 12848) (a := (410272352563 / 500000000000 : ℝ)) (b := (32059733061 / 20000000000000 : ℝ)) (q := (111694680303 / 5000000000000 : ℝ))
      (E := (cell12848 ⟨59, by decide⟩).energy) (xi := (330137866638509 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12848 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12848]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12848])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12848) (a := (410272352563 / 500000000000 : ℝ)) (b := (32059733061 / 20000000000000 : ℝ)) (q := (111694680303 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12848])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12848])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12848]

theorem cert12849_40 : CellCertificate 12849 (441287158793839 / 5000000000000000 : ℝ) (408676718403379 / 250000000000000000 : ℝ) (165055780646903 / 5000000000000000 : ℝ)
    (cell12849 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · have h := gap_lower (n := 12849) (a := (16539141404927 / 20000000000000 : ℝ)) (b := (40071510307 / 25000000000000 : ℝ)) (q := (2233699353371 / 100000000000000 : ℝ))
      (E := (cell12849 ⟨40, by decide⟩).energy) (xi := (165055780646903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12849 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12849]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12849])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12849) (a := (16539141404927 / 20000000000000 : ℝ)) (b := (40071510307 / 25000000000000 : ℝ)) (q := (2233699353371 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12849])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12849])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12849]

theorem cert12849_41 : CellCertificate 12849 (441287158793839 / 5000000000000000 : ℝ) (408676718403379 / 250000000000000000 : ℝ) (165055780646903 / 5000000000000000 : ℝ)
    (cell12849 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · have h := gap_lower (n := 12849) (a := (82661747413297 / 100000000000000 : ℝ)) (b := (40071510307 / 25000000000000 : ℝ)) (q := (446740673103 / 20000000000000 : ℝ))
      (E := (cell12849 ⟨41, by decide⟩).energy) (xi := (165055780646903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12849 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12849]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12849])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12849) (a := (82661747413297 / 100000000000000 : ℝ)) (b := (40071510307 / 25000000000000 : ℝ)) (q := (446740673103 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12849])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12849])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12849]

theorem cert12849_42 : CellCertificate 12849 (441287158793839 / 5000000000000000 : ℝ) (408676718403379 / 250000000000000000 : ℝ) (165055780646903 / 5000000000000000 : ℝ)
    (cell12849 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · have h := gap_lower (n := 12849) (a := (41313905676519 / 50000000000000 : ℝ)) (b := (40071510307 / 25000000000000 : ℝ)) (q := (2233707373687 / 100000000000000 : ℝ))
      (E := (cell12849 ⟨42, by decide⟩).energy) (xi := (165055780646903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12849 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12849]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12849])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12849) (a := (41313905676519 / 50000000000000 : ℝ)) (b := (40071510307 / 25000000000000 : ℝ)) (q := (2233707373687 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12849])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12849])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12849]

theorem cert12849_43 : CellCertificate 12849 (441287158793839 / 5000000000000000 : ℝ) (408676718403379 / 250000000000000000 : ℝ) (165055780646903 / 5000000000000000 : ℝ)
    (cell12849 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · have h := gap_lower (n := 12849) (a := (41296949407139 / 50000000000000 : ℝ)) (b := (40071510307 / 25000000000000 : ℝ)) (q := (2233711376839 / 100000000000000 : ℝ))
      (E := (cell12849 ⟨43, by decide⟩).energy) (xi := (165055780646903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12849 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12849]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12849])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12849) (a := (41296949407139 / 50000000000000 : ℝ)) (b := (40071510307 / 25000000000000 : ℝ)) (q := (2233711376839 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12849])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12849])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12849]

theorem cert12849_44 : CellCertificate 12849 (441287158793839 / 5000000000000000 : ℝ) (408676718403379 / 250000000000000000 : ℝ) (165055780646903 / 5000000000000000 : ℝ)
    (cell12849 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · have h := gap_lower (n := 12849) (a := (82560009767587 / 100000000000000 : ℝ)) (b := (40071510307 / 25000000000000 : ℝ)) (q := (1116857686853 / 50000000000000 : ℝ))
      (E := (cell12849 ⟨44, by decide⟩).energy) (xi := (165055780646903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12849 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12849]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12849])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12849) (a := (82560009767587 / 100000000000000 : ℝ)) (b := (40071510307 / 25000000000000 : ℝ)) (q := (1116857686853 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12849])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12849])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12849]

theorem cert12849_45 : CellCertificate 12849 (441287158793839 / 5000000000000000 : ℝ) (408676718403379 / 250000000000000000 : ℝ) (165055780646903 / 5000000000000000 : ℝ)
    (cell12849 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · have h := gap_lower (n := 12849) (a := (41263072091841 / 50000000000000 : ℝ)) (b := (40071510307 / 25000000000000 : ℝ)) (q := (446743872561 / 20000000000000 : ℝ))
      (E := (cell12849 ⟨45, by decide⟩).energy) (xi := (165055780646903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12849 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12849]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12849])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12849) (a := (41263072091841 / 50000000000000 : ℝ)) (b := (40071510307 / 25000000000000 : ℝ)) (q := (446743872561 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12849])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12849])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12849]

theorem cert12849_46 : CellCertificate 12849 (441287158793839 / 5000000000000000 : ℝ) (408676718403379 / 250000000000000000 : ℝ) (165055780646903 / 5000000000000000 : ℝ)
    (cell12849 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · have h := gap_lower (n := 12849) (a := (82492302033429 / 100000000000000 : ℝ)) (b := (40071510307 / 25000000000000 : ℝ)) (q := (111686170067 / 5000000000000 : ℝ))
      (E := (cell12849 ⟨46, by decide⟩).energy) (xi := (165055780646903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12849 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12849]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12849])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12849) (a := (82492302033429 / 100000000000000 : ℝ)) (b := (40071510307 / 25000000000000 : ℝ)) (q := (111686170067 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12849])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12849])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12849]

theorem cert12849_47 : CellCertificate 12849 (441287158793839 / 5000000000000000 : ℝ) (408676718403379 / 250000000000000000 : ℝ) (165055780646903 / 5000000000000000 : ℝ)
    (cell12849 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · have h := gap_lower (n := 12849) (a := (41229241643919 / 50000000000000 : ℝ)) (b := (40071510307 / 25000000000000 : ℝ)) (q := (139607960601 / 6250000000000 : ℝ))
      (E := (cell12849 ⟨47, by decide⟩).energy) (xi := (165055780646903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12849 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12849]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12849])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12849) (a := (41229241643919 / 50000000000000 : ℝ)) (b := (40071510307 / 25000000000000 : ℝ)) (q := (139607960601 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12849])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12849])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12849]

theorem cert12849_48 : CellCertificate 12849 (441287158793839 / 5000000000000000 : ℝ) (408676718403379 / 250000000000000000 : ℝ) (165055780646903 / 5000000000000000 : ℝ)
    (cell12849 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · have h := gap_lower (n := 12849) (a := (41212343959033 / 50000000000000 : ℝ)) (b := (40071510307 / 25000000000000 : ℝ)) (q := (279216422917 / 12500000000000 : ℝ))
      (E := (cell12849 ⟨48, by decide⟩).energy) (xi := (165055780646903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12849 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12849]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12849])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12849) (a := (41212343959033 / 50000000000000 : ℝ)) (b := (40071510307 / 25000000000000 : ℝ)) (q := (279216422917 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12849])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12849])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12849]

theorem cert12849_49 : CellCertificate 12849 (441287158793839 / 5000000000000000 : ℝ) (408676718403379 / 250000000000000000 : ℝ) (165055780646903 / 5000000000000000 : ℝ)
    (cell12849 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · have h := gap_lower (n := 12849) (a := (16478183179083 / 20000000000000 : ℝ)) (b := (40071510307 / 25000000000000 : ℝ)) (q := (446747076251 / 20000000000000 : ℝ))
      (E := (cell12849 ⟨49, by decide⟩).energy) (xi := (165055780646903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12849 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12849]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12849])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12849) (a := (16478183179083 / 20000000000000 : ℝ)) (b := (40071510307 / 25000000000000 : ℝ)) (q := (446747076251 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12849])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12849])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12849]

theorem cert12849_50 : CellCertificate 12849 (441287158793839 / 5000000000000000 : ℝ) (408676718403379 / 250000000000000000 : ℝ) (165055780646903 / 5000000000000000 : ℝ)
    (cell12849 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · have h := gap_lower (n := 12849) (a := (2573661474729 / 3125000000000 : ℝ)) (b := (40071510307 / 25000000000000 : ℝ)) (q := (2233739419819 / 100000000000000 : ℝ))
      (E := (cell12849 ⟨50, by decide⟩).energy) (xi := (165055780646903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12849 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12849]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12849])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12849) (a := (2573661474729 / 3125000000000 : ℝ)) (b := (40071510307 / 25000000000000 : ℝ)) (q := (2233739419819 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12849])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12849])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12849]

theorem cert12849_51 : CellCertificate 12849 (441287158793839 / 5000000000000000 : ℝ) (408676718403379 / 250000000000000000 : ℝ) (165055780646903 / 5000000000000000 : ℝ)
    (cell12849 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · have h := gap_lower (n := 12849) (a := (16464688355479 / 20000000000000 : ℝ)) (b := (40071510307 / 25000000000000 : ℝ)) (q := (223374343731 / 10000000000000 : ℝ))
      (E := (cell12849 ⟨51, by decide⟩).energy) (xi := (165055780646903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12849 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12849]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12849])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12849) (a := (16464688355479 / 20000000000000 : ℝ)) (b := (40071510307 / 25000000000000 : ℝ)) (q := (223374343731 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12849])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12849])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12849]

theorem cert12849_52 : CellCertificate 12849 (441287158793839 / 5000000000000000 : ℝ) (408676718403379 / 250000000000000000 : ℝ) (165055780646903 / 5000000000000000 : ℝ)
    (cell12849 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · have h := gap_lower (n := 12849) (a := (16457947925069 / 20000000000000 : ℝ)) (b := (40071510307 / 25000000000000 : ℝ)) (q := (558436857689 / 25000000000000 : ℝ))
      (E := (cell12849 ⟨52, by decide⟩).energy) (xi := (165055780646903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12849 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12849]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12849])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12849) (a := (16457947925069 / 20000000000000 : ℝ)) (b := (40071510307 / 25000000000000 : ℝ)) (q := (558436857689 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12849])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12849])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12849]

theorem cert12849_53 : CellCertificate 12849 (441287158793839 / 5000000000000000 : ℝ) (408676718403379 / 250000000000000000 : ℝ) (165055780646903 / 5000000000000000 : ℝ)
    (cell12849 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · have h := gap_lower (n := 12849) (a := (10282007588381 / 12500000000000 : ℝ)) (b := (40071510307 / 25000000000000 : ℝ)) (q := (2233751396971 / 100000000000000 : ℝ))
      (E := (cell12849 ⟨53, by decide⟩).energy) (xi := (165055780646903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12849 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12849]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12849])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12849) (a := (10282007588381 / 12500000000000 : ℝ)) (b := (40071510307 / 25000000000000 : ℝ)) (q := (2233751396971 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12849])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12849])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12849]

theorem cert12849_54 : CellCertificate 12849 (441287158793839 / 5000000000000000 : ℝ) (408676718403379 / 250000000000000000 : ℝ) (165055780646903 / 5000000000000000 : ℝ)
    (cell12849 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · have h := gap_lower (n := 12849) (a := (82222404994517 / 100000000000000 : ℝ)) (b := (40071510307 / 25000000000000 : ℝ)) (q := (1116877725369 / 50000000000000 : ℝ))
      (E := (cell12849 ⟨54, by decide⟩).energy) (xi := (165055780646903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12849 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12849]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12849])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12849) (a := (82222404994517 / 100000000000000 : ℝ)) (b := (40071510307 / 25000000000000 : ℝ)) (q := (1116877725369 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12849])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12849])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12849]

theorem cert12849_55 : CellCertificate 12849 (441287158793839 / 5000000000000000 : ℝ) (408676718403379 / 250000000000000000 : ℝ) (165055780646903 / 5000000000000000 : ℝ)
    (cell12849 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · have h := gap_lower (n := 12849) (a := (642099784843 / 781250000000 : ℝ)) (b := (40071510307 / 25000000000000 : ℝ)) (q := (69804983449 / 3125000000000 : ℝ))
      (E := (cell12849 ⟨55, by decide⟩).energy) (xi := (165055780646903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12849 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12849]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12849])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12849) (a := (642099784843 / 781250000000 : ℝ)) (b := (40071510307 / 25000000000000 : ℝ)) (q := (69804983449 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12849])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12849])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12849]

theorem cert12849_56 : CellCertificate 12849 (441287158793839 / 5000000000000000 : ℝ) (408676718403379 / 250000000000000000 : ℝ) (165055780646903 / 5000000000000000 : ℝ)
    (cell12849 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · have h := gap_lower (n := 12849) (a := (82155163075497 / 100000000000000 : ℝ)) (b := (40071510307 / 25000000000000 : ℝ)) (q := (44675269041 / 2000000000000 : ℝ))
      (E := (cell12849 ⟨56, by decide⟩).energy) (xi := (165055780646903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12849 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12849]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12849])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12849) (a := (82155163075497 / 100000000000000 : ℝ)) (b := (40071510307 / 25000000000000 : ℝ)) (q := (44675269041 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12849])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12849])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12849]

theorem cert12849_57 : CellCertificate 12849 (441287158793839 / 5000000000000000 : ℝ) (408676718403379 / 250000000000000000 : ℝ) (165055780646903 / 5000000000000000 : ℝ)
    (cell12849 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · have h := gap_lower (n := 12849) (a := (3284863072549 / 4000000000000 : ℝ)) (b := (40071510307 / 25000000000000 : ℝ)) (q := (89350698037 / 4000000000000 : ℝ))
      (E := (cell12849 ⟨57, by decide⟩).energy) (xi := (165055780646903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12849 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12849]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12849])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12849) (a := (3284863072549 / 4000000000000 : ℝ)) (b := (40071510307 / 25000000000000 : ℝ)) (q := (89350698037 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12849])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12849])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12849]

theorem cert12849_58 : CellCertificate 12849 (441287158793839 / 5000000000000000 : ℝ) (408676718403379 / 250000000000000000 : ℝ) (165055780646903 / 5000000000000000 : ℝ)
    (cell12849 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · have h := gap_lower (n := 12849) (a := (16417602729431 / 20000000000000 : ℝ)) (b := (40071510307 / 25000000000000 : ℝ)) (q := (1116885731419 / 50000000000000 : ℝ))
      (E := (cell12849 ⟨58, by decide⟩).energy) (xi := (165055780646903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12849 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12849]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12849])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12849) (a := (16417602729431 / 20000000000000 : ℝ)) (b := (40071510307 / 25000000000000 : ℝ)) (q := (1116885731419 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12849])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12849])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12849]

theorem cert12849_59 : CellCertificate 12849 (441287158793839 / 5000000000000000 : ℝ) (408676718403379 / 250000000000000000 : ℝ) (165055780646903 / 5000000000000000 : ℝ)
    (cell12849 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · have h := gap_lower (n := 12849) (a := (82054473548487 / 100000000000000 : ℝ)) (b := (40071510307 / 25000000000000 : ℝ)) (q := (558443870857 / 25000000000000 : ℝ))
      (E := (cell12849 ⟨59, by decide⟩).energy) (xi := (165055780646903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12849 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12849]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12849])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12849) (a := (82054473548487 / 100000000000000 : ℝ)) (b := (40071510307 / 25000000000000 : ℝ)) (q := (558443870857 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12849])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12849])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12849]

end BstLean.Part268
