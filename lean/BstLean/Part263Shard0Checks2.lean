import BstLean.Part263Shard0Checks1

/-! Twenty scalar cells per dimension in a 25-dimension shard. -/
namespace BstLean.Part263
open Real

theorem cert12225_40 : CellCertificate 12225 (450227846321489 / 5000000000000000 : ℝ) (1718175626812061 / 1000000000000000000 : ℝ) (347397722670537 / 10000000000000000 : ℝ)
    (cell12225 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · have h := gap_lower (n := 12225) (a := (20674366766843 / 25000000000000 : ℝ)) (b := (168573401311 / 100000000000000 : ℝ)) (q := (463047393899 / 20000000000000 : ℝ))
      (E := (cell12225 ⟨40, by decide⟩).energy) (xi := (347397722670537 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12225 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12225]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12225])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12225) (a := (20674366766843 / 25000000000000 : ℝ)) (b := (168573401311 / 100000000000000 : ℝ)) (q := (463047393899 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12225])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12225])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12225]

theorem cert12225_41 : CellCertificate 12225 (450227846321489 / 5000000000000000 : ℝ) (1718175626812061 / 1000000000000000000 : ℝ) (347397722670537 / 10000000000000000 : ℝ)
    (cell12225 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · have h := gap_lower (n := 12225) (a := (8266331471461 / 10000000000000 : ℝ)) (b := (168573401311 / 100000000000000 : ℝ)) (q := (2315240995987 / 100000000000000 : ℝ))
      (E := (cell12225 ⟨41, by decide⟩).energy) (xi := (347397722670537 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12225 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12225]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12225])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12225) (a := (8266331471461 / 10000000000000 : ℝ)) (b := (168573401311 / 100000000000000 : ℝ)) (q := (2315240995987 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12225])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12225])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12225]

theorem cert12225_42 : CellCertificate 12225 (450227846321489 / 5000000000000000 : ℝ) (1718175626812061 / 1000000000000000000 : ℝ) (347397722670537 / 10000000000000000 : ℝ)
    (cell12225 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · have h := gap_lower (n := 12225) (a := (41314593089629 / 50000000000000 : ℝ)) (b := (168573401311 / 100000000000000 : ℝ)) (q := (46304899679 / 2000000000000 : ℝ))
      (E := (cell12225 ⟨42, by decide⟩).energy) (xi := (347397722670537 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12225 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12225]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12225])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12225) (a := (41314593089629 / 50000000000000 : ℝ)) (b := (168573401311 / 100000000000000 : ℝ)) (q := (46304899679 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12225])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12225])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12225]

theorem cert12225_43 : CellCertificate 12225 (450227846321489 / 5000000000000000 : ℝ) (1718175626812061 / 1000000000000000000 : ℝ) (347397722670537 / 10000000000000000 : ℝ)
    (cell12225 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · have h := gap_lower (n := 12225) (a := (82595081431251 / 100000000000000 : ℝ)) (b := (168573401311 / 100000000000000 : ℝ)) (q := (36175765501 / 1562500000000 : ℝ))
      (E := (cell12225 ⟨43, by decide⟩).energy) (xi := (347397722670537 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12225 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12225]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12225])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12225) (a := (82595081431251 / 100000000000000 : ℝ)) (b := (168573401311 / 100000000000000 : ℝ)) (q := (36175765501 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12225])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12225])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12225]

theorem cert12225_44 : CellCertificate 12225 (450227846321489 / 5000000000000000 : ℝ) (1718175626812061 / 1000000000000000000 : ℝ) (347397722670537 / 10000000000000000 : ℝ)
    (cell12225 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · have h := gap_lower (n := 12225) (a := (20640250110169 / 25000000000000 : ℝ)) (b := (168573401311 / 100000000000000 : ℝ)) (q := (2315252961293 / 100000000000000 : ℝ))
      (E := (cell12225 ⟨44, by decide⟩).energy) (xi := (347397722670537 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12225 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12225]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12225])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12225) (a := (20640250110169 / 25000000000000 : ℝ)) (b := (168573401311 / 100000000000000 : ℝ)) (q := (2315252961293 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12225])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12225])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12225]

theorem cert12225_45 : CellCertificate 12225 (450227846321489 / 5000000000000000 : ℝ) (1718175626812061 / 1000000000000000000 : ℝ) (347397722670537 / 10000000000000000 : ℝ)
    (cell12225 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · have h := gap_lower (n := 12225) (a := (82526943177773 / 100000000000000 : ℝ)) (b := (168573401311 / 100000000000000 : ℝ)) (q := (1157628474961 / 50000000000000 : ℝ))
      (E := (cell12225 ⟨45, by decide⟩).energy) (xi := (347397722670537 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12225 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12225]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12225])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12225) (a := (82526943177773 / 100000000000000 : ℝ)) (b := (168573401311 / 100000000000000 : ℝ)) (q := (1157628474961 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12225])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12225])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12225]

theorem cert12225_46 : CellCertificate 12225 (450227846321489 / 5000000000000000 : ℝ) (1718175626812061 / 1000000000000000000 : ℝ) (347397722670537 / 10000000000000000 : ℝ)
    (cell12225 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · have h := gap_lower (n := 12225) (a := (20623227403233 / 25000000000000 : ℝ)) (b := (168573401311 / 100000000000000 : ℝ)) (q := (2315260957269 / 100000000000000 : ℝ))
      (E := (cell12225 ⟨46, by decide⟩).energy) (xi := (347397722670537 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12225 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12225]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12225])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12225) (a := (20623227403233 / 25000000000000 : ℝ)) (b := (168573401311 / 100000000000000 : ℝ)) (q := (2315260957269 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12225])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12225])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12225]

theorem cert12225_47 : CellCertificate 12225 (450227846321489 / 5000000000000000 : ℝ) (1718175626812061 / 1000000000000000000 : ℝ) (347397722670537 / 10000000000000000 : ℝ)
    (cell12225 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · have h := gap_lower (n := 12225) (a := (20614724929173 / 25000000000000 : ℝ)) (b := (168573401311 / 100000000000000 : ℝ)) (q := (1157632461787 / 50000000000000 : ℝ))
      (E := (cell12225 ⟨47, by decide⟩).energy) (xi := (347397722670537 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12225 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12225]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12225])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12225) (a := (20614724929173 / 25000000000000 : ℝ)) (b := (168573401311 / 100000000000000 : ℝ)) (q := (1157632461787 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12225])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12225])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12225]

theorem cert12225_48 : CellCertificate 12225 (450227846321489 / 5000000000000000 : ℝ) (1718175626812061 / 1000000000000000000 : ℝ) (347397722670537 / 10000000000000000 : ℝ)
    (cell12225 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · have h := gap_lower (n := 12225) (a := (4121245672987 / 5000000000000 : ℝ)) (b := (168573401311 / 100000000000000 : ℝ)) (q := (144704310339 / 6250000000000 : ℝ))
      (E := (cell12225 ⟨48, by decide⟩).energy) (xi := (347397722670537 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12225 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12225]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12225])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12225) (a := (4121245672987 / 5000000000000 : ℝ)) (b := (168573401311 / 100000000000000 : ℝ)) (q := (144704310339 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12225])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12225])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12225]

theorem cert12225_49 : CellCertificate 12225 (450227846321489 / 5000000000000000 : ℝ) (1718175626812061 / 1000000000000000000 : ℝ) (347397722670537 / 10000000000000000 : ℝ)
    (cell12225 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · have h := gap_lower (n := 12225) (a := (82390950812913 / 100000000000000 : ℝ)) (b := (168573401311 / 100000000000000 : ℝ)) (q := (1157636452413 / 50000000000000 : ℝ))
      (E := (cell12225 ⟨49, by decide⟩).energy) (xi := (347397722670537 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12225 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12225]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12225])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12225) (a := (82390950812913 / 100000000000000 : ℝ)) (b := (168573401311 / 100000000000000 : ℝ)) (q := (1157636452413 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12225])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12225])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12225]

theorem cert12225_50 : CellCertificate 12225 (450227846321489 / 5000000000000000 : ℝ) (1718175626812061 / 1000000000000000000 : ℝ) (347397722670537 / 10000000000000000 : ℝ)
    (cell12225 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · have h := gap_lower (n := 12225) (a := (10294626468399 / 12500000000000 : ℝ)) (b := (168573401311 / 100000000000000 : ℝ)) (q := (463055383379 / 20000000000000 : ℝ))
      (E := (cell12225 ⟨50, by decide⟩).energy) (xi := (347397722670537 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12225 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12225]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12225])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12225) (a := (10294626468399 / 12500000000000 : ℝ)) (b := (168573401311 / 100000000000000 : ℝ)) (q := (463055383379 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12225])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12225])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12225]

theorem cert12225_51 : CellCertificate 12225 (450227846321489 / 5000000000000000 : ℝ) (1718175626812061 / 1000000000000000000 : ℝ) (347397722670537 / 10000000000000000 : ℝ)
    (cell12225 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · have h := gap_lower (n := 12225) (a := (16464619246741 / 20000000000000 : ℝ)) (b := (168573401311 / 100000000000000 : ℝ)) (q := (2315280940983 / 100000000000000 : ℝ))
      (E := (cell12225 ⟨51, by decide⟩).energy) (xi := (347397722670537 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12225 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12225]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12225])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12225) (a := (16464619246741 / 20000000000000 : ℝ)) (b := (168573401311 / 100000000000000 : ℝ)) (q := (2315280940983 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12225])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12225])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12225]

theorem cert12225_52 : CellCertificate 12225 (450227846321489 / 5000000000000000 : ℝ) (1718175626812061 / 1000000000000000000 : ℝ) (347397722670537 / 10000000000000000 : ℝ)
    (cell12225 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · have h := gap_lower (n := 12225) (a := (5143075265233 / 6250000000000 : ℝ)) (b := (168573401311 / 100000000000000 : ℝ)) (q := (231528491613 / 10000000000000 : ℝ))
      (E := (cell12225 ⟨52, by decide⟩).energy) (xi := (347397722670537 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12225 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12225]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12225])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12225) (a := (5143075265233 / 6250000000000 : ℝ)) (b := (168573401311 / 100000000000000 : ℝ)) (q := (231528491613 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12225])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12225])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12225]

theorem cert12225_53 : CellCertificate 12225 (450227846321489 / 5000000000000000 : ℝ) (1718175626812061 / 1000000000000000000 : ℝ) (347397722670537 / 10000000000000000 : ℝ)
    (cell12225 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · have h := gap_lower (n := 12225) (a := (20563833937169 / 25000000000000 : ℝ)) (b := (168573401311 / 100000000000000 : ℝ)) (q := (463057779817 / 20000000000000 : ℝ))
      (E := (cell12225 ⟨53, by decide⟩).energy) (xi := (347397722670537 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12225 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12225]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12225])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12225) (a := (20563833937169 / 25000000000000 : ℝ)) (b := (168573401311 / 100000000000000 : ℝ)) (q := (463057779817 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12225])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12225])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12225]

theorem cert12225_54 : CellCertificate 12225 (450227846321489 / 5000000000000000 : ℝ) (1718175626812061 / 1000000000000000000 : ℝ) (347397722670537 / 10000000000000000 : ℝ)
    (cell12225 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · have h := gap_lower (n := 12225) (a := (82221490720113 / 100000000000000 : ℝ)) (b := (168573401311 / 100000000000000 : ℝ)) (q := (463058577489 / 20000000000000 : ℝ))
      (E := (cell12225 ⟨54, by decide⟩).energy) (xi := (347397722670537 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12225 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12225]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12225])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12225) (a := (82221490720113 / 100000000000000 : ℝ)) (b := (168573401311 / 100000000000000 : ℝ)) (q := (463058577489 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12225])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12225])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12225]

theorem cert12225_55 : CellCertificate 12225 (450227846321489 / 5000000000000000 : ℝ) (1718175626812061 / 1000000000000000000 : ℝ) (347397722670537 / 10000000000000000 : ℝ)
    (cell12225 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · have h := gap_lower (n := 12225) (a := (41093834564871 / 50000000000000 : ℝ)) (b := (168573401311 / 100000000000000 : ℝ)) (q := (2315296878597 / 100000000000000 : ℝ))
      (E := (cell12225 ⟨55, by decide⟩).energy) (xi := (347397722670537 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12225 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12225]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12225])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12225) (a := (41093834564871 / 50000000000000 : ℝ)) (b := (168573401311 / 100000000000000 : ℝ)) (q := (2315296878597 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12225])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12225])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12225]

theorem cert12225_56 : CellCertificate 12225 (450227846321489 / 5000000000000000 : ℝ) (1718175626812061 / 1000000000000000000 : ℝ) (347397722670537 / 10000000000000000 : ℝ)
    (cell12225 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · have h := gap_lower (n := 12225) (a := (82153870949409 / 100000000000000 : ℝ)) (b := (168573401311 / 100000000000000 : ℝ)) (q := (1157650464397 / 50000000000000 : ℝ))
      (E := (cell12225 ⟨56, by decide⟩).energy) (xi := (347397722670537 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12225 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12225]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12225])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12225) (a := (82153870949409 / 100000000000000 : ℝ)) (b := (168573401311 / 100000000000000 : ℝ)) (q := (1157650464397 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12225])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12225])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12225]

theorem cert12225_57 : CellCertificate 12225 (450227846321489 / 5000000000000000 : ℝ) (1718175626812061 / 1000000000000000000 : ℝ) (347397722670537 / 10000000000000000 : ℝ)
    (cell12225 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · have h := gap_lower (n := 12225) (a := (82120096151101 / 100000000000000 : ℝ)) (b := (168573401311 / 100000000000000 : ℝ)) (q := (578826229219 / 25000000000000 : ℝ))
      (E := (cell12225 ⟨57, by decide⟩).energy) (xi := (347397722670537 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12225 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12225]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12225])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12225) (a := (82120096151101 / 100000000000000 : ℝ)) (b := (168573401311 / 100000000000000 : ℝ)) (q := (578826229219 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12225])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12225])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12225]

theorem cert12225_58 : CellCertificate 12225 (450227846321489 / 5000000000000000 : ℝ) (1718175626812061 / 1000000000000000000 : ℝ) (347397722670537 / 10000000000000000 : ℝ)
    (cell12225 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · have h := gap_lower (n := 12225) (a := (16417268941389 / 20000000000000 : ℝ)) (b := (168573401311 / 100000000000000 : ℝ)) (q := (578827224663 / 25000000000000 : ℝ))
      (E := (cell12225 ⟨58, by decide⟩).energy) (xi := (347397722670537 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12225 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12225]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12225])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12225) (a := (16417268941389 / 20000000000000 : ℝ)) (b := (168573401311 / 100000000000000 : ℝ)) (q := (578827224663 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12225])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12225])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12225]

theorem cert12225_59 : CellCertificate 12225 (450227846321489 / 5000000000000000 : ℝ) (1718175626812061 / 1000000000000000000 : ℝ) (347397722670537 / 10000000000000000 : ℝ)
    (cell12225 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · have h := gap_lower (n := 12225) (a := (82052616589209 / 100000000000000 : ℝ)) (b := (168573401311 / 100000000000000 : ℝ)) (q := (231531287067 / 10000000000000 : ℝ))
      (E := (cell12225 ⟨59, by decide⟩).energy) (xi := (347397722670537 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12225 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12225]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12225])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12225) (a := (82052616589209 / 100000000000000 : ℝ)) (b := (168573401311 / 100000000000000 : ℝ)) (q := (231531287067 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12225])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12225])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12225]

theorem cert12226_40 : CellCertificate 12226 (450212816205331 / 5000000000000000 : ℝ) (343607008849341 / 200000000000000000 : ℝ) (347368541485789 / 10000000000000000 : ℝ)
    (cell12226 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · have h := gap_lower (n := 12226) (a := (2584295748501 / 3125000000000 : ℝ)) (b := (168559427229 / 100000000000000 : ℝ)) (q := (46301750631 / 2000000000000 : ℝ))
      (E := (cell12226 ⟨40, by decide⟩).energy) (xi := (347368541485789 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12226 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12226]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12226])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12226) (a := (2584295748501 / 3125000000000 : ℝ)) (b := (168559427229 / 100000000000000 : ℝ)) (q := (46301750631 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12226])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12226])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12226]

theorem cert12226_41 : CellCertificate 12226 (450212816205331 / 5000000000000000 : ℝ) (343607008849341 / 200000000000000000 : ℝ) (347368541485789 / 10000000000000000 : ℝ)
    (cell12226 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · have h := gap_lower (n := 12226) (a := (82663311920223 / 100000000000000 : ℝ)) (b := (168559427229 / 100000000000000 : ℝ)) (q := (463018304527 / 20000000000000 : ℝ))
      (E := (cell12226 ⟨41, by decide⟩).energy) (xi := (347368541485789 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12226 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12226]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12226])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12226) (a := (82663311920223 / 100000000000000 : ℝ)) (b := (168559427229 / 100000000000000 : ℝ)) (q := (463018304527 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12226])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12226])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12226]

theorem cert12226_42 : CellCertificate 12226 (450212816205331 / 5000000000000000 : ℝ) (343607008849341 / 200000000000000000 : ℝ) (347368541485789 / 10000000000000000 : ℝ)
    (cell12226 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · have h := gap_lower (n := 12226) (a := (41314591852689 / 50000000000000 : ℝ)) (b := (168559427229 / 100000000000000 : ℝ)) (q := (1157547767329 / 50000000000000 : ℝ))
      (E := (cell12226 ⟨42, by decide⟩).energy) (xi := (347368541485789 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12226 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12226]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12226])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12226) (a := (41314591852689 / 50000000000000 : ℝ)) (b := (168559427229 / 100000000000000 : ℝ)) (q := (1157547767329 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12226])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12226])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12226]

theorem cert12226_43 : CellCertificate 12226 (450212816205331 / 5000000000000000 : ℝ) (343607008849341 / 200000000000000000 : ℝ) (347368541485789 / 10000000000000000 : ℝ)
    (cell12226 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · have h := gap_lower (n := 12226) (a := (41297539638717 / 50000000000000 : ℝ)) (b := (168559427229 / 100000000000000 : ℝ)) (q := (2315099508829 / 100000000000000 : ℝ))
      (E := (cell12226 ⟨43, by decide⟩).energy) (xi := (347368541485789 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12226 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12226]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12226])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12226) (a := (41297539638717 / 50000000000000 : ℝ)) (b := (168559427229 / 100000000000000 : ℝ)) (q := (2315099508829 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12226])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12226])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12226]

theorem cert12226_44 : CellCertificate 12226 (450212816205331 / 5000000000000000 : ℝ) (343607008849341 / 200000000000000000 : ℝ) (347368541485789 / 10000000000000000 : ℝ)
    (cell12226 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · have h := gap_lower (n := 12226) (a := (1032012482581 / 1250000000000 : ℝ)) (b := (168559427229 / 100000000000000 : ℝ)) (q := (1157551751813 / 50000000000000 : ℝ))
      (E := (cell12226 ⟨44, by decide⟩).energy) (xi := (347368541485789 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12226 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12226]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12226])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12226) (a := (1032012482581 / 1250000000000 : ℝ)) (b := (168559427229 / 100000000000000 : ℝ)) (q := (1157551751813 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12226])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12226])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12226]

theorem cert12226_45 : CellCertificate 12226 (450212816205331 / 5000000000000000 : ℝ) (343607008849341 / 200000000000000000 : ℝ) (347368541485789 / 10000000000000000 : ℝ)
    (cell12226 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · have h := gap_lower (n := 12226) (a := (16505388332551 / 20000000000000 : ℝ)) (b := (168559427229 / 100000000000000 : ℝ)) (q := (2315107518589 / 100000000000000 : ℝ))
      (E := (cell12226 ⟨45, by decide⟩).energy) (xi := (347368541485789 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12226 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12226]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12226])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12226) (a := (16505388332551 / 20000000000000 : ℝ)) (b := (168559427229 / 100000000000000 : ℝ)) (q := (2315107518589 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12226])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12226])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12226]

theorem cert12226_46 : CellCertificate 12226 (450212816205331 / 5000000000000000 : ℝ) (343607008849341 / 200000000000000000 : ℝ) (347368541485789 / 10000000000000000 : ℝ)
    (cell12226 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · have h := gap_lower (n := 12226) (a := (82492908416651 / 100000000000000 : ℝ)) (b := (168559427229 / 100000000000000 : ℝ)) (q := (1157555747097 / 50000000000000 : ℝ))
      (E := (cell12226 ⟨46, by decide⟩).energy) (xi := (347368541485789 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12226 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12226]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12226])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12226) (a := (82492908416651 / 100000000000000 : ℝ)) (b := (168559427229 / 100000000000000 : ℝ)) (q := (1157555747097 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12226])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12226])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12226]

theorem cert12226_47 : CellCertificate 12226 (450212816205331 / 5000000000000000 : ℝ) (343607008849341 / 200000000000000000 : ℝ) (347368541485789 / 10000000000000000 : ℝ)
    (cell12226 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · have h := gap_lower (n := 12226) (a := (82458898838707 / 100000000000000 : ℝ)) (b := (168559427229 / 100000000000000 : ℝ)) (q := (144694718021 / 6250000000000 : ℝ))
      (E := (cell12226 ⟨47, by decide⟩).energy) (xi := (347368541485789 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12226 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12226]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12226])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12226) (a := (82458898838707 / 100000000000000 : ℝ)) (b := (168559427229 / 100000000000000 : ℝ)) (q := (144694718021 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12226])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12226])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12226]

theorem cert12226_48 : CellCertificate 12226 (450212816205331 / 5000000000000000 : ℝ) (343607008849341 / 200000000000000000 : ℝ) (347368541485789 / 10000000000000000 : ℝ)
    (cell12226 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · have h := gap_lower (n := 12226) (a := (82424912899611 / 100000000000000 : ℝ)) (b := (168559427229 / 100000000000000 : ℝ)) (q := (23151194999 / 1000000000000 : ℝ))
      (E := (cell12226 ⟨48, by decide⟩).energy) (xi := (347368541485789 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12226 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12226]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12226])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12226) (a := (82424912899611 / 100000000000000 : ℝ)) (b := (168559427229 / 100000000000000 : ℝ)) (q := (23151194999 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12226])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12226])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12226]

theorem cert12226_49 : CellCertificate 12226 (450212816205331 / 5000000000000000 : ℝ) (343607008849341 / 200000000000000000 : ℝ) (347368541485789 / 10000000000000000 : ℝ)
    (cell12226 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · have h := gap_lower (n := 12226) (a := (411954752851 / 500000000000 : ℝ)) (b := (168559427229 / 100000000000000 : ℝ)) (q := (1157561734321 / 50000000000000 : ℝ))
      (E := (cell12226 ⟨49, by decide⟩).energy) (xi := (347368541485789 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12226 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12226]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12226])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12226) (a := (411954752851 / 500000000000 : ℝ)) (b := (168559427229 / 100000000000000 : ℝ)) (q := (1157561734321 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12226])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12226])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12226]

theorem cert12226_50 : CellCertificate 12226 (450212816205331 / 5000000000000000 : ℝ) (343607008849341 / 200000000000000000 : ℝ) (347368541485789 / 10000000000000000 : ℝ)
    (cell12226 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · have h := gap_lower (n := 12226) (a := (41178505910729 / 50000000000000 : ℝ)) (b := (168559427229 / 100000000000000 : ℝ)) (q := (2315127510811 / 100000000000000 : ℝ))
      (E := (cell12226 ⟨50, by decide⟩).energy) (xi := (347368541485789 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12226 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12226]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12226])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12226) (a := (41178505910729 / 50000000000000 : ℝ)) (b := (168559427229 / 100000000000000 : ℝ)) (q := (2315127510811 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12226])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12226])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12226]

theorem cert12226_51 : CellCertificate 12226 (450212816205331 / 5000000000000000 : ℝ) (343607008849341 / 200000000000000000 : ℝ) (347368541485789 / 10000000000000000 : ℝ)
    (cell12226 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · have h := gap_lower (n := 12226) (a := (82323096624513 / 100000000000000 : ℝ)) (b := (168559427229 / 100000000000000 : ℝ)) (q := (2315131506801 / 100000000000000 : ℝ))
      (E := (cell12226 ⟨51, by decide⟩).energy) (xi := (347368541485789 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12226 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12226]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12226])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12226) (a := (82323096624513 / 100000000000000 : ℝ)) (b := (168559427229 / 100000000000000 : ℝ)) (q := (2315131506801 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12226])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12226])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12226]

theorem cert12226_52 : CellCertificate 12226 (450212816205331 / 5000000000000000 : ℝ) (343607008849341 / 200000000000000000 : ℝ) (347368541485789 / 10000000000000000 : ℝ)
    (cell12226 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · have h := gap_lower (n := 12226) (a := (82289204950639 / 100000000000000 : ℝ)) (b := (168559427229 / 100000000000000 : ℝ)) (q := (1157567727283 / 50000000000000 : ℝ))
      (E := (cell12226 ⟨52, by decide⟩).energy) (xi := (347368541485789 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12226 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12226]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12226])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12226) (a := (82289204950639 / 100000000000000 : ℝ)) (b := (168559427229 / 100000000000000 : ℝ)) (q := (1157567727283 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12226])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12226])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12226]

theorem cert12226_53 : CellCertificate 12226 (450212816205331 / 5000000000000000 : ℝ) (343607008849341 / 200000000000000000 : ℝ) (347368541485789 / 10000000000000000 : ℝ)
    (cell12226 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · have h := gap_lower (n := 12226) (a := (82255336771257 / 100000000000000 : ℝ)) (b := (168559427229 / 100000000000000 : ℝ)) (q := (578784867463 / 25000000000000 : ℝ))
      (E := (cell12226 ⟨53, by decide⟩).energy) (xi := (347368541485789 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12226 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12226]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12226])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12226) (a := (82255336771257 / 100000000000000 : ℝ)) (b := (168559427229 / 100000000000000 : ℝ)) (q := (578784867463 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12226])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12226])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12226]

theorem cert12226_54 : CellCertificate 12226 (450212816205331 / 5000000000000000 : ℝ) (343607008849341 / 200000000000000000 : ℝ) (347368541485789 / 10000000000000000 : ℝ)
    (cell12226 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · have h := gap_lower (n := 12226) (a := (41110746028963 / 50000000000000 : ℝ)) (b := (168559427229 / 100000000000000 : ℝ)) (q := (289392936413 / 12500000000000 : ℝ))
      (E := (cell12226 ⟨54, by decide⟩).energy) (xi := (347368541485789 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12226 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12226]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12226])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12226) (a := (41110746028963 / 50000000000000 : ℝ)) (b := (168559427229 / 100000000000000 : ℝ)) (q := (289392936413 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12226])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12226])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12226]

theorem cert12226_55 : CellCertificate 12226 (450212816205331 / 5000000000000000 : ℝ) (343607008849341 / 200000000000000000 : ℝ) (347368541485789 / 10000000000000000 : ℝ)
    (cell12226 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · have h := gap_lower (n := 12226) (a := (82187670782353 / 100000000000000 : ℝ)) (b := (168559427229 / 100000000000000 : ℝ)) (q := (1157573728627 / 50000000000000 : ℝ))
      (E := (cell12226 ⟨55, by decide⟩).energy) (xi := (347368541485789 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12226 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12226]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12226])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12226) (a := (82187670782353 / 100000000000000 : ℝ)) (b := (168559427229 / 100000000000000 : ℝ)) (q := (1157573728627 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12226])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12226])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12226]

theorem cert12226_56 : CellCertificate 12226 (450212816205331 / 5000000000000000 : ℝ) (343607008849341 / 200000000000000000 : ℝ) (347368541485789 / 10000000000000000 : ℝ)
    (cell12226 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · have h := gap_lower (n := 12226) (a := (16430774583277 / 20000000000000 : ℝ)) (b := (168559427229 / 100000000000000 : ℝ)) (q := (2315151482957 / 100000000000000 : ℝ))
      (E := (cell12226 ⟨56, by decide⟩).energy) (xi := (347368541485789 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12226 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12226]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12226])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12226) (a := (16430774583277 / 20000000000000 : ℝ)) (b := (168559427229 / 100000000000000 : ℝ)) (q := (2315151482957 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12226])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12226])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12226]

theorem cert12226_57 : CellCertificate 12226 (450212816205331 / 5000000000000000 : ℝ) (343607008849341 / 200000000000000000 : ℝ) (347368541485789 / 10000000000000000 : ℝ)
    (cell12226 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · have h := gap_lower (n := 12226) (a := (82120098432009 / 100000000000000 : ℝ)) (b := (168559427229 / 100000000000000 : ℝ)) (q := (463031089451 / 20000000000000 : ℝ))
      (E := (cell12226 ⟨57, by decide⟩).energy) (xi := (347368541485789 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12226 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12226]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12226])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12226) (a := (82120098432009 / 100000000000000 : ℝ)) (b := (168559427229 / 100000000000000 : ℝ)) (q := (463031089451 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12226])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12226])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12226]

theorem cert12226_58 : CellCertificate 12226 (450212816205331 / 5000000000000000 : ℝ) (343607008849341 / 200000000000000000 : ℝ) (347368541485789 / 10000000000000000 : ℝ)
    (cell12226 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · have h := gap_lower (n := 12226) (a := (10260793412669 / 12500000000000 : ℝ)) (b := (168559427229 / 100000000000000 : ℝ)) (q := (1157579732539 / 50000000000000 : ℝ))
      (E := (cell12226 ⟨58, by decide⟩).energy) (xi := (347368541485789 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12226 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12226]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12226])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12226) (a := (10260793412669 / 12500000000000 : ℝ)) (b := (168559427229 / 100000000000000 : ℝ)) (q := (1157579732539 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12226])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12226])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12226]

theorem cert12226_59 : CellCertificate 12226 (450212816205331 / 5000000000000000 : ℝ) (343607008849341 / 200000000000000000 : ℝ) (347368541485789 / 10000000000000000 : ℝ)
    (cell12226 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · have h := gap_lower (n := 12226) (a := (20513154874171 / 25000000000000 : ℝ)) (b := (168559427229 / 100000000000000 : ℝ)) (q := (1157581736949 / 50000000000000 : ℝ))
      (E := (cell12226 ⟨59, by decide⟩).energy) (xi := (347368541485789 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12226 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12226]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12226])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12226) (a := (20513154874171 / 25000000000000 : ℝ)) (b := (168559427229 / 100000000000000 : ℝ)) (q := (1157581736949 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12226])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12226])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12226]

theorem cert12227_40 : CellCertificate 12227 (450197788458709 / 5000000000000000 : ℝ) (171789448468463 / 100000000000000000 : ℝ) (69467873066693 / 2000000000000000 : ℝ)
    (cell12227 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · have h := gap_lower (n := 12227) (a := (82697460837699 / 100000000000000 : ℝ)) (b := (33709091099 / 20000000000000 : ℝ)) (q := (1157469103661 / 50000000000000 : ℝ))
      (E := (cell12227 ⟨40, by decide⟩).energy) (xi := (69467873066693 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12227 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12227]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12227])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12227) (a := (82697460837699 / 100000000000000 : ℝ)) (b := (33709091099 / 20000000000000 : ℝ)) (q := (1157469103661 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12227])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12227])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12227]

theorem cert12227_41 : CellCertificate 12227 (450197788458709 / 5000000000000000 : ℝ) (171789448468463 / 100000000000000000 : ℝ) (69467873066693 / 2000000000000000 : ℝ)
    (cell12227 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · have h := gap_lower (n := 12227) (a := (82663309126801 / 100000000000000 : ℝ)) (b := (33709091099 / 20000000000000 : ℝ)) (q := (2314942163089 / 100000000000000 : ℝ))
      (E := (cell12227 ⟨41, by decide⟩).energy) (xi := (69467873066693 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12227 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12227]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12227])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12227) (a := (82663309126801 / 100000000000000 : ℝ)) (b := (33709091099 / 20000000000000 : ℝ)) (q := (2314942163089 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12227])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12227])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12227]

theorem cert12227_42 : CellCertificate 12227 (450197788458709 / 5000000000000000 : ℝ) (171789448468463 / 100000000000000000 : ℝ) (69467873066693 / 2000000000000000 : ℝ)
    (cell12227 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · have h := gap_lower (n := 12227) (a := (82629181232423 / 100000000000000 : ℝ)) (b := (33709091099 / 20000000000000 : ℝ)) (q := (462989228103 / 20000000000000 : ℝ))
      (E := (cell12227 ⟨42, by decide⟩).energy) (xi := (69467873066693 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12227 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12227]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12227])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12227) (a := (82629181232423 / 100000000000000 : ℝ)) (b := (33709091099 / 20000000000000 : ℝ)) (q := (462989228103 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12227])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12227])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12227]

theorem cert12227_43 : CellCertificate 12227 (450197788458709 / 5000000000000000 : ℝ) (171789448468463 / 100000000000000000 : ℝ) (69467873066693 / 2000000000000000 : ℝ)
    (cell12227 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · have h := gap_lower (n := 12227) (a := (82595077124503 / 100000000000000 : ℝ)) (b := (33709091099 / 20000000000000 : ℝ)) (q := (289368767447 / 12500000000000 : ℝ))
      (E := (cell12227 ⟨43, by decide⟩).energy) (xi := (69467873066693 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12227 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12227]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12227])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12227) (a := (82595077124503 / 100000000000000 : ℝ)) (b := (33709091099 / 20000000000000 : ℝ)) (q := (289368767447 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12227])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12227])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12227]

theorem cert12227_44 : CellCertificate 12227 (450197788458709 / 5000000000000000 : ℝ) (171789448468463 / 100000000000000000 : ℝ) (69467873066693 / 2000000000000000 : ℝ)
    (cell12227 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · have h := gap_lower (n := 12227) (a := (10320124596641 / 12500000000000 : ℝ)) (b := (33709091099 / 20000000000000 : ℝ)) (q := (72342317501 / 3125000000000 : ℝ))
      (E := (cell12227 ⟨44, by decide⟩).energy) (xi := (69467873066693 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12227 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12227]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12227])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12227) (a := (10320124596641 / 12500000000000 : ℝ)) (b := (33709091099 / 20000000000000 : ℝ)) (q := (72342317501 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12227])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12227])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12227]

theorem cert12227_45 : CellCertificate 12227 (450197788458709 / 5000000000000000 : ℝ) (171789448468463 / 100000000000000000 : ℝ) (69467873066693 / 2000000000000000 : ℝ)
    (cell12227 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · have h := gap_lower (n := 12227) (a := (41263470074271 / 50000000000000 : ℝ)) (b := (33709091099 / 20000000000000 : ℝ)) (q := (2314958142599 / 100000000000000 : ℝ))
      (E := (cell12227 ⟨45, by decide⟩).energy) (xi := (69467873066693 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12227 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12227]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12227])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12227) (a := (41263470074271 / 50000000000000 : ℝ)) (b := (33709091099 / 20000000000000 : ℝ)) (q := (2314958142599 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12227])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12227])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12227]

theorem cert12227_46 : CellCertificate 12227 (450197788458709 / 5000000000000000 : ℝ) (171789448468463 / 100000000000000000 : ℝ) (69467873066693 / 2000000000000000 : ℝ)
    (cell12227 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · have h := gap_lower (n := 12227) (a := (41246453610567 / 50000000000000 : ℝ)) (b := (33709091099 / 20000000000000 : ℝ)) (q := (2314962145367 / 100000000000000 : ℝ))
      (E := (cell12227 ⟨46, by decide⟩).energy) (xi := (69467873066693 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12227 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12227]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12227])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12227) (a := (41246453610567 / 50000000000000 : ℝ)) (b := (33709091099 / 20000000000000 : ℝ)) (q := (2314962145367 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12227])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12227])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12227]

theorem cert12227_47 : CellCertificate 12227 (450197788458709 / 5000000000000000 : ℝ) (171789448468463 / 100000000000000000 : ℝ) (69467873066693 / 2000000000000000 : ℝ)
    (cell12227 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · have h := gap_lower (n := 12227) (a := (41229448980723 / 50000000000000 : ℝ)) (b := (33709091099 / 20000000000000 : ℝ)) (q := (462993233487 / 20000000000000 : ℝ))
      (E := (cell12227 ⟨47, by decide⟩).energy) (xi := (69467873066693 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12227 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12227]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12227])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12227) (a := (41229448980723 / 50000000000000 : ℝ)) (b := (33709091099 / 20000000000000 : ℝ)) (q := (462993233487 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12227])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12227])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12227]

theorem cert12227_48 : CellCertificate 12227 (450197788458709 / 5000000000000000 : ℝ) (171789448468463 / 100000000000000000 : ℝ) (69467873066693 / 2000000000000000 : ℝ)
    (cell12227 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · have h := gap_lower (n := 12227) (a := (82424912340167 / 100000000000000 : ℝ)) (b := (33709091099 / 20000000000000 : ℝ)) (q := (1446856343 / 62500000000 : ℝ))
      (E := (cell12227 ⟨48, by decide⟩).energy) (xi := (69467873066693 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12227 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12227]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12227])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12227) (a := (82424912340167 / 100000000000000 : ℝ)) (b := (33709091099 / 20000000000000 : ℝ)) (q := (1446856343 / 62500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12227])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12227])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12227]

theorem cert12227_49 : CellCertificate 12227 (450197788458709 / 5000000000000000 : ℝ) (171789448468463 / 100000000000000000 : ℝ) (69467873066693 / 2000000000000000 : ℝ)
    (cell12227 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · have h := gap_lower (n := 12227) (a := (82390950328133 / 100000000000000 : ℝ)) (b := (33709091099 / 20000000000000 : ℝ)) (q := (231497414697 / 10000000000000 : ℝ))
      (E := (cell12227 ⟨49, by decide⟩).energy) (xi := (69467873066693 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12227 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12227]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12227])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12227) (a := (82390950328133 / 100000000000000 : ℝ)) (b := (33709091099 / 20000000000000 : ℝ)) (q := (231497414697 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12227])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12227])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12227]

theorem cert12227_50 : CellCertificate 12227 (450197788458709 / 5000000000000000 : ℝ) (171789448468463 / 100000000000000000 : ℝ) (69467873066693 / 2000000000000000 : ℝ)
    (cell12227 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · have h := gap_lower (n := 12227) (a := (82357011896329 / 100000000000000 : ℝ)) (b := (33709091099 / 20000000000000 : ℝ)) (q := (115748905073 / 5000000000000 : ℝ))
      (E := (cell12227 ⟨50, by decide⟩).energy) (xi := (69467873066693 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12227 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12227]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12227])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12227) (a := (82357011896329 / 100000000000000 : ℝ)) (b := (33709091099 / 20000000000000 : ℝ)) (q := (115748905073 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12227])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12227])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12227]

theorem cert12227_51 : CellCertificate 12227 (450197788458709 / 5000000000000000 : ℝ) (171789448468463 / 100000000000000000 : ℝ) (69467873066693 / 2000000000000000 : ℝ)
    (cell12227 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · have h := gap_lower (n := 12227) (a := (41161548507943 / 50000000000000 : ℝ)) (b := (33709091099 / 20000000000000 : ℝ)) (q := (2314982128351 / 100000000000000 : ℝ))
      (E := (cell12227 ⟨51, by decide⟩).energy) (xi := (69467873066693 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12227 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12227]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12227])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12227) (a := (41161548507943 / 50000000000000 : ℝ)) (b := (33709091099 / 20000000000000 : ℝ)) (q := (2314982128351 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12227])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12227])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12227]

theorem cert12227_52 : CellCertificate 12227 (450197788458709 / 5000000000000000 : ℝ) (171789448468463 / 100000000000000000 : ℝ) (69467873066693 / 2000000000000000 : ℝ)
    (cell12227 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · have h := gap_lower (n := 12227) (a := (82289205658077 / 100000000000000 : ℝ)) (b := (33709091099 / 20000000000000 : ℝ)) (q := (2314986107777 / 100000000000000 : ℝ))
      (E := (cell12227 ⟨52, by decide⟩).energy) (xi := (69467873066693 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12227 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12227]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12227])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12227) (a := (82289205658077 / 100000000000000 : ℝ)) (b := (33709091099 / 20000000000000 : ℝ)) (q := (2314986107777 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12227])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12227])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12227]

theorem cert12227_53 : CellCertificate 12227 (450197788458709 / 5000000000000000 : ℝ) (171789448468463 / 100000000000000000 : ℝ) (69467873066693 / 2000000000000000 : ℝ)
    (cell12227 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · have h := gap_lower (n := 12227) (a := (41127668897161 / 50000000000000 : ℝ)) (b := (33709091099 / 20000000000000 : ℝ)) (q := (2314990096481 / 100000000000000 : ℝ))
      (E := (cell12227 ⟨53, by decide⟩).energy) (xi := (69467873066693 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12227 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12227]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12227])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12227) (a := (41127668897161 / 50000000000000 : ℝ)) (b := (33709091099 / 20000000000000 : ℝ)) (q := (2314990096481 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12227])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12227])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12227]

theorem cert12227_54 : CellCertificate 12227 (450197788458709 / 5000000000000000 : ℝ) (171789448468463 / 100000000000000000 : ℝ) (69467873066693 / 2000000000000000 : ℝ)
    (cell12227 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · have h := gap_lower (n := 12227) (a := (16444298679237 / 20000000000000 : ℝ)) (b := (33709091099 / 20000000000000 : ℝ)) (q := (2314994092059 / 100000000000000 : ℝ))
      (E := (cell12227 ⟨54, by decide⟩).energy) (xi := (69467873066693 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12227 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12227]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12227])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12227) (a := (16444298679237 / 20000000000000 : ℝ)) (b := (33709091099 / 20000000000000 : ℝ)) (q := (2314994092059 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12227])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12227])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12227]

theorem cert12227_55 : CellCertificate 12227 (450197788458709 / 5000000000000000 : ℝ) (171789448468463 / 100000000000000000 : ℝ) (69467873066693 / 2000000000000000 : ℝ)
    (cell12227 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · have h := gap_lower (n := 12227) (a := (20546918108843 / 25000000000000 : ℝ)) (b := (33709091099 / 20000000000000 : ℝ)) (q := (2314998091897 / 100000000000000 : ℝ))
      (E := (cell12227 ⟨55, by decide⟩).energy) (xi := (69467873066693 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12227 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12227]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12227])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12227) (a := (20546918108843 / 25000000000000 : ℝ)) (b := (33709091099 / 20000000000000 : ℝ)) (q := (2314998091897 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12227])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12227])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12227]

theorem cert12227_56 : CellCertificate 12227 (450197788458709 / 5000000000000000 : ℝ) (171789448468463 / 100000000000000000 : ℝ) (69467873066693 / 2000000000000000 : ℝ)
    (cell12227 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · have h := gap_lower (n := 12227) (a := (5134617180233 / 6250000000000 : ℝ)) (b := (33709091099 / 20000000000000 : ℝ)) (q := (2315002093173 / 100000000000000 : ℝ))
      (E := (cell12227 ⟨56, by decide⟩).energy) (xi := (69467873066693 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12227 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12227]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12227])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12227) (a := (5134617180233 / 6250000000000 : ℝ)) (b := (33709091099 / 20000000000000 : ℝ)) (q := (2315002093173 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12227])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12227])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12227]

theorem cert12227_57 : CellCertificate 12227 (450197788458709 / 5000000000000000 : ℝ) (171789448468463 / 100000000000000000 : ℝ) (69467873066693 / 2000000000000000 : ℝ)
    (cell12227 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · have h := gap_lower (n := 12227) (a := (20530025178311 / 25000000000000 : ℝ)) (b := (33709091099 / 20000000000000 : ℝ)) (q := (46300121857 / 2000000000000 : ℝ))
      (E := (cell12227 ⟨57, by decide⟩).energy) (xi := (69467873066693 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12227 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12227]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12227])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12227) (a := (20530025178311 / 25000000000000 : ℝ)) (b := (33709091099 / 20000000000000 : ℝ)) (q := (46300121857 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12227])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12227])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12227]

theorem cert12227_58 : CellCertificate 12227 (450197788458709 / 5000000000000000 : ℝ) (171789448468463 / 100000000000000000 : ℝ) (69467873066693 / 2000000000000000 : ℝ)
    (cell12227 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · have h := gap_lower (n := 12227) (a := (82086349896047 / 100000000000000 : ℝ)) (b := (33709091099 / 20000000000000 : ℝ)) (q := (1157505043843 / 50000000000000 : ℝ))
      (E := (cell12227 ⟨58, by decide⟩).energy) (xi := (69467873066693 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12227 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12227]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12227])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12227) (a := (82086349896047 / 100000000000000 : ℝ)) (b := (33709091099 / 20000000000000 : ℝ)) (q := (1157505043843 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12227])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12227])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12227]

theorem cert12227_59 : CellCertificate 12227 (450197788458709 / 5000000000000000 : ℝ) (171789448468463 / 100000000000000000 : ℝ) (69467873066693 / 2000000000000000 : ℝ)
    (cell12227 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · have h := gap_lower (n := 12227) (a := (82052622404407 / 100000000000000 : ℝ)) (b := (33709091099 / 20000000000000 : ℝ)) (q := (1157507037113 / 50000000000000 : ℝ))
      (E := (cell12227 ⟨59, by decide⟩).energy) (xi := (69467873066693 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12227 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12227]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12227])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12227) (a := (82052622404407 / 100000000000000 : ℝ)) (b := (33709091099 / 20000000000000 : ℝ)) (q := (1157507037113 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12227])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12227])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12227]

theorem cert12228_40 : CellCertificate 12228 (450182763081037 / 5000000000000000 : ℝ) (13419952719689 / 7812500000000000 : ℝ) (347310194212083 / 10000000000000000 : ℝ)
    (cell12228 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · have h := gap_lower (n := 12228) (a := (20674364431093 / 25000000000000 : ℝ)) (b := (168531486109 / 100000000000000 : ℝ)) (q := (2314788938113 / 100000000000000 : ℝ))
      (E := (cell12228 ⟨40, by decide⟩).energy) (xi := (347310194212083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12228 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12228]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12228])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12228) (a := (20674364431093 / 25000000000000 : ℝ)) (b := (168531486109 / 100000000000000 : ℝ)) (q := (2314788938113 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12228])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12228])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12228]

theorem cert12228_41 : CellCertificate 12228 (450182763081037 / 5000000000000000 : ℝ) (13419952719689 / 7812500000000000 : ℝ) (347310194212083 / 10000000000000000 : ℝ)
    (cell12228 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · have h := gap_lower (n := 12228) (a := (41331653167173 / 50000000000000 : ℝ)) (b := (168531486109 / 100000000000000 : ℝ)) (q := (2314792917349 / 100000000000000 : ℝ))
      (E := (cell12228 ⟨41, by decide⟩).energy) (xi := (347310194212083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12228 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12228]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12228])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12228) (a := (41331653167173 / 50000000000000 : ℝ)) (b := (168531486109 / 100000000000000 : ℝ)) (q := (2314792917349 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12228])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12228])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12228]

theorem cert12228_42 : CellCertificate 12228 (450182763081037 / 5000000000000000 : ℝ) (13419952719689 / 7812500000000000 : ℝ) (347310194212083 / 10000000000000000 : ℝ)
    (cell12228 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · have h := gap_lower (n := 12228) (a := (41314589380197 / 50000000000000 : ℝ)) (b := (168531486109 / 100000000000000 : ℝ)) (q := (578699229753 / 25000000000000 : ℝ))
      (E := (cell12228 ⟨42, by decide⟩).energy) (xi := (347310194212083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12228 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12228]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12228])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12228) (a := (41314589380197 / 50000000000000 : ℝ)) (b := (168531486109 / 100000000000000 : ℝ)) (q := (578699229753 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12228])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12228])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12228]

theorem cert12228_43 : CellCertificate 12228 (450182763081037 / 5000000000000000 : ℝ) (13419952719689 / 7812500000000000 : ℝ) (347310194212083 / 10000000000000000 : ℝ)
    (cell12228 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · have h := gap_lower (n := 12228) (a := (10324384371557 / 12500000000000 : ℝ)) (b := (168531486109 / 100000000000000 : ℝ)) (q := (2314800884309 / 100000000000000 : ℝ))
      (E := (cell12228 ⟨43, by decide⟩).energy) (xi := (347310194212083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12228 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12228]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12228])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12228) (a := (10324384371557 / 12500000000000 : ℝ)) (b := (168531486109 / 100000000000000 : ℝ)) (q := (2314800884309 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12228])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12228])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12228]

theorem cert12228_44 : CellCertificate 12228 (450182763081037 / 5000000000000000 : ℝ) (13419952719689 / 7812500000000000 : ℝ) (347310194212083 / 10000000000000000 : ℝ)
    (cell12228 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · have h := gap_lower (n := 12228) (a := (41280497470311 / 50000000000000 : ℝ)) (b := (168531486109 / 100000000000000 : ℝ)) (q := (462960974343 / 20000000000000 : ℝ))
      (E := (cell12228 ⟨44, by decide⟩).energy) (xi := (347310194212083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12228 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12228]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12228])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12228) (a := (41280497470311 / 50000000000000 : ℝ)) (b := (168531486109 / 100000000000000 : ℝ)) (q := (462960974343 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12228])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12228])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12228]

theorem cert12228_45 : CellCertificate 12228 (450182763081037 / 5000000000000000 : ℝ) (13419952719689 / 7812500000000000 : ℝ) (347310194212083 / 10000000000000000 : ℝ)
    (cell12228 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · have h := gap_lower (n := 12228) (a := (41263469317567 / 50000000000000 : ℝ)) (b := (168531486109 / 100000000000000 : ℝ)) (q := (2314808880769 / 100000000000000 : ℝ))
      (E := (cell12228 ⟨45, by decide⟩).energy) (xi := (347310194212083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12228 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12228]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12228])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12228) (a := (41263469317567 / 50000000000000 : ℝ)) (b := (168531486109 / 100000000000000 : ℝ)) (q := (2314808880769 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12228])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12228])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12228]

theorem cert12228_46 : CellCertificate 12228 (450182763081037 / 5000000000000000 : ℝ) (13419952719689 / 7812500000000000 : ℝ) (347310194212083 / 10000000000000000 : ℝ)
    (cell12228 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · have h := gap_lower (n := 12228) (a := (41246453013191 / 50000000000000 : ℝ)) (b := (168531486109 / 100000000000000 : ℝ)) (q := (2314812910789 / 100000000000000 : ℝ))
      (E := (cell12228 ⟨46, by decide⟩).energy) (xi := (347310194212083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12228 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12228]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12228])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12228) (a := (41246453013191 / 50000000000000 : ℝ)) (b := (168531486109 / 100000000000000 : ℝ)) (q := (2314812910789 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12228])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12228])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12228]

theorem cert12228_47 : CellCertificate 12228 (450182763081037 / 5000000000000000 : ℝ) (13419952719689 / 7812500000000000 : ℝ) (347310194212083 / 10000000000000000 : ℝ)
    (cell12228 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · have h := gap_lower (n := 12228) (a := (8245889708491 / 10000000000000 : ℝ)) (b := (168531486109 / 100000000000000 : ℝ)) (q := (289352112751 / 12500000000000 : ℝ))
      (E := (cell12228 ⟨47, by decide⟩).energy) (xi := (347310194212083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12228 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12228]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12228])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12228) (a := (8245889708491 / 10000000000000 : ℝ)) (b := (168531486109 / 100000000000000 : ℝ)) (q := (289352112751 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12228])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12228])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12228]

theorem cert12228_48 : CellCertificate 12228 (450182763081037 / 5000000000000000 : ℝ) (13419952719689 / 7812500000000000 : ℝ) (347310194212083 / 10000000000000000 : ℝ)
    (cell12228 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · have h := gap_lower (n := 12228) (a := (82424911781407 / 100000000000000 : ℝ)) (b := (168531486109 / 100000000000000 : ℝ)) (q := (2314820853239 / 100000000000000 : ℝ))
      (E := (cell12228 ⟨48, by decide⟩).energy) (xi := (347310194212083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12228 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12228]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12228])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12228) (a := (82424911781407 / 100000000000000 : ℝ)) (b := (168531486109 / 100000000000000 : ℝ)) (q := (2314820853239 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12228])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12228])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12228]

theorem cert12228_49 : CellCertificate 12228 (450182763081037 / 5000000000000000 : ℝ) (13419952719689 / 7812500000000000 : ℝ) (347310194212083 / 10000000000000000 : ℝ)
    (cell12228 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · have h := gap_lower (n := 12228) (a := (8239095008671 / 10000000000000 : ℝ)) (b := (168531486109 / 100000000000000 : ℝ)) (q := (2314824880901 / 100000000000000 : ℝ))
      (E := (cell12228 ⟨49, by decide⟩).energy) (xi := (347310194212083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12228 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12228]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12228])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12228) (a := (8239095008671 / 10000000000000 : ℝ)) (b := (168531486109 / 100000000000000 : ℝ)) (q := (2314824880901 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12228])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12228])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12228]

theorem cert12228_50 : CellCertificate 12228 (450182763081037 / 5000000000000000 : ℝ) (13419952719689 / 7812500000000000 : ℝ) (347310194212083 / 10000000000000000 : ℝ)
    (cell12228 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · have h := gap_lower (n := 12228) (a := (41178505985903 / 50000000000000 : ℝ)) (b := (168531486109 / 100000000000000 : ℝ)) (q := (2314828865643 / 100000000000000 : ℝ))
      (E := (cell12228 ⟨50, by decide⟩).energy) (xi := (347310194212083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12228 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12228]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12228])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12228) (a := (41178505985903 / 50000000000000 : ℝ)) (b := (168531486109 / 100000000000000 : ℝ)) (q := (2314828865643 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12228])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12228])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12228]

theorem cert12228_51 : CellCertificate 12228 (450182763081037 / 5000000000000000 : ℝ) (13419952719689 / 7812500000000000 : ℝ) (347310194212083 / 10000000000000000 : ℝ)
    (cell12228 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · have h := gap_lower (n := 12228) (a := (82323097407823 / 100000000000000 : ℝ)) (b := (168531486109 / 100000000000000 : ℝ)) (q := (144677054037 / 6250000000000 : ℝ))
      (E := (cell12228 ⟨51, by decide⟩).energy) (xi := (347310194212083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12228 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12228]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12228])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12228) (a := (82323097407823 / 100000000000000 : ℝ)) (b := (168531486109 / 100000000000000 : ℝ)) (q := (144677054037 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12228])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12228])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12228]

theorem cert12228_52 : CellCertificate 12228 (450182763081037 / 5000000000000000 : ℝ) (13419952719689 / 7812500000000000 : ℝ) (347310194212083 / 10000000000000000 : ℝ)
    (cell12228 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · have h := gap_lower (n := 12228) (a := (82289206366039 / 100000000000000 : ℝ)) (b := (168531486109 / 100000000000000 : ℝ)) (q := (2314836875767 / 100000000000000 : ℝ))
      (E := (cell12228 ⟨52, by decide⟩).energy) (xi := (347310194212083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12228 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12228]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12228])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12228) (a := (82289206366039 / 100000000000000 : ℝ)) (b := (168531486109 / 100000000000000 : ℝ)) (q := (2314836875767 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12228])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12228])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12228]

theorem cert12228_53 : CellCertificate 12228 (450182763081037 / 5000000000000000 : ℝ) (13419952719689 / 7812500000000000 : ℝ) (347310194212083 / 10000000000000000 : ℝ)
    (cell12228 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · have h := gap_lower (n := 12228) (a := (41127669408937 / 50000000000000 : ℝ)) (b := (168531486109 / 100000000000000 : ℝ)) (q := (2314840837973 / 100000000000000 : ℝ))
      (E := (cell12228 ⟨53, by decide⟩).energy) (xi := (347310194212083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12228 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12228]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12228])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12228) (a := (41127669408937 / 50000000000000 : ℝ)) (b := (168531486109 / 100000000000000 : ℝ)) (q := (2314840837973 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12228])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12228])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12228]

theorem cert12228_54 : CellCertificate 12228 (450182763081037 / 5000000000000000 : ℝ) (13419952719689 / 7812500000000000 : ℝ) (347310194212083 / 10000000000000000 : ℝ)
    (cell12228 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · have h := gap_lower (n := 12228) (a := (8222149473489 / 10000000000000 : ℝ)) (b := (168531486109 / 100000000000000 : ℝ)) (q := (578711216699 / 25000000000000 : ℝ))
      (E := (cell12228 ⟨54, by decide⟩).energy) (xi := (347310194212083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12228 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12228]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12228])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12228) (a := (8222149473489 / 10000000000000 : ℝ)) (b := (168531486109 / 100000000000000 : ℝ)) (q := (578711216699 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12228])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12228])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12228]

theorem cert12228_55 : CellCertificate 12228 (450182763081037 / 5000000000000000 : ℝ) (13419952719689 / 7812500000000000 : ℝ) (347310194212083 / 10000000000000000 : ℝ)
    (cell12228 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · have h := gap_lower (n := 12228) (a := (20546918522199 / 25000000000000 : ℝ)) (b := (168531486109 / 100000000000000 : ℝ)) (q := (2314848841583 / 100000000000000 : ℝ))
      (E := (cell12228 ⟨55, by decide⟩).energy) (xi := (347310194212083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12228 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12228]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12228])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12228) (a := (20546918522199 / 25000000000000 : ℝ)) (b := (168531486109 / 100000000000000 : ℝ)) (q := (2314848841583 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12228])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12228])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12228]

theorem cert12228_56 : CellCertificate 12228 (450182763081037 / 5000000000000000 : ℝ) (13419952719689 / 7812500000000000 : ℝ) (347310194212083 / 10000000000000000 : ℝ)
    (cell12228 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · have h := gap_lower (n := 12228) (a := (41076938425719 / 50000000000000 : ℝ)) (b := (168531486109 / 100000000000000 : ℝ)) (q := (1157426409259 / 50000000000000 : ℝ))
      (E := (cell12228 ⟨56, by decide⟩).energy) (xi := (347310194212083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12228 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12228]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12228])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12228) (a := (41076938425719 / 50000000000000 : ℝ)) (b := (168531486109 / 100000000000000 : ℝ)) (q := (1157426409259 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12228])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12228])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12228]

theorem cert12228_57 : CellCertificate 12228 (450182763081037 / 5000000000000000 : ℝ) (13419952719689 / 7812500000000000 : ℝ) (347310194212083 / 10000000000000000 : ℝ)
    (cell12228 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · have h := gap_lower (n := 12228) (a := (41060051497403 / 50000000000000 : ℝ)) (b := (168531486109 / 100000000000000 : ℝ)) (q := (1157428426831 / 50000000000000 : ℝ))
      (E := (cell12228 ⟨57, by decide⟩).energy) (xi := (347310194212083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12228 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12228]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12228])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12228) (a := (41060051497403 / 50000000000000 : ℝ)) (b := (168531486109 / 100000000000000 : ℝ)) (q := (1157428426831 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12228])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12228])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12228]

theorem cert12228_58 : CellCertificate 12228 (450182763081037 / 5000000000000000 : ℝ) (13419952719689 / 7812500000000000 : ℝ) (347310194212083 / 10000000000000000 : ℝ)
    (cell12228 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · have h := gap_lower (n := 12228) (a := (8208635249103 / 10000000000000 : ℝ)) (b := (168531486109 / 100000000000000 : ℝ)) (q := (2314860825597 / 100000000000000 : ℝ))
      (E := (cell12228 ⟨58, by decide⟩).energy) (xi := (347310194212083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12228 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12228]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12228])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12228) (a := (8208635249103 / 10000000000000 : ℝ)) (b := (168531486109 / 100000000000000 : ℝ)) (q := (2314860825597 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12228])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12228])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12228]

theorem cert12228_59 : CellCertificate 12228 (450182763081037 / 5000000000000000 : ℝ) (13419952719689 / 7812500000000000 : ℝ) (347310194212083 / 10000000000000000 : ℝ)
    (cell12228 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · have h := gap_lower (n := 12228) (a := (82052625312379 / 100000000000000 : ℝ)) (b := (168531486109 / 100000000000000 : ℝ)) (q := (2314864849091 / 100000000000000 : ℝ))
      (E := (cell12228 ⟨59, by decide⟩).energy) (xi := (347310194212083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12228 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12228]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12228])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12228) (a := (82052625312379 / 100000000000000 : ℝ)) (b := (168531486109 / 100000000000000 : ℝ)) (q := (2314864849091 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12228])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12228])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12228]

theorem cert12229_40 : CellCertificate 12229 (28135483754483 / 312500000000000 : ℝ) (343522686909549 / 200000000000000000 : ℝ) (173640514060081 / 5000000000000000 : ℝ)
    (cell12229 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · have h := gap_lower (n := 12229) (a := (20674363653013 / 25000000000000 : ℝ)) (b := (16851751907 / 10000000000000 : ℝ)) (q := (2314639723923 / 100000000000000 : ℝ))
      (E := (cell12229 ⟨40, by decide⟩).energy) (xi := (173640514060081 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12229 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12229]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12229])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12229) (a := (20674363653013 / 25000000000000 : ℝ)) (b := (16851751907 / 10000000000000 : ℝ)) (q := (2314639723923 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12229])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12229])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12229]

theorem cert12229_41 : CellCertificate 12229 (28135483754483 / 312500000000000 : ℝ) (343522686909549 / 200000000000000000 : ℝ) (173640514060081 / 5000000000000000 : ℝ)
    (cell12229 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · have h := gap_lower (n := 12229) (a := (10332912942857 / 12500000000000 : ℝ)) (b := (16851751907 / 10000000000000 : ℝ)) (q := (462928745339 / 20000000000000 : ℝ))
      (E := (cell12229 ⟨41, by decide⟩).energy) (xi := (173640514060081 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12229 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12229]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12229])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12229) (a := (10332912942857 / 12500000000000 : ℝ)) (b := (16851751907 / 10000000000000 : ℝ)) (q := (462928745339 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12229])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12229])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12229]

theorem cert12229_42 : CellCertificate 12229 (28135483754483 / 312500000000000 : ℝ) (343522686909549 / 200000000000000000 : ℝ) (173640514060081 / 5000000000000000 : ℝ)
    (cell12229 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · have h := gap_lower (n := 12229) (a := (82629176289291 / 100000000000000 : ℝ)) (b := (16851751907 / 10000000000000 : ℝ)) (q := (115732387633 / 5000000000000 : ℝ))
      (E := (cell12229 ⟨42, by decide⟩).energy) (xi := (173640514060081 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12229 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12229]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12229])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12229) (a := (82629176289291 / 100000000000000 : ℝ)) (b := (16851751907 / 10000000000000 : ℝ)) (q := (115732387633 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12229])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12229])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12229]

theorem cert12229_43 : CellCertificate 12229 (28135483754483 / 312500000000000 : ℝ) (343522686909549 / 200000000000000000 : ℝ) (173640514060081 / 5000000000000000 : ℝ)
    (cell12229 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · have h := gap_lower (n := 12229) (a := (16519014564259 / 20000000000000 : ℝ)) (b := (16851751907 / 10000000000000 : ℝ)) (q := (92586069721 / 4000000000000 : ℝ))
      (E := (cell12229 ⟨43, by decide⟩).energy) (xi := (173640514060081 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12229 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12229]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12229])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12229) (a := (16519014564259 / 20000000000000 : ℝ)) (b := (16851751907 / 10000000000000 : ℝ)) (q := (92586069721 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12229])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12229])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12229]

theorem cert12229_44 : CellCertificate 12229 (28135483754483 / 312500000000000 : ℝ) (343522686909549 / 200000000000000000 : ℝ) (173640514060081 / 5000000000000000 : ℝ)
    (cell12229 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · have h := gap_lower (n := 12229) (a := (82560993108961 / 100000000000000 : ℝ)) (b := (16851751907 / 10000000000000 : ℝ)) (q := (1157327878133 / 50000000000000 : ℝ))
      (E := (cell12229 ⟨44, by decide⟩).energy) (xi := (173640514060081 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12229 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12229]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12229])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12229) (a := (82560993108961 / 100000000000000 : ℝ)) (b := (16851751907 / 10000000000000 : ℝ)) (q := (1157327878133 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12229])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12229])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12229]

theorem cert12229_45 : CellCertificate 12229 (28135483754483 / 312500000000000 : ℝ) (343522686909549 / 200000000000000000 : ℝ) (173640514060081 / 5000000000000000 : ℝ)
    (cell12229 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · have h := gap_lower (n := 12229) (a := (8252693712253 / 10000000000000 : ℝ)) (b := (16851751907 / 10000000000000 : ℝ)) (q := (1157329866551 / 50000000000000 : ℝ))
      (E := (cell12229 ⟨45, by decide⟩).energy) (xi := (173640514060081 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12229 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12229]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12229])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12229) (a := (8252693712253 / 10000000000000 : ℝ)) (b := (16851751907 / 10000000000000 : ℝ)) (q := (1157329866551 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12229])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12229])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12229]

theorem cert12229_46 : CellCertificate 12229 (28135483754483 / 312500000000000 : ℝ) (343522686909549 / 200000000000000000 : ℝ) (173640514060081 / 5000000000000000 : ℝ)
    (cell12229 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · have h := gap_lower (n := 12229) (a := (16498580966479 / 20000000000000 : ℝ)) (b := (16851751907 / 10000000000000 : ℝ)) (q := (115733186581 / 5000000000000 : ℝ))
      (E := (cell12229 ⟨46, by decide⟩).energy) (xi := (173640514060081 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12229 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12229]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12229])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12229) (a := (16498580966479 / 20000000000000 : ℝ)) (b := (16851751907 / 10000000000000 : ℝ)) (q := (115733186581 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12229])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12229])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12229]

theorem cert12229_47 : CellCertificate 12229 (28135483754483 / 312500000000000 : ℝ) (343522686909549 / 200000000000000000 : ℝ) (173640514060081 / 5000000000000000 : ℝ)
    (cell12229 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · have h := gap_lower (n := 12229) (a := (41229448104549 / 50000000000000 : ℝ)) (b := (16851751907 / 10000000000000 : ℝ)) (q := (289333461507 / 12500000000000 : ℝ))
      (E := (cell12229 ⟨47, by decide⟩).energy) (xi := (173640514060081 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12229 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12229]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12229])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12229) (a := (41229448104549 / 50000000000000 : ℝ)) (b := (16851751907 / 10000000000000 : ℝ)) (q := (289333461507 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12229])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12229])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12229]

theorem cert12229_48 : CellCertificate 12229 (28135483754483 / 312500000000000 : ℝ) (343522686909549 / 200000000000000000 : ℝ) (173640514060081 / 5000000000000000 : ℝ)
    (cell12229 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · have h := gap_lower (n := 12229) (a := (82424911223331 / 100000000000000 : ℝ)) (b := (16851751907 / 10000000000000 : ℝ)) (q := (2314671730993 / 100000000000000 : ℝ))
      (E := (cell12229 ⟨48, by decide⟩).energy) (xi := (173640514060081 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12229 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12229]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12229])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12229) (a := (82424911223331 / 100000000000000 : ℝ)) (b := (16851751907 / 10000000000000 : ℝ)) (q := (2314671730993 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12229])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12229])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12229]

theorem cert12229_49 : CellCertificate 12229 (28135483754483 / 312500000000000 : ℝ) (343522686909549 / 200000000000000000 : ℝ) (173640514060081 / 5000000000000000 : ℝ)
    (cell12229 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · have h := gap_lower (n := 12229) (a := (20597737461483 / 25000000000000 : ℝ)) (b := (16851751907 / 10000000000000 : ℝ)) (q := (1157337864673 / 50000000000000 : ℝ))
      (E := (cell12229 ⟨49, by decide⟩).energy) (xi := (173640514060081 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12229 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12229]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12229])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12229) (a := (20597737461483 / 25000000000000 : ℝ)) (b := (16851751907 / 10000000000000 : ℝ)) (q := (1157337864673 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12229])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12229])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12229]

theorem cert12229_50 : CellCertificate 12229 (28135483754483 / 312500000000000 : ℝ) (343522686909549 / 200000000000000000 : ℝ) (173640514060081 / 5000000000000000 : ℝ)
    (cell12229 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · have h := gap_lower (n := 12229) (a := (41178506023943 / 50000000000000 : ℝ)) (b := (16851751907 / 10000000000000 : ℝ)) (q := (289334960687 / 12500000000000 : ℝ))
      (E := (cell12229 ⟨50, by decide⟩).energy) (xi := (173640514060081 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12229 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12229]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12229])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12229) (a := (41178506023943 / 50000000000000 : ℝ)) (b := (16851751907 / 10000000000000 : ℝ)) (q := (289334960687 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12229])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12229])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12229]

theorem cert12229_51 : CellCertificate 12229 (28135483754483 / 312500000000000 : ℝ) (343522686909549 / 200000000000000000 : ℝ) (173640514060081 / 5000000000000000 : ℝ)
    (cell12229 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · have h := gap_lower (n := 12229) (a := (41161548900163 / 50000000000000 : ℝ)) (b := (16851751907 / 10000000000000 : ℝ)) (q := (1157341857761 / 50000000000000 : ℝ))
      (E := (cell12229 ⟨51, by decide⟩).energy) (xi := (173640514060081 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12229 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12229]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12229])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12229) (a := (41161548900163 / 50000000000000 : ℝ)) (b := (16851751907 / 10000000000000 : ℝ)) (q := (1157341857761 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12229])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12229])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12229]

theorem cert12229_52 : CellCertificate 12229 (28135483754483 / 312500000000000 : ℝ) (343522686909549 / 200000000000000000 : ℝ) (173640514060081 / 5000000000000000 : ℝ)
    (cell12229 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · have h := gap_lower (n := 12229) (a := (82289207074527 / 100000000000000 : ℝ)) (b := (16851751907 / 10000000000000 : ℝ)) (q := (1157343849777 / 50000000000000 : ℝ))
      (E := (cell12229 ⟨52, by decide⟩).energy) (xi := (173640514060081 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12229 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12229]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12229])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12229) (a := (82289207074527 / 100000000000000 : ℝ)) (b := (16851751907 / 10000000000000 : ℝ)) (q := (1157343849777 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12229])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12229])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12229]

theorem cert12229_53 : CellCertificate 12229 (28135483754483 / 312500000000000 : ℝ) (343522686909549 / 200000000000000000 : ℝ) (173640514060081 / 5000000000000000 : ℝ)
    (cell12229 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · have h := gap_lower (n := 12229) (a := (8225533984191 / 10000000000000 : ℝ)) (b := (16851751907 / 10000000000000 : ℝ)) (q := (1157345847167 / 50000000000000 : ℝ))
      (E := (cell12229 ⟨53, by decide⟩).energy) (xi := (173640514060081 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12229 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12229]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12229])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12229) (a := (8225533984191 / 10000000000000 : ℝ)) (b := (16851751907 / 10000000000000 : ℝ)) (q := (1157345847167 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12229])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12229])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12229]

theorem cert12229_54 : CellCertificate 12229 (28135483754483 / 312500000000000 : ℝ) (343522686909549 / 200000000000000000 : ℝ) (173640514060081 / 5000000000000000 : ℝ)
    (cell12229 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · have h := gap_lower (n := 12229) (a := (82221496074041 / 100000000000000 : ℝ)) (b := (16851751907 / 10000000000000 : ℝ)) (q := (2314695697459 / 100000000000000 : ℝ))
      (E := (cell12229 ⟨54, by decide⟩).energy) (xi := (173640514060081 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12229 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12229]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12229])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12229) (a := (82221496074041 / 100000000000000 : ℝ)) (b := (16851751907 / 10000000000000 : ℝ)) (q := (2314695697459 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12229])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12229])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12229]

theorem cert12229_55 : CellCertificate 12229 (28135483754483 / 312500000000000 : ℝ) (343522686909549 / 200000000000000000 : ℝ) (173640514060081 / 5000000000000000 : ℝ)
    (cell12229 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · have h := gap_lower (n := 12229) (a := (41093837871313 / 50000000000000 : ℝ)) (b := (16851751907 / 10000000000000 : ℝ)) (q := (289337463289 / 12500000000000 : ℝ))
      (E := (cell12229 ⟨55, by decide⟩).energy) (xi := (173640514060081 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12229 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12229]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12229])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12229) (a := (41093837871313 / 50000000000000 : ℝ)) (b := (16851751907 / 10000000000000 : ℝ)) (q := (289337463289 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12229])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12229])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12229]

theorem cert12229_56 : CellCertificate 12229 (28135483754483 / 312500000000000 : ℝ) (343522686909549 / 200000000000000000 : ℝ) (173640514060081 / 5000000000000000 : ℝ)
    (cell12229 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · have h := gap_lower (n := 12229) (a := (16430775763903 / 20000000000000 : ℝ)) (b := (16851751907 / 10000000000000 : ℝ)) (q := (144668978687 / 6250000000000 : ℝ))
      (E := (cell12229 ⟨56, by decide⟩).energy) (xi := (173640514060081 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12229 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12229]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12229])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12229) (a := (16430775763903 / 20000000000000 : ℝ)) (b := (16851751907 / 10000000000000 : ℝ)) (q := (144668978687 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12229])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12229])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12229]

theorem cert12229_57 : CellCertificate 12229 (28135483754483 / 312500000000000 : ℝ) (343522686909549 / 200000000000000000 : ℝ) (173640514060081 / 5000000000000000 : ℝ)
    (cell12229 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · have h := gap_lower (n := 12229) (a := (10265013159587 / 12500000000000 : ℝ)) (b := (16851751907 / 10000000000000 : ℝ)) (q := (2314707670593 / 100000000000000 : ℝ))
      (E := (cell12229 ⟨57, by decide⟩).energy) (xi := (173640514060081 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12229 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12229]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12229])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12229) (a := (10265013159587 / 12500000000000 : ℝ)) (b := (16851751907 / 10000000000000 : ℝ)) (q := (2314707670593 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12229])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12229])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12229]

theorem cert12229_58 : CellCertificate 12229 (28135483754483 / 312500000000000 : ℝ) (343522686909549 / 200000000000000000 : ℝ) (173640514060081 / 5000000000000000 : ℝ)
    (cell12229 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · have h := gap_lower (n := 12229) (a := (82086355086301 / 100000000000000 : ℝ)) (b := (16851751907 / 10000000000000 : ℝ)) (q := (1157355839407 / 50000000000000 : ℝ))
      (E := (cell12229 ⟨58, by decide⟩).energy) (xi := (173640514060081 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12229 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12229]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12229])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12229) (a := (82086355086301 / 100000000000000 : ℝ)) (b := (16851751907 / 10000000000000 : ℝ)) (q := (1157355839407 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12229])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12229])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12229]

theorem cert12229_59 : CellCertificate 12229 (28135483754483 / 312500000000000 : ℝ) (343522686909549 / 200000000000000000 : ℝ) (173640514060081 / 5000000000000000 : ℝ)
    (cell12229 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · have h := gap_lower (n := 12229) (a := (82052628220599 / 100000000000000 : ℝ)) (b := (16851751907 / 10000000000000 : ℝ)) (q := (578678920051 / 25000000000000 : ℝ))
      (E := (cell12229 ⟨59, by decide⟩).energy) (xi := (173640514060081 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12229 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12229]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12229])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12229) (a := (82052628220599 / 100000000000000 : ℝ)) (b := (16851751907 / 10000000000000 : ℝ)) (q := (578678920051 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12229])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12229])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12229]

theorem cert12230_40 : CellCertificate 12230 (900305438860391 / 10000000000000000 : ℝ) (34349458879233 / 20000000000000000 : ℝ) (347251867056221 / 10000000000000000 : ℝ)
    (cell12230 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · have h := gap_lower (n := 12230) (a := (82697451500737 / 100000000000000 : ℝ)) (b := (84251777189 / 50000000000000 : ℝ)) (q := (462898136431 / 20000000000000 : ℝ))
      (E := (cell12230 ⟨40, by decide⟩).energy) (xi := (347251867056221 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12230 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12230]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12230])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12230) (a := (82697451500737 / 100000000000000 : ℝ)) (b := (84251777189 / 50000000000000 : ℝ)) (q := (462898136431 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12230])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12230])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12230]

theorem cert12230_41 : CellCertificate 12230 (900305438860391 / 10000000000000000 : ℝ) (34349458879233 / 20000000000000000 : ℝ) (347251867056221 / 10000000000000000 : ℝ)
    (cell12230 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · have h := gap_lower (n := 12230) (a := (82663300752331 / 100000000000000 : ℝ)) (b := (84251777189 / 50000000000000 : ℝ)) (q := (2314494649851 / 100000000000000 : ℝ))
      (E := (cell12230 ⟨41, by decide⟩).energy) (xi := (347251867056221 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12230 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12230]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12230])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12230) (a := (82663300752331 / 100000000000000 : ℝ)) (b := (84251777189 / 50000000000000 : ℝ)) (q := (2314494649851 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12230])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12230])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12230]

theorem cert12230_42 : CellCertificate 12230 (900305438860391 / 10000000000000000 : ℝ) (34349458879233 / 20000000000000000 : ℝ) (347251867056221 / 10000000000000000 : ℝ)
    (cell12230 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · have h := gap_lower (n := 12230) (a := (10328646727389 / 12500000000000 : ℝ)) (b := (84251777189 / 50000000000000 : ℝ)) (q := (115724932073 / 5000000000000 : ℝ))
      (E := (cell12230 ⟨42, by decide⟩).energy) (xi := (347251867056221 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12230 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12230]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12230])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12230) (a := (10328646727389 / 12500000000000 : ℝ)) (b := (84251777189 / 50000000000000 : ℝ)) (q := (115724932073 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12230])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12230])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12230]

theorem cert12230_43 : CellCertificate 12230 (900305438860391 / 10000000000000000 : ℝ) (34349458879233 / 20000000000000000 : ℝ) (347251867056221 / 10000000000000000 : ℝ)
    (cell12230 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · have h := gap_lower (n := 12230) (a := (82595070671019 / 100000000000000 : ℝ)) (b := (84251777189 / 50000000000000 : ℝ)) (q := (1157251328479 / 50000000000000 : ℝ))
      (E := (cell12230 ⟨43, by decide⟩).energy) (xi := (347251867056221 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12230 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12230]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12230])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12230) (a := (82595070671019 / 100000000000000 : ℝ)) (b := (84251777189 / 50000000000000 : ℝ)) (q := (1157251328479 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12230])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12230])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12230]

theorem cert12230_44 : CellCertificate 12230 (900305438860391 / 10000000000000000 : ℝ) (34349458879233 / 20000000000000000 : ℝ) (347251867056221 / 10000000000000000 : ℝ)
    (cell12230 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · have h := gap_lower (n := 12230) (a := (1290015488721 / 1562500000000 : ℝ)) (b := (84251777189 / 50000000000000 : ℝ)) (q := (462901327461 / 20000000000000 : ℝ))
      (E := (cell12230 ⟨44, by decide⟩).energy) (xi := (347251867056221 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12230 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12230]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12230])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12230) (a := (1290015488721 / 1562500000000 : ℝ)) (b := (84251777189 / 50000000000000 : ℝ)) (q := (462901327461 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12230])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12230])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12230]

theorem cert12230_45 : CellCertificate 12230 (900305438860391 / 10000000000000000 : ℝ) (34349458879233 / 20000000000000000 : ℝ) (347251867056221 / 10000000000000000 : ℝ)
    (cell12230 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · have h := gap_lower (n := 12230) (a := (8252693561073 / 10000000000000 : ℝ)) (b := (84251777189 / 50000000000000 : ℝ)) (q := (1157255320391 / 50000000000000 : ℝ))
      (E := (cell12230 ⟨45, by decide⟩).energy) (xi := (347251867056221 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12230 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12230]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12230])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12230) (a := (8252693561073 / 10000000000000 : ℝ)) (b := (84251777189 / 50000000000000 : ℝ)) (q := (1157255320391 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12230])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12230])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12230]

theorem cert12230_46 : CellCertificate 12230 (900305438860391 / 10000000000000000 : ℝ) (34349458879233 / 20000000000000000 : ℝ) (347251867056221 / 10000000000000000 : ℝ)
    (cell12230 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · have h := gap_lower (n := 12230) (a := (20623225909793 / 25000000000000 : ℝ)) (b := (84251777189 / 50000000000000 : ℝ)) (q := (144657166669 / 6250000000000 : ℝ))
      (E := (cell12230 ⟨46, by decide⟩).energy) (xi := (347251867056221 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12230 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12230]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12230])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12230) (a := (20623225909793 / 25000000000000 : ℝ)) (b := (84251777189 / 50000000000000 : ℝ)) (q := (144657166669 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12230])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12230])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12230]

theorem cert12230_47 : CellCertificate 12230 (900305438860391 / 10000000000000000 : ℝ) (34349458879233 / 20000000000000000 : ℝ) (347251867056221 / 10000000000000000 : ℝ)
    (cell12230 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · have h := gap_lower (n := 12230) (a := (82458895334011 / 100000000000000 : ℝ)) (b := (84251777189 / 50000000000000 : ℝ)) (q := (1157259327653 / 50000000000000 : ℝ))
      (E := (cell12230 ⟨47, by decide⟩).energy) (xi := (347251867056221 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12230 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12230]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12230])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12230) (a := (82458895334011 / 100000000000000 : ℝ)) (b := (84251777189 / 50000000000000 : ℝ)) (q := (1157259327653 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12230])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12230])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12230]

theorem cert12230_48 : CellCertificate 12230 (900305438860391 / 10000000000000000 : ℝ) (34349458879233 / 20000000000000000 : ℝ) (347251867056221 / 10000000000000000 : ℝ)
    (cell12230 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · have h := gap_lower (n := 12230) (a := (4121245533297 / 5000000000000 : ℝ)) (b := (84251777189 / 50000000000000 : ℝ)) (q := (2314522605399 / 100000000000000 : ℝ))
      (E := (cell12230 ⟨48, by decide⟩).energy) (xi := (347251867056221 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12230 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12230]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12230])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12230) (a := (4121245533297 / 5000000000000 : ℝ)) (b := (84251777189 / 50000000000000 : ℝ)) (q := (2314522605399 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12230])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12230])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12230]

theorem cert12230_49 : CellCertificate 12230 (900305438860391 / 10000000000000000 : ℝ) (34349458879233 / 20000000000000000 : ℝ) (347251867056221 / 10000000000000000 : ℝ)
    (cell12230 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · have h := gap_lower (n := 12230) (a := (41195474802899 / 50000000000000 : ℝ)) (b := (84251777189 / 50000000000000 : ℝ)) (q := (2314526633397 / 100000000000000 : ℝ))
      (E := (cell12230 ⟨49, by decide⟩).energy) (xi := (347251867056221 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12230 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12230]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12230])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12230) (a := (41195474802899 / 50000000000000 : ℝ)) (b := (84251777189 / 50000000000000 : ℝ)) (q := (2314526633397 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12230])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12230])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12230]

theorem cert12230_50 : CellCertificate 12230 (900305438860391 / 10000000000000000 : ℝ) (34349458879233 / 20000000000000000 : ℝ) (347251867056221 / 10000000000000000 : ℝ)
    (cell12230 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · have h := gap_lower (n := 12230) (a := (20589253031143 / 25000000000000 : ℝ)) (b := (84251777189 / 50000000000000 : ℝ)) (q := (144658163747 / 6250000000000 : ℝ))
      (E := (cell12230 ⟨50, by decide⟩).energy) (xi := (347251867056221 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12230 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12230]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12230])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12230) (a := (20589253031143 / 25000000000000 : ℝ)) (b := (84251777189 / 50000000000000 : ℝ)) (q := (144658163747 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12230])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12230])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12230]

theorem cert12230_51 : CellCertificate 12230 (900305438860391 / 10000000000000000 : ℝ) (34349458879233 / 20000000000000000 : ℝ) (347251867056221 / 10000000000000000 : ℝ)
    (cell12230 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · have h := gap_lower (n := 12230) (a := (82323098193393 / 100000000000000 : ℝ)) (b := (84251777189 / 50000000000000 : ℝ)) (q := (2314534622187 / 100000000000000 : ℝ))
      (E := (cell12230 ⟨51, by decide⟩).energy) (xi := (347251867056221 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12230 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12230]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12230])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12230) (a := (82323098193393 / 100000000000000 : ℝ)) (b := (84251777189 / 50000000000000 : ℝ)) (q := (2314534622187 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12230])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12230])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12230]

theorem cert12230_52 : CellCertificate 12230 (900305438860391 / 10000000000000000 : ℝ) (34349458879233 / 20000000000000000 : ℝ) (347251867056221 / 10000000000000000 : ℝ)
    (cell12230 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · have h := gap_lower (n := 12230) (a := (82289207783539 / 100000000000000 : ℝ)) (b := (84251777189 / 50000000000000 : ℝ)) (q := (2314538638121 / 100000000000000 : ℝ))
      (E := (cell12230 ⟨52, by decide⟩).energy) (xi := (347251867056221 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12230 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12230]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12230])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12230) (a := (82289207783539 / 100000000000000 : ℝ)) (b := (84251777189 / 50000000000000 : ℝ)) (q := (2314538638121 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12230])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12230])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12230]

theorem cert12230_53 : CellCertificate 12230 (900305438860391 / 10000000000000000 : ℝ) (34349458879233 / 20000000000000000 : ℝ) (347251867056221 / 10000000000000000 : ℝ)
    (cell12230 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · have h := gap_lower (n := 12230) (a := (642619850519 / 781250000000 : ℝ)) (b := (84251777189 / 50000000000000 : ℝ)) (q := (2314542606557 / 100000000000000 : ℝ))
      (E := (cell12230 ⟨53, by decide⟩).energy) (xi := (347251867056221 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12230 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12230]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12230])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12230) (a := (642619850519 / 781250000000 : ℝ)) (b := (84251777189 / 50000000000000 : ℝ)) (q := (2314542606557 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12230])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12230])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12230]

theorem cert12230_54 : CellCertificate 12230 (900305438860391 / 10000000000000000 : ℝ) (34349458879233 / 20000000000000000 : ℝ) (347251867056221 / 10000000000000000 : ℝ)
    (cell12230 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · have h := gap_lower (n := 12230) (a := (82221497413637 / 100000000000000 : ℝ)) (b := (84251777189 / 50000000000000 : ℝ)) (q := (2314546584049 / 100000000000000 : ℝ))
      (E := (cell12230 ⟨54, by decide⟩).energy) (xi := (347251867056221 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12230 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12230]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12230])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12230) (a := (82221497413637 / 100000000000000 : ℝ)) (b := (84251777189 / 50000000000000 : ℝ)) (q := (2314546584049 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12230])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12230])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12230]

theorem cert12230_55 : CellCertificate 12230 (900305438860391 / 10000000000000000 : ℝ) (34349458879233 / 20000000000000000 : ℝ) (347251867056221 / 10000000000000000 : ℝ)
    (cell12230 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · have h := gap_lower (n := 12230) (a := (82187677396863 / 100000000000000 : ℝ)) (b := (84251777189 / 50000000000000 : ℝ)) (q := (289318828379 / 12500000000000 : ℝ))
      (E := (cell12230 ⟨55, by decide⟩).energy) (xi := (347251867056221 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12230 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12230]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12230])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12230) (a := (82187677396863 / 100000000000000 : ℝ)) (b := (84251777189 / 50000000000000 : ℝ)) (q := (289318828379 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12230])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12230])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12230]

theorem cert12230_56 : CellCertificate 12230 (900305438860391 / 10000000000000000 : ℝ) (34349458879233 / 20000000000000000 : ℝ) (347251867056221 / 10000000000000000 : ℝ)
    (cell12230 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · have h := gap_lower (n := 12230) (a := (82153880787957 / 100000000000000 : ℝ)) (b := (84251777189 / 50000000000000 : ℝ)) (q := (11572773073 / 500000000000 : ℝ))
      (E := (cell12230 ⟨56, by decide⟩).energy) (xi := (347251867056221 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12230 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12230]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12230])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12230) (a := (82153880787957 / 100000000000000 : ℝ)) (b := (84251777189 / 50000000000000 : ℝ)) (q := (11572773073 / 500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12230])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12230])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12230]

theorem cert12230_57 : CellCertificate 12230 (900305438860391 / 10000000000000000 : ℝ) (34349458879233 / 20000000000000000 : ℝ) (347251867056221 / 10000000000000000 : ℝ)
    (cell12230 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · have h := gap_lower (n := 12230) (a := (82120107558913 / 100000000000000 : ℝ)) (b := (84251777189 / 50000000000000 : ℝ)) (q := (1157279301371 / 50000000000000 : ℝ))
      (E := (cell12230 ⟨57, by decide⟩).energy) (xi := (347251867056221 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12230 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12230]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12230])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12230) (a := (82120107558913 / 100000000000000 : ℝ)) (b := (84251777189 / 50000000000000 : ℝ)) (q := (1157279301371 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12230])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12230])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12230]

theorem cert12230_58 : CellCertificate 12230 (900305438860391 / 10000000000000000 : ℝ) (34349458879233 / 20000000000000000 : ℝ) (347251867056221 / 10000000000000000 : ℝ)
    (cell12230 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · have h := gap_lower (n := 12230) (a := (82086357681859 / 100000000000000 : ℝ)) (b := (84251777189 / 50000000000000 : ℝ)) (q := (289320323527 / 12500000000000 : ℝ))
      (E := (cell12230 ⟨58, by decide⟩).energy) (xi := (347251867056221 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12230 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12230]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12230])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12230) (a := (82086357681859 / 100000000000000 : ℝ)) (b := (84251777189 / 50000000000000 : ℝ)) (q := (289320323527 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12230])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12230])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12230]

theorem cert12230_59 : CellCertificate 12230 (900305438860391 / 10000000000000000 : ℝ) (34349458879233 / 20000000000000000 : ℝ) (347251867056221 / 10000000000000000 : ℝ)
    (cell12230 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · have h := gap_lower (n := 12230) (a := (20513157782267 / 25000000000000 : ℝ)) (b := (84251777189 / 50000000000000 : ℝ)) (q := (2314566567563 / 100000000000000 : ℝ))
      (E := (cell12230 ⟨59, by decide⟩).energy) (xi := (347251867056221 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12230 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12230]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12230])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12230) (a := (20513157782267 / 25000000000000 : ℝ)) (b := (84251777189 / 50000000000000 : ℝ)) (q := (2314566567563 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12230])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12230])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12230]

theorem cert12231_40 : CellCertificate 12231 (225068850577927 / 2500000000000000 : ℝ) (214666559544533 / 125000000000000000 : ℝ) (17361135550939 / 500000000000000 : ℝ)
    (cell12231 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · have h := gap_lower (n := 12231) (a := (82697448390427 / 100000000000000 : ℝ)) (b := (168489592031 / 100000000000000 : ℝ)) (q := (2314341695411 / 100000000000000 : ℝ))
      (E := (cell12231 ⟨40, by decide⟩).energy) (xi := (17361135550939 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12231 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12231]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12231])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12231) (a := (82697448390427 / 100000000000000 : ℝ)) (b := (168489592031 / 100000000000000 : ℝ)) (q := (2314341695411 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12231])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12231])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12231]

theorem cert12231_41 : CellCertificate 12231 (225068850577927 / 2500000000000000 : ℝ) (214666559544533 / 125000000000000000 : ℝ) (17361135550939 / 500000000000000 : ℝ)
    (cell12231 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · have h := gap_lower (n := 12231) (a := (20665824490693 / 25000000000000 : ℝ)) (b := (168489592031 / 100000000000000 : ℝ)) (q := (1157172843409 / 50000000000000 : ℝ))
      (E := (cell12231 ⟨41, by decide⟩).energy) (xi := (17361135550939 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12231 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12231]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12231])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12231) (a := (20665824490693 / 25000000000000 : ℝ)) (b := (168489592031 / 100000000000000 : ℝ)) (q := (1157172843409 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12231])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12231])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12231]

theorem cert12231_42 : CellCertificate 12231 (225068850577927 / 2500000000000000 : ℝ) (214666559544533 / 125000000000000000 : ℝ) (17361135550939 / 500000000000000 : ℝ)
    (cell12231 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · have h := gap_lower (n := 12231) (a := (41314585674929 / 50000000000000 : ℝ)) (b := (168489592031 / 100000000000000 : ℝ)) (q := (2314349644161 / 100000000000000 : ℝ))
      (E := (cell12231 ⟨42, by decide⟩).energy) (xi := (17361135550939 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12231 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12231]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12231])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12231) (a := (41314585674929 / 50000000000000 : ℝ)) (b := (168489592031 / 100000000000000 : ℝ)) (q := (2314349644161 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12231])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12231])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12231]

theorem cert12231_43 : CellCertificate 12231 (225068850577927 / 2500000000000000 : ℝ) (214666559544533 / 125000000000000000 : ℝ) (17361135550939 / 500000000000000 : ℝ)
    (cell12231 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · have h := gap_lower (n := 12231) (a := (82595068521627 / 100000000000000 : ℝ)) (b := (168489592031 / 100000000000000 : ℝ)) (q := (2314353684881 / 100000000000000 : ℝ))
      (E := (cell12231 ⟨43, by decide⟩).energy) (xi := (17361135550939 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12231 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12231]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12231])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12231) (a := (82595068521627 / 100000000000000 : ℝ)) (b := (168489592031 / 100000000000000 : ℝ)) (q := (2314353684881 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12231])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12231])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12231]

theorem cert12231_44 : CellCertificate 12231 (225068850577927 / 2500000000000000 : ℝ) (214666559544533 / 125000000000000000 : ℝ) (17361135550939 / 500000000000000 : ℝ)
    (cell12231 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · have h := gap_lower (n := 12231) (a := (82560989448171 / 100000000000000 : ℝ)) (b := (168489592031 / 100000000000000 : ℝ)) (q := (462871538243 / 20000000000000 : ℝ))
      (E := (cell12231 ⟨44, by decide⟩).energy) (xi := (17361135550939 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12231 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12231]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12231])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12231) (a := (82560989448171 / 100000000000000 : ℝ)) (b := (168489592031 / 100000000000000 : ℝ)) (q := (462871538243 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12231])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12231])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12231]

theorem cert12231_45 : CellCertificate 12231 (225068850577927 / 2500000000000000 : ℝ) (214666559544533 / 125000000000000000 : ℝ) (17361135550939 / 500000000000000 : ℝ)
    (cell12231 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · have h := gap_lower (n := 12231) (a := (16505386819947 / 20000000000000 : ℝ)) (b := (168489592031 / 100000000000000 : ℝ)) (q := (2314361662627 / 100000000000000 : ℝ))
      (E := (cell12231 ⟨45, by decide⟩).energy) (xi := (17361135550939 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12231 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12231]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12231])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12231) (a := (16505386819947 / 20000000000000 : ℝ)) (b := (168489592031 / 100000000000000 : ℝ)) (q := (2314361662627 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12231])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12231])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12231]

theorem cert12231_46 : CellCertificate 12231 (225068850577927 / 2500000000000000 : ℝ) (214666559544533 / 125000000000000000 : ℝ) (17361135550939 / 500000000000000 : ℝ)
    (cell12231 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · have h := gap_lower (n := 12231) (a := (10311612805839 / 12500000000000 : ℝ)) (b := (168489592031 / 100000000000000 : ℝ)) (q := (1157182828601 / 50000000000000 : ℝ))
      (E := (cell12231 ⟨46, by decide⟩).energy) (xi := (17361135550939 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12231 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12231]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12231])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12231) (a := (10311612805839 / 12500000000000 : ℝ)) (b := (168489592031 / 100000000000000 : ℝ)) (q := (1157182828601 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12231])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12231])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12231]

theorem cert12231_47 : CellCertificate 12231 (225068850577927 / 2500000000000000 : ℝ) (214666559544533 / 125000000000000000 : ℝ) (17361135550939 / 500000000000000 : ℝ)
    (cell12231 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · have h := gap_lower (n := 12231) (a := (322105056483 / 390625000000 : ℝ)) (b := (168489592031 / 100000000000000 : ℝ)) (q := (462873934807 / 20000000000000 : ℝ))
      (E := (cell12231 ⟨47, by decide⟩).energy) (xi := (17361135550939 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12231 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12231]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12231])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12231) (a := (322105056483 / 390625000000 : ℝ)) (b := (168489592031 / 100000000000000 : ℝ)) (q := (462873934807 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12231])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12231])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12231]

theorem cert12231_48 : CellCertificate 12231 (225068850577927 / 2500000000000000 : ℝ) (214666559544533 / 125000000000000000 : ℝ) (17361135550939 / 500000000000000 : ℝ)
    (cell12231 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · have h := gap_lower (n := 12231) (a := (82424910109233 / 100000000000000 : ℝ)) (b := (168489592031 / 100000000000000 : ℝ)) (q := (2314373653123 / 100000000000000 : ℝ))
      (E := (cell12231 ⟨48, by decide⟩).energy) (xi := (17361135550939 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12231 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12231]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12231])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12231) (a := (82424910109233 / 100000000000000 : ℝ)) (b := (168489592031 / 100000000000000 : ℝ)) (q := (2314373653123 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12231])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12231])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12231]

theorem cert12231_49 : CellCertificate 12231 (225068850577927 / 2500000000000000 : ℝ) (214666559544533 / 125000000000000000 : ℝ) (17361135550939 / 500000000000000 : ℝ)
    (cell12231 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · have h := gap_lower (n := 12231) (a := (20597737341577 / 25000000000000 : ℝ)) (b := (168489592031 / 100000000000000 : ℝ)) (q := (2314377651967 / 100000000000000 : ℝ))
      (E := (cell12231 ⟨49, by decide⟩).energy) (xi := (17361135550939 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12231 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12231]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12231])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12231) (a := (20597737341577 / 25000000000000 : ℝ)) (b := (168489592031 / 100000000000000 : ℝ)) (q := (2314377651967 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12231])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12231])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12231]

theorem cert12231_50 : CellCertificate 12231 (225068850577927 / 2500000000000000 : ℝ) (214666559544533 / 125000000000000000 : ℝ) (17361135550939 / 500000000000000 : ℝ)
    (cell12231 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · have h := gap_lower (n := 12231) (a := (82357012201861 / 100000000000000 : ℝ)) (b := (168489592031 / 100000000000000 : ℝ)) (q := (1157190805041 / 50000000000000 : ℝ))
      (E := (cell12231 ⟨50, by decide⟩).energy) (xi := (17361135550939 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12231 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12231]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12231])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12231) (a := (82357012201861 / 100000000000000 : ℝ)) (b := (168489592031 / 100000000000000 : ℝ)) (q := (1157190805041 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12231])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12231])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12231]

theorem cert12231_51 : CellCertificate 12231 (225068850577927 / 2500000000000000 : ℝ) (214666559544533 / 125000000000000000 : ℝ) (17361135550939 / 500000000000000 : ℝ)
    (cell12231 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · have h := gap_lower (n := 12231) (a := (5145193661689 / 6250000000000 : ℝ)) (b := (168489592031 / 100000000000000 : ℝ)) (q := (2314385643547 / 100000000000000 : ℝ))
      (E := (cell12231 ⟨51, by decide⟩).energy) (xi := (17361135550939 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12231 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12231]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12231])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12231) (a := (5145193661689 / 6250000000000 : ℝ)) (b := (168489592031 / 100000000000000 : ℝ)) (q := (2314385643547 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12231])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12231])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12231]

theorem cert12231_52 : CellCertificate 12231 (225068850577927 / 2500000000000000 : ℝ) (214666559544533 / 125000000000000000 : ℝ) (17361135550939 / 500000000000000 : ℝ)
    (cell12231 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · have h := gap_lower (n := 12231) (a := (20572302123269 / 25000000000000 : ℝ)) (b := (168489592031 / 100000000000000 : ℝ)) (q := (231438963249 / 10000000000000 : ℝ))
      (E := (cell12231 ⟨52, by decide⟩).energy) (xi := (17361135550939 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12231 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12231]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12231])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12231) (a := (20572302123269 / 25000000000000 : ℝ)) (b := (168489592031 / 100000000000000 : ℝ)) (q := (231438963249 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12231])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12231])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12231]

theorem cert12231_53 : CellCertificate 12231 (225068850577927 / 2500000000000000 : ℝ) (214666559544533 / 125000000000000000 : ℝ) (17361135550939 / 500000000000000 : ℝ)
    (cell12231 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · have h := gap_lower (n := 12231) (a := (82255341891439 / 100000000000000 : ℝ)) (b := (168489592031 / 100000000000000 : ℝ)) (q := (2314393633651 / 100000000000000 : ℝ))
      (E := (cell12231 ⟨53, by decide⟩).energy) (xi := (17361135550939 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12231 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12231]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12231])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12231) (a := (82255341891439 / 100000000000000 : ℝ)) (b := (168489592031 / 100000000000000 : ℝ)) (q := (2314393633651 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12231])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12231])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12231]

theorem cert12231_54 : CellCertificate 12231 (225068850577927 / 2500000000000000 : ℝ) (214666559544533 / 125000000000000000 : ℝ) (17361135550939 / 500000000000000 : ℝ)
    (cell12231 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · have h := gap_lower (n := 12231) (a := (82221498753679 / 100000000000000 : ℝ)) (b := (168489592031 / 100000000000000 : ℝ)) (q := (2314397644627 / 100000000000000 : ℝ))
      (E := (cell12231 ⟨54, by decide⟩).energy) (xi := (17361135550939 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12231 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12231]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12231])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12231) (a := (82221498753679 / 100000000000000 : ℝ)) (b := (168489592031 / 100000000000000 : ℝ)) (q := (2314397644627 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12231])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12231])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12231]

theorem cert12231_55 : CellCertificate 12231 (225068850577927 / 2500000000000000 : ℝ) (214666559544533 / 125000000000000000 : ℝ) (17361135550939 / 500000000000000 : ℝ)
    (cell12231 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · have h := gap_lower (n := 12231) (a := (16437535810301 / 20000000000000 : ℝ)) (b := (168489592031 / 100000000000000 : ℝ)) (q := (1157200801873 / 50000000000000 : ℝ))
      (E := (cell12231 ⟨55, by decide⟩).energy) (xi := (17361135550939 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12231 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12231]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12231])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12231) (a := (16437535810301 / 20000000000000 : ℝ)) (b := (168489592031 / 100000000000000 : ℝ)) (q := (1157200801873 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12231])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12231])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12231]

theorem cert12231_56 : CellCertificate 12231 (225068850577927 / 2500000000000000 : ℝ) (214666559544533 / 125000000000000000 : ℝ) (17361135550939 / 500000000000000 : ℝ)
    (cell12231 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · have h := gap_lower (n := 12231) (a := (41076941378383 / 50000000000000 : ℝ)) (b := (168489592031 / 100000000000000 : ℝ)) (q := (462881125253 / 20000000000000 : ℝ))
      (E := (cell12231 ⟨56, by decide⟩).energy) (xi := (17361135550939 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12231 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12231]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12231])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12231) (a := (41076941378383 / 50000000000000 : ℝ)) (b := (168489592031 / 100000000000000 : ℝ)) (q := (462881125253 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12231])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12231])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12231]

theorem cert12231_57 : CellCertificate 12231 (225068850577927 / 2500000000000000 : ℝ) (214666559544533 / 125000000000000000 : ℝ) (17361135550939 / 500000000000000 : ℝ)
    (cell12231 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · have h := gap_lower (n := 12231) (a := (5132506865091 / 6250000000000 : ℝ)) (b := (168489592031 / 100000000000000 : ℝ)) (q := (462881918203 / 20000000000000 : ℝ))
      (E := (cell12231 ⟨57, by decide⟩).energy) (xi := (17361135550939 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12231 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12231]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12231])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12231) (a := (5132506865091 / 6250000000000 : ℝ)) (b := (168489592031 / 100000000000000 : ℝ)) (q := (462881918203 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12231])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12231])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12231]

theorem cert12231_58 : CellCertificate 12231 (225068850577927 / 2500000000000000 : ℝ) (214666559544533 / 125000000000000000 : ℝ) (17361135550939 / 500000000000000 : ℝ)
    (cell12231 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · have h := gap_lower (n := 12231) (a := (16417272055541 / 20000000000000 : ℝ)) (b := (168489592031 / 100000000000000 : ℝ)) (q := (1157206806463 / 50000000000000 : ℝ))
      (E := (cell12231 ⟨58, by decide⟩).energy) (xi := (17361135550939 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12231 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12231]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12231])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12231) (a := (16417272055541 / 20000000000000 : ℝ)) (b := (168489592031 / 100000000000000 : ℝ)) (q := (1157206806463 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12231])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12231])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12231]

theorem cert12231_59 : CellCertificate 12231 (225068850577927 / 2500000000000000 : ℝ) (214666559544533 / 125000000000000000 : ℝ) (17361135550939 / 500000000000000 : ℝ)
    (cell12231 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · have h := gap_lower (n := 12231) (a := (10256579254723 / 12500000000000 : ℝ)) (b := (168489592031 / 100000000000000 : ℝ)) (q := (2314417570321 / 100000000000000 : ℝ))
      (E := (cell12231 ⟨59, by decide⟩).energy) (xi := (17361135550939 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12231 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12231]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12231])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12231) (a := (10256579254723 / 12500000000000 : ℝ)) (b := (168489592031 / 100000000000000 : ℝ)) (q := (2314417570321 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12231])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12231])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12231]

theorem cert12232_40 : CellCertificate 12232 (450122685248117 / 5000000000000000 : ℝ) (13415562747859 / 7812500000000000 : ℝ) (347193560006361 / 10000000000000000 : ℝ)
    (cell12232 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · have h := gap_lower (n := 12232) (a := (82697445281123 / 100000000000000 : ℝ)) (b := (16847563203 / 10000000000000 : ℝ)) (q := (231419276369 / 10000000000000 : ℝ))
      (E := (cell12232 ⟨40, by decide⟩).energy) (xi := (347193560006361 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12232 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12232]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12232])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12232) (a := (82697445281123 / 100000000000000 : ℝ)) (b := (16847563203 / 10000000000000 : ℝ)) (q := (231419276369 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12232])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12232])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12232]

theorem cert12232_41 : CellCertificate 12232 (450122685248117 / 5000000000000000 : ℝ) (13415562747859 / 7812500000000000 : ℝ) (347193560006361 / 10000000000000000 : ℝ)
    (cell12232 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · have h := gap_lower (n := 12232) (a := (82663295174177 / 100000000000000 : ℝ)) (b := (16847563203 / 10000000000000 : ℝ)) (q := (18513574231 / 800000000000 : ℝ))
      (E := (cell12232 ⟨41, by decide⟩).energy) (xi := (347193560006361 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12232 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12232]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12232])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12232) (a := (82663295174177 / 100000000000000 : ℝ)) (b := (16847563203 / 10000000000000 : ℝ)) (q := (18513574231 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12232])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12232])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12232]

theorem cert12232_42 : CellCertificate 12232 (450122685248117 / 5000000000000000 : ℝ) (13415562747859 / 7812500000000000 : ℝ) (347193560006361 / 10000000000000000 : ℝ)
    (cell12232 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · have h := gap_lower (n := 12232) (a := (10328646110191 / 12500000000000 : ℝ)) (b := (16847563203 / 10000000000000 : ℝ)) (q := (2314200760763 / 100000000000000 : ℝ))
      (E := (cell12232 ⟨42, by decide⟩).energy) (xi := (347193560006361 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12232 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12232]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12232])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12232) (a := (10328646110191 / 12500000000000 : ℝ)) (b := (16847563203 / 10000000000000 : ℝ)) (q := (2314200760763 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12232])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12232])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12232]

theorem cert12232_43 : CellCertificate 12232 (450122685248117 / 5000000000000000 : ℝ) (13415562747859 / 7812500000000000 : ℝ) (347193560006361 / 10000000000000000 : ℝ)
    (cell12232 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · have h := gap_lower (n := 12232) (a := (82595066373119 / 100000000000000 : ℝ)) (b := (16847563203 / 10000000000000 : ℝ)) (q := (2314204768023 / 100000000000000 : ℝ))
      (E := (cell12232 ⟨43, by decide⟩).energy) (xi := (347193560006361 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12232 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12232]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12232])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12232) (a := (82595066373119 / 100000000000000 : ℝ)) (b := (16847563203 / 10000000000000 : ℝ)) (q := (2314204768023 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12232])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12232])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12232]

theorem cert12232_44 : CellCertificate 12232 (450122685248117 / 5000000000000000 : ℝ) (13415562747859 / 7812500000000000 : ℝ) (347193560006361 / 10000000000000000 : ℝ)
    (cell12232 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · have h := gap_lower (n := 12232) (a := (82560987619043 / 100000000000000 : ℝ)) (b := (16847563203 / 10000000000000 : ℝ)) (q := (462841748323 / 20000000000000 : ℝ))
      (E := (cell12232 ⟨44, by decide⟩).energy) (xi := (347193560006361 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12232 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12232]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12232])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12232) (a := (82560987619043 / 100000000000000 : ℝ)) (b := (16847563203 / 10000000000000 : ℝ)) (q := (462841748323 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12232])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12232])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12232]

theorem cert12232_45 : CellCertificate 12232 (450122685248117 / 5000000000000000 : ℝ) (13415562747859 / 7812500000000000 : ℝ) (347193560006361 / 10000000000000000 : ℝ)
    (cell12232 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · have h := gap_lower (n := 12232) (a := (82526932589543 / 100000000000000 : ℝ)) (b := (16847563203 / 10000000000000 : ℝ)) (q := (2314212739821 / 100000000000000 : ℝ))
      (E := (cell12232 ⟨45, by decide⟩).energy) (xi := (347193560006361 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12232 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12232]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12232])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12232) (a := (82526932589543 / 100000000000000 : ℝ)) (b := (16847563203 / 10000000000000 : ℝ)) (q := (2314212739821 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12232])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12232])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12232]

theorem cert12232_46 : CellCertificate 12232 (450122685248117 / 5000000000000000 : ℝ) (13415562747859 / 7812500000000000 : ℝ) (347193560006361 / 10000000000000000 : ℝ)
    (cell12232 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · have h := gap_lower (n := 12232) (a := (82492901255017 / 100000000000000 : ℝ)) (b := (16847563203 / 10000000000000 : ℝ)) (q := (2314216761953 / 100000000000000 : ℝ))
      (E := (cell12232 ⟨46, by decide⟩).energy) (xi := (347193560006361 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12232 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12232]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12232])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12232) (a := (82492901255017 / 100000000000000 : ℝ)) (b := (16847563203 / 10000000000000 : ℝ)) (q := (2314216761953 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12232])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12232])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12232]

theorem cert12232_47 : CellCertificate 12232 (450122685248117 / 5000000000000000 : ℝ) (13415562747859 / 7812500000000000 : ℝ) (347193560006361 / 10000000000000000 : ℝ)
    (cell12232 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · have h := gap_lower (n := 12232) (a := (10307361698251 / 12500000000000 : ℝ)) (b := (16847563203 / 10000000000000 : ℝ)) (q := (578555187061 / 25000000000000 : ℝ))
      (E := (cell12232 ⟨47, by decide⟩).energy) (xi := (347193560006361 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12232 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12232]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12232])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12232) (a := (10307361698251 / 12500000000000 : ℝ)) (b := (16847563203 / 10000000000000 : ℝ)) (q := (578555187061 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12232])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12232])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12232]

theorem cert12232_48 : CellCertificate 12232 (450122685248117 / 5000000000000000 : ℝ) (13415562747859 / 7812500000000000 : ℝ) (347193560006361 / 10000000000000000 : ℝ)
    (cell12232 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · have h := gap_lower (n := 12232) (a := (82424909553209 / 100000000000000 : ℝ)) (b := (16847563203 / 10000000000000 : ℝ)) (q := (2314224756391 / 100000000000000 : ℝ))
      (E := (cell12232 ⟨48, by decide⟩).energy) (xi := (347193560006361 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12232 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12232]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12232])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12232) (a := (82424909553209 / 100000000000000 : ℝ)) (b := (16847563203 / 10000000000000 : ℝ)) (q := (2314224756391 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12232])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12232])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12232]

theorem cert12232_49 : CellCertificate 12232 (450122685248117 / 5000000000000000 : ℝ) (13415562747859 / 7812500000000000 : ℝ) (347193560006361 / 10000000000000000 : ℝ)
    (cell12232 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · have h := gap_lower (n := 12232) (a := (41195474563731 / 50000000000000 : ℝ)) (b := (16847563203 / 10000000000000 : ℝ)) (q := (462845745229 / 20000000000000 : ℝ))
      (E := (cell12232 ⟨49, by decide⟩).energy) (xi := (347193560006361 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12232 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12232]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12232])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12232) (a := (41195474563731 / 50000000000000 : ℝ)) (b := (16847563203 / 10000000000000 : ℝ)) (q := (462845745229 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12232])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12232])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12232]

theorem cert12232_50 : CellCertificate 12232 (450122685248117 / 5000000000000000 : ℝ) (13415562747859 / 7812500000000000 : ℝ) (347193560006361 / 10000000000000000 : ℝ)
    (cell12232 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · have h := gap_lower (n := 12232) (a := (41178506139877 / 50000000000000 : ℝ)) (b := (16847563203 / 10000000000000 : ℝ)) (q := (1157116357409 / 50000000000000 : ℝ))
      (E := (cell12232 ⟨50, by decide⟩).energy) (xi := (347193560006361 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12232 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12232]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12232])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12232) (a := (41178506139877 / 50000000000000 : ℝ)) (b := (16847563203 / 10000000000000 : ℝ)) (q := (1157116357409 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12232])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12232])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12232]

theorem cert12232_51 : CellCertificate 12232 (450122685248117 / 5000000000000000 : ℝ) (13415562747859 / 7812500000000000 : ℝ) (347193560006361 / 10000000000000000 : ℝ)
    (cell12232 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · have h := gap_lower (n := 12232) (a := (4116154949061 / 5000000000000 : ℝ)) (b := (16847563203 / 10000000000000 : ℝ)) (q := (2314236720643 / 100000000000000 : ℝ))
      (E := (cell12232 ⟨51, by decide⟩).energy) (xi := (347193560006361 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12232 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12232]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12232])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12232) (a := (4116154949061 / 5000000000000 : ℝ)) (b := (16847563203 / 10000000000000 : ℝ)) (q := (2314236720643 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12232])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12232])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12232]

theorem cert12232_52 : CellCertificate 12232 (450122685248117 / 5000000000000000 : ℝ) (13415562747859 / 7812500000000000 : ℝ) (347193560006361 / 10000000000000000 : ℝ)
    (cell12232 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · have h := gap_lower (n := 12232) (a := (82289209203137 / 100000000000000 : ℝ)) (b := (16847563203 / 10000000000000 : ℝ)) (q := (2314240741641 / 100000000000000 : ℝ))
      (E := (cell12232 ⟨52, by decide⟩).energy) (xi := (347193560006361 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12232 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12232]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12232])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12232) (a := (82289209203137 / 100000000000000 : ℝ)) (b := (16847563203 / 10000000000000 : ℝ)) (q := (2314240741641 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12232])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12232])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12232]

theorem cert12232_53 : CellCertificate 12232 (450122685248117 / 5000000000000000 : ℝ) (13415562747859 / 7812500000000000 : ℝ) (347193560006361 / 10000000000000000 : ℝ)
    (cell12232 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · have h := gap_lower (n := 12232) (a := (8225534291693 / 10000000000000 : ℝ)) (b := (16847563203 / 10000000000000 : ℝ)) (q := (2314244716611 / 100000000000000 : ℝ))
      (E := (cell12232 ⟨53, by decide⟩).energy) (xi := (347193560006361 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12232 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12232]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12232])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12232) (a := (8225534291693 / 10000000000000 : ℝ)) (b := (16847563203 / 10000000000000 : ℝ)) (q := (2314244716611 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12232])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12232])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12232]

theorem cert12232_54 : CellCertificate 12232 (450122685248117 / 5000000000000000 : ℝ) (13415562747859 / 7812500000000000 : ℝ) (347193560006361 / 10000000000000000 : ℝ)
    (cell12232 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · have h := gap_lower (n := 12232) (a := (41110750047083 / 50000000000000 : ℝ)) (b := (16847563203 / 10000000000000 : ℝ)) (q := (462849740421 / 20000000000000 : ℝ))
      (E := (cell12232 ⟨54, by decide⟩).energy) (xi := (347193560006361 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12232 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12232]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12232])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12232) (a := (41110750047083 / 50000000000000 : ℝ)) (b := (16847563203 / 10000000000000 : ℝ)) (q := (462849740421 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12232])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12232])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12232]

theorem cert12232_55 : CellCertificate 12232 (450122685248117 / 5000000000000000 : ℝ) (13415562747859 / 7812500000000000 : ℝ) (347193560006361 / 10000000000000000 : ℝ)
    (cell12232 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · have h := gap_lower (n := 12232) (a := (10273460088319 / 12500000000000 : ℝ)) (b := (16847563203 / 10000000000000 : ℝ)) (q := (2314252695507 / 100000000000000 : ℝ))
      (E := (cell12232 ⟨55, by decide⟩).energy) (xi := (347193560006361 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12232 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12232]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12232])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12232) (a := (10273460088319 / 12500000000000 : ℝ)) (b := (16847563203 / 10000000000000 : ℝ)) (q := (2314252695507 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12232])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12232])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12232]

theorem cert12232_56 : CellCertificate 12232 (450122685248117 / 5000000000000000 : ℝ) (13415562747859 / 7812500000000000 : ℝ) (347193560006361 / 10000000000000000 : ℝ)
    (cell12232 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · have h := gap_lower (n := 12232) (a := (41076942362971 / 50000000000000 : ℝ)) (b := (16847563203 / 10000000000000 : ℝ)) (q := (2314256693987 / 100000000000000 : ℝ))
      (E := (cell12232 ⟨56, by decide⟩).energy) (xi := (347193560006361 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12232 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12232]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12232])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12232) (a := (41076942362971 / 50000000000000 : ℝ)) (b := (16847563203 / 10000000000000 : ℝ)) (q := (2314256693987 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12232])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12232])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12232]

theorem cert12232_57 : CellCertificate 12232 (450122685248117 / 5000000000000000 : ℝ) (13415562747859 / 7812500000000000 : ℝ) (347193560006361 / 10000000000000000 : ℝ)
    (cell12232 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · have h := gap_lower (n := 12232) (a := (41060056062163 / 50000000000000 : ℝ)) (b := (16847563203 / 10000000000000 : ℝ)) (q := (578565173627 / 25000000000000 : ℝ))
      (E := (cell12232 ⟨57, by decide⟩).energy) (xi := (347193560006361 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12232 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12232]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12232])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12232) (a := (41060056062163 / 50000000000000 : ℝ)) (b := (16847563203 / 10000000000000 : ℝ)) (q := (578565173627 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12232])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12232])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12232]

theorem cert12232_58 : CellCertificate 12232 (450122685248117 / 5000000000000000 : ℝ) (13415562747859 / 7812500000000000 : ℝ) (347193560006361 / 10000000000000000 : ℝ)
    (cell12232 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · have h := gap_lower (n := 12232) (a := (41043181436919 / 50000000000000 : ℝ)) (b := (16847563203 / 10000000000000 : ℝ)) (q := (2314264693823 / 100000000000000 : ℝ))
      (E := (cell12232 ⟨58, by decide⟩).energy) (xi := (347193560006361 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12232 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12232]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12232])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12232) (a := (41043181436919 / 50000000000000 : ℝ)) (b := (16847563203 / 10000000000000 : ℝ)) (q := (2314264693823 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12232])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12232])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12232]

theorem cert12232_59 : CellCertificate 12232 (450122685248117 / 5000000000000000 : ℝ) (13415562747859 / 7812500000000000 : ℝ) (347193560006361 / 10000000000000000 : ℝ)
    (cell12232 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · have h := gap_lower (n := 12232) (a := (20513159236687 / 25000000000000 : ℝ)) (b := (16847563203 / 10000000000000 : ℝ)) (q := (578567172119 / 25000000000000 : ℝ))
      (E := (cell12232 ⟨59, by decide⟩).energy) (xi := (347193560006361 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12232 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12232]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12232])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12232) (a := (20513159236687 / 25000000000000 : ℝ)) (b := (16847563203 / 10000000000000 : ℝ)) (q := (578567172119 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12232])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12232])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12232]

theorem cert12233_40 : CellCertificate 12233 (900215343412797 / 10000000000000000 : ℝ) (68682064402603 / 40000000000000000 : ℝ) (86791103504371 / 2500000000000000 : ℝ)
    (cell12233 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · have h := gap_lower (n := 12233) (a := (82697442172823 / 100000000000000 : ℝ)) (b := (84230837187 / 50000000000000 : ℝ)) (q := (462808800879 / 20000000000000 : ℝ))
      (E := (cell12233 ⟨40, by decide⟩).energy) (xi := (86791103504371 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12233 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12233]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12233])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12233) (a := (82697442172823 / 100000000000000 : ℝ)) (b := (84230837187 / 50000000000000 : ℝ)) (q := (462808800879 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12233])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12233])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12233]

theorem cert12233_41 : CellCertificate 12233 (900215343412797 / 10000000000000000 : ℝ) (68682064402603 / 40000000000000000 : ℝ) (86791103504371 / 2500000000000000 : ℝ)
    (cell12233 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · have h := gap_lower (n := 12233) (a := (41331646193273 / 50000000000000 : ℝ)) (b := (84230837187 / 50000000000000 : ℝ)) (q := (2314047984747 / 100000000000000 : ℝ))
      (E := (cell12233 ⟨41, by decide⟩).energy) (xi := (86791103504371 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12233 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12233]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12233])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12233) (a := (41331646193273 / 50000000000000 : ℝ)) (b := (84230837187 / 50000000000000 : ℝ)) (q := (2314047984747 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12233])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12233])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12233]

theorem cert12233_42 : CellCertificate 12233 (900215343412797 / 10000000000000000 : ℝ) (68682064402603 / 40000000000000000 : ℝ) (86791103504371 / 2500000000000000 : ℝ)
    (cell12233 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · have h := gap_lower (n := 12233) (a := (82629166414123 / 100000000000000 : ℝ)) (b := (84230837187 / 50000000000000 : ℝ)) (q := (1157025995633 / 50000000000000 : ℝ))
      (E := (cell12233 ⟨42, by decide⟩).energy) (xi := (86791103504371 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12233 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12233]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12233])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12233) (a := (82629166414123 / 100000000000000 : ℝ)) (b := (84230837187 / 50000000000000 : ℝ)) (q := (1157025995633 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12233])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12233])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12233]

theorem cert12233_43 : CellCertificate 12233 (900215343412797 / 10000000000000000 : ℝ) (68682064402603 / 40000000000000000 : ℝ) (86791103504371 / 2500000000000000 : ℝ)
    (cell12233 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · have h := gap_lower (n := 12233) (a := (16519012845099 / 20000000000000 : ℝ)) (b := (84230837187 / 50000000000000 : ℝ)) (q := (462811193031 / 20000000000000 : ℝ))
      (E := (cell12233 ⟨43, by decide⟩).energy) (xi := (86791103504371 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12233 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12233]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12233])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12233) (a := (16519012845099 / 20000000000000 : ℝ)) (b := (84230837187 / 50000000000000 : ℝ)) (q := (462811193031 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12233])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12233])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12233]

theorem cert12233_44 : CellCertificate 12233 (900215343412797 / 10000000000000000 : ℝ) (68682064402603 / 40000000000000000 : ℝ) (86791103504371 / 2500000000000000 : ℝ)
    (cell12233 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · have h := gap_lower (n := 12233) (a := (82560985790757 / 100000000000000 : ℝ)) (b := (84230837187 / 50000000000000 : ℝ)) (q := (2314059964889 / 100000000000000 : ℝ))
      (E := (cell12233 ⟨44, by decide⟩).energy) (xi := (86791103504371 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12233 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12233]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12233])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12233) (a := (82560985790757 / 100000000000000 : ℝ)) (b := (84230837187 / 50000000000000 : ℝ)) (q := (2314059964889 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12233])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12233])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12233]

theorem cert12233_45 : CellCertificate 12233 (900215343412797 / 10000000000000000 : ℝ) (68682064402603 / 40000000000000000 : ℝ) (86791103504371 / 2500000000000000 : ℝ)
    (cell12233 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · have h := gap_lower (n := 12233) (a := (16505386216031 / 20000000000000 : ℝ)) (b := (84230837187 / 50000000000000 : ℝ)) (q := (2314063931183 / 100000000000000 : ℝ))
      (E := (cell12233 ⟨45, by decide⟩).energy) (xi := (86791103504371 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12233 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12233]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12233])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12233) (a := (16505386216031 / 20000000000000 : ℝ)) (b := (84230837187 / 50000000000000 : ℝ)) (q := (2314063931183 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12233])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12233])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12233]

theorem cert12233_46 : CellCertificate 12233 (900215343412797 / 10000000000000000 : ℝ) (68682064402603 / 40000000000000000 : ℝ) (86791103504371 / 2500000000000000 : ℝ)
    (cell12233 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · have h := gap_lower (n := 12233) (a := (16498580012817 / 20000000000000 : ℝ)) (b := (84230837187 / 50000000000000 : ℝ)) (q := (14462924881 / 625000000000 : ℝ))
      (E := (cell12233 ⟨46, by decide⟩).energy) (xi := (86791103504371 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12233 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12233]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12233])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12233) (a := (16498580012817 / 20000000000000 : ℝ)) (b := (84230837187 / 50000000000000 : ℝ)) (q := (14462924881 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12233])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12233])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12233]

theorem cert12233_47 : CellCertificate 12233 (900215343412797 / 10000000000000000 : ℝ) (68682064402603 / 40000000000000000 : ℝ) (86791103504371 / 2500000000000000 : ℝ)
    (cell12233 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · have h := gap_lower (n := 12233) (a := (82458892713091 / 100000000000000 : ℝ)) (b := (84230837187 / 50000000000000 : ℝ)) (q := (578517984199 / 25000000000000 : ℝ))
      (E := (cell12233 ⟨47, by decide⟩).energy) (xi := (86791103504371 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12233 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12233]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12233])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12233) (a := (82458892713091 / 100000000000000 : ℝ)) (b := (84230837187 / 50000000000000 : ℝ)) (q := (578517984199 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12233])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12233])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12233]

theorem cert12233_48 : CellCertificate 12233 (900215343412797 / 10000000000000000 : ℝ) (68682064402603 / 40000000000000000 : ℝ) (86791103504371 / 2500000000000000 : ℝ)
    (cell12233 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · have h := gap_lower (n := 12233) (a := (82424908997869 / 100000000000000 : ℝ)) (b := (84230837187 / 50000000000000 : ℝ)) (q := (2314075915203 / 100000000000000 : ℝ))
      (E := (cell12233 ⟨48, by decide⟩).energy) (xi := (86791103504371 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12233 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12233]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12233])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12233) (a := (82424908997869 / 100000000000000 : ℝ)) (b := (84230837187 / 50000000000000 : ℝ)) (q := (2314075915203 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12233])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12233])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12233]

theorem cert12233_49 : CellCertificate 12233 (900215343412797 / 10000000000000000 : ℝ) (68682064402603 / 40000000000000000 : ℝ) (86791103504371 / 2500000000000000 : ℝ)
    (cell12233 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · have h := gap_lower (n := 12233) (a := (82390948889259 / 100000000000000 : ℝ)) (b := (84230837187 / 50000000000000 : ℝ)) (q := (2314079914843 / 100000000000000 : ℝ))
      (E := (cell12233 ⟨49, by decide⟩).energy) (xi := (86791103504371 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12233 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12233]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12233])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12233) (a := (82390948889259 / 100000000000000 : ℝ)) (b := (84230837187 / 50000000000000 : ℝ)) (q := (2314079914843 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12233])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12233])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12233]

theorem cert12233_50 : CellCertificate 12233 (900215343412797 / 10000000000000000 : ℝ) (68682064402603 / 40000000000000000 : ℝ) (86791103504371 / 2500000000000000 : ℝ)
    (cell12233 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · have h := gap_lower (n := 12233) (a := (82357012358251 / 100000000000000 : ℝ)) (b := (84230837187 / 50000000000000 : ℝ)) (q := (2314083934163 / 100000000000000 : ℝ))
      (E := (cell12233 ⟨50, by decide⟩).energy) (xi := (86791103504371 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12233 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12233]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12233])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12233) (a := (82357012358251 / 100000000000000 : ℝ)) (b := (84230837187 / 50000000000000 : ℝ)) (q := (2314083934163 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12233])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12233])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12233]

theorem cert12233_51 : CellCertificate 12233 (900215343412797 / 10000000000000000 : ℝ) (68682064402603 / 40000000000000000 : ℝ) (86791103504371 / 2500000000000000 : ℝ)
    (cell12233 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · have h := gap_lower (n := 12233) (a := (82323099375979 / 100000000000000 : ℝ)) (b := (84230837187 / 50000000000000 : ℝ)) (q := (2314087912437 / 100000000000000 : ℝ))
      (E := (cell12233 ⟨51, by decide⟩).energy) (xi := (86791103504371 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12233 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12233]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12233])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12233) (a := (82323099375979 / 100000000000000 : ℝ)) (b := (84230837187 / 50000000000000 : ℝ)) (q := (2314087912437 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12233])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12233])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12233]

theorem cert12233_52 : CellCertificate 12233 (900215343412797 / 10000000000000000 : ℝ) (68682064402603 / 40000000000000000 : ℝ) (86791103504371 / 2500000000000000 : ℝ)
    (cell12233 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · have h := gap_lower (n := 12233) (a := (82289209913723 / 100000000000000 : ℝ)) (b := (84230837187 / 50000000000000 : ℝ)) (q := (462818381319 / 20000000000000 : ℝ))
      (E := (cell12233 ⟨52, by decide⟩).energy) (xi := (86791103504371 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12233 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12233]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12233])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12233) (a := (82289209913723 / 100000000000000 : ℝ)) (b := (84230837187 / 50000000000000 : ℝ)) (q := (462818381319 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12233])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12233])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12233]

theorem cert12233_53 : CellCertificate 12233 (900215343412797 / 10000000000000000 : ℝ) (68682064402603 / 40000000000000000 : ℝ) (86791103504371 / 2500000000000000 : ℝ)
    (cell12233 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · have h := gap_lower (n := 12233) (a := (41127671971453 / 50000000000000 : ℝ)) (b := (84230837187 / 50000000000000 : ℝ)) (q := (2314095914443 / 100000000000000 : ℝ))
      (E := (cell12233 ⟨53, by decide⟩).energy) (xi := (86791103504371 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12233 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12233]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12233])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12233) (a := (41127671971453 / 50000000000000 : ℝ)) (b := (84230837187 / 50000000000000 : ℝ)) (q := (2314095914443 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12233])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12233])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12233]

theorem cert12233_54 : CellCertificate 12233 (900215343412797 / 10000000000000000 : ℝ) (68682064402603 / 40000000000000000 : ℝ) (86791103504371 / 2500000000000000 : ℝ)
    (cell12233 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · have h := gap_lower (n := 12233) (a := (82221501435097 / 100000000000000 : ℝ)) (b := (84230837187 / 50000000000000 : ℝ)) (q := (2314099933573 / 100000000000000 : ℝ))
      (E := (cell12233 ⟨54, by decide⟩).energy) (xi := (86791103504371 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12233 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12233]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12233])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12233) (a := (82221501435097 / 100000000000000 : ℝ)) (b := (84230837187 / 50000000000000 : ℝ)) (q := (2314099933573 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12233])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12233])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12233]

theorem cert12233_55 : CellCertificate 12233 (900215343412797 / 10000000000000000 : ℝ) (68682064402603 / 40000000000000000 : ℝ) (86791103504371 / 2500000000000000 : ℝ)
    (cell12233 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · have h := gap_lower (n := 12233) (a := (16437536472401 / 20000000000000 : ℝ)) (b := (84230837187 / 50000000000000 : ℝ)) (q := (462820780463 / 20000000000000 : ℝ))
      (E := (cell12233 ⟨55, by decide⟩).energy) (xi := (86791103504371 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12233 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12233]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12233])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12233) (a := (16437536472401 / 20000000000000 : ℝ)) (b := (84230837187 / 50000000000000 : ℝ)) (q := (462820780463 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12233])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12233])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12233]

theorem cert12233_56 : CellCertificate 12233 (900215343412797 / 10000000000000000 : ℝ) (68682064402603 / 40000000000000000 : ℝ) (86791103504371 / 2500000000000000 : ℝ)
    (cell12233 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · have h := gap_lower (n := 12233) (a := (82153886695483 / 100000000000000 : ℝ)) (b := (84230837187 / 50000000000000 : ℝ)) (q := (2314107935921 / 100000000000000 : ℝ))
      (E := (cell12233 ⟨56, by decide⟩).energy) (xi := (86791103504371 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12233 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12233]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12233])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12233) (a := (82153886695483 / 100000000000000 : ℝ)) (b := (84230837187 / 50000000000000 : ℝ)) (q := (2314107935921 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12233])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12233])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12233]

theorem cert12233_57 : CellCertificate 12233 (900215343412797 / 10000000000000000 : ℝ) (68682064402603 / 40000000000000000 : ℝ) (86791103504371 / 2500000000000000 : ℝ)
    (cell12233 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · have h := gap_lower (n := 12233) (a := (41060057203761 / 50000000000000 : ℝ)) (b := (84230837187 / 50000000000000 : ℝ)) (q := (1157055956613 / 50000000000000 : ℝ))
      (E := (cell12233 ⟨57, by decide⟩).energy) (xi := (86791103504371 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12233 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12233]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12233])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12233) (a := (41060057203761 / 50000000000000 : ℝ)) (b := (84230837187 / 50000000000000 : ℝ)) (q := (1157055956613 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12233])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12233])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12233]

theorem cert12233_58 : CellCertificate 12233 (900215343412797 / 10000000000000000 : ℝ) (68682064402603 / 40000000000000000 : ℝ) (86791103504371 / 2500000000000000 : ℝ)
    (cell12233 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · have h := gap_lower (n := 12233) (a := (82086365470257 / 100000000000000 : ℝ)) (b := (84230837187 / 50000000000000 : ℝ)) (q := (2314115890031 / 100000000000000 : ℝ))
      (E := (cell12233 ⟨58, by decide⟩).energy) (xi := (86791103504371 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12233 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12233]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12233])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12233) (a := (82086365470257 / 100000000000000 : ℝ)) (b := (84230837187 / 50000000000000 : ℝ)) (q := (2314115890031 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12233])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12233])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12233]

theorem cert12233_59 : CellCertificate 12233 (900215343412797 / 10000000000000000 : ℝ) (68682064402603 / 40000000000000000 : ℝ) (86791103504371 / 2500000000000000 : ℝ)
    (cell12233 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · have h := gap_lower (n := 12233) (a := (82052639855961 / 100000000000000 : ℝ)) (b := (84230837187 / 50000000000000 : ℝ)) (q := (2314119922027 / 100000000000000 : ℝ))
      (E := (cell12233 ⟨59, by decide⟩).energy) (xi := (86791103504371 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12233 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12233]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12233])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12233) (a := (82052639855961 / 100000000000000 : ℝ)) (b := (84230837187 / 50000000000000 : ℝ)) (q := (2314119922027 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12233])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12233])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12233]

theorem cert12234_40 : CellCertificate 12234 (900185321060227 / 10000000000000000 : ℝ) (1716911211367999 / 1000000000000000000 : ℝ) (347135273050673 / 10000000000000000 : ℝ)
    (cell12234 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · have h := gap_lower (n := 12234) (a := (10337179883191 / 12500000000000 : ℝ)) (b := (168447719061 / 100000000000000 : ℝ)) (q := (2313895241429 / 100000000000000 : ℝ))
      (E := (cell12234 ⟨40, by decide⟩).energy) (xi := (347135273050673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12234 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12234]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12234])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12234) (a := (10337179883191 / 12500000000000 : ℝ)) (b := (168447719061 / 100000000000000 : ℝ)) (q := (2313895241429 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12234])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12234])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12234]

theorem cert12234_41 : CellCertificate 12234 (900185321060227 / 10000000000000000 : ℝ) (1716911211367999 / 1000000000000000000 : ℝ) (347135273050673 / 10000000000000000 : ℝ)
    (cell12234 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · have h := gap_lower (n := 12234) (a := (2066582239997 / 2500000000000 : ℝ)) (b := (168447719061 / 100000000000000 : ℝ)) (q := (144618702857 / 6250000000000 : ℝ))
      (E := (cell12234 ⟨41, by decide⟩).energy) (xi := (347135273050673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12234 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12234]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12234])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12234) (a := (2066582239997 / 2500000000000 : ℝ)) (b := (168447719061 / 100000000000000 : ℝ)) (q := (144618702857 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12234])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12234])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12234]

theorem cert12234_42 : CellCertificate 12234 (900185321060227 / 10000000000000000 : ℝ) (1716911211367999 / 1000000000000000000 : ℝ) (347135273050673 / 10000000000000000 : ℝ)
    (cell12234 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · have h := gap_lower (n := 12234) (a := (82629163947641 / 100000000000000 : ℝ)) (b := (168447719061 / 100000000000000 : ℝ)) (q := (2313903276929 / 100000000000000 : ℝ))
      (E := (cell12234 ⟨42, by decide⟩).energy) (xi := (347135273050673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12234 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12234]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12234])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12234) (a := (82629163947641 / 100000000000000 : ℝ)) (b := (168447719061 / 100000000000000 : ℝ)) (q := (2313903276929 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12234])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12234])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12234]

theorem cert12234_43 : CellCertificate 12234 (900185321060227 / 10000000000000000 : ℝ) (1716911211367999 / 1000000000000000000 : ℝ) (347135273050673 / 10000000000000000 : ℝ)
    (cell12234 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · have h := gap_lower (n := 12234) (a := (16519012415751 / 20000000000000 : ℝ)) (b := (168447719061 / 100000000000000 : ℝ)) (q := (2313907276281 / 100000000000000 : ℝ))
      (E := (cell12234 ⟨43, by decide⟩).energy) (xi := (347135273050673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12234 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12234]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12234])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12234) (a := (16519012415751 / 20000000000000 : ℝ)) (b := (168447719061 / 100000000000000 : ℝ)) (q := (2313907276281 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12234])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12234])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12234]

theorem cert12234_44 : CellCertificate 12234 (900185321060227 / 10000000000000000 : ℝ) (1716911211367999 / 1000000000000000000 : ℝ) (347135273050673 / 10000000000000000 : ℝ)
    (cell12234 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · have h := gap_lower (n := 12234) (a := (20640245990829 / 25000000000000 : ℝ)) (b := (168447719061 / 100000000000000 : ℝ)) (q := (2313911243451 / 100000000000000 : ℝ))
      (E := (cell12234 ⟨44, by decide⟩).energy) (xi := (347135273050673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12234 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12234]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12234])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12234) (a := (20640245990829 / 25000000000000 : ℝ)) (b := (168447719061 / 100000000000000 : ℝ)) (q := (2313911243451 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12234])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12234])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12234]

theorem cert12234_45 : CellCertificate 12234 (900185321060227 / 10000000000000000 : ℝ) (1716911211367999 / 1000000000000000000 : ℝ) (347135273050673 / 10000000000000000 : ℝ)
    (cell12234 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · have h := gap_lower (n := 12234) (a := (8252692957157 / 10000000000000 : ℝ)) (b := (168447719061 / 100000000000000 : ℝ)) (q := (462783047343 / 20000000000000 : ℝ))
      (E := (cell12234 ⟨45, by decide⟩).energy) (xi := (347135273050673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12234 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12234]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12234])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12234) (a := (8252692957157 / 10000000000000 : ℝ)) (b := (168447719061 / 100000000000000 : ℝ)) (q := (462783047343 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12234])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12234])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12234]

theorem cert12234_46 : CellCertificate 12234 (900185321060227 / 10000000000000000 : ℝ) (1716911211367999 / 1000000000000000000 : ℝ) (347135273050673 / 10000000000000000 : ℝ)
    (cell12234 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · have h := gap_lower (n := 12234) (a := (20623224718479 / 25000000000000 : ℝ)) (b := (168447719061 / 100000000000000 : ℝ)) (q := (1156959627693 / 50000000000000 : ℝ))
      (E := (cell12234 ⟨46, by decide⟩).energy) (xi := (347135273050673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12234 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12234]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12234])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12234) (a := (20623224718479 / 25000000000000 : ℝ)) (b := (168447719061 / 100000000000000 : ℝ)) (q := (1156959627693 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12234])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12234])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12234]

theorem cert12234_47 : CellCertificate 12234 (900185321060227 / 10000000000000000 : ℝ) (1716911211367999 / 1000000000000000000 : ℝ) (347135273050673 / 10000000000000000 : ℝ)
    (cell12234 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · have h := gap_lower (n := 12234) (a := (41229445920449 / 50000000000000 : ℝ)) (b := (168447719061 / 100000000000000 : ℝ)) (q := (462784647939 / 20000000000000 : ℝ))
      (E := (cell12234 ⟨47, by decide⟩).energy) (xi := (347135273050673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12234 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12234]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12234])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12234) (a := (41229445920449 / 50000000000000 : ℝ)) (b := (168447719061 / 100000000000000 : ℝ)) (q := (462784647939 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12234])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12234])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12234]

theorem cert12234_48 : CellCertificate 12234 (900185321060227 / 10000000000000000 : ℝ) (1716911211367999 / 1000000000000000000 : ℝ) (347135273050673 / 10000000000000000 : ℝ)
    (cell12234 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · have h := gap_lower (n := 12234) (a := (20606227110803 / 25000000000000 : ℝ)) (b := (168447719061 / 100000000000000 : ℝ)) (q := (2313927247337 / 100000000000000 : ℝ))
      (E := (cell12234 ⟨48, by decide⟩).energy) (xi := (347135273050673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12234 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12234]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12234])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12234) (a := (20606227110803 / 25000000000000 : ℝ)) (b := (168447719061 / 100000000000000 : ℝ)) (q := (2313927247337 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12234])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12234])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12234]

theorem cert12234_49 : CellCertificate 12234 (900185321060227 / 10000000000000000 : ℝ) (1716911211367999 / 1000000000000000000 : ℝ) (347135273050673 / 10000000000000000 : ℝ)
    (cell12234 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · have h := gap_lower (n := 12234) (a := (823909486517 / 1000000000000 : ℝ)) (b := (168447719061 / 100000000000000 : ℝ)) (q := (2313931218063 / 100000000000000 : ℝ))
      (E := (cell12234 ⟨49, by decide⟩).energy) (xi := (347135273050673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12234 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12234]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12234])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12234) (a := (823909486517 / 1000000000000 : ℝ)) (b := (168447719061 / 100000000000000 : ℝ)) (q := (2313931218063 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12234])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12234])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12234]

theorem cert12234_50 : CellCertificate 12234 (900185321060227 / 10000000000000000 : ℝ) (1716911211367999 / 1000000000000000000 : ℝ) (347135273050673 / 10000000000000000 : ℝ)
    (cell12234 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · have h := gap_lower (n := 12234) (a := (10294626554669 / 12500000000000 : ℝ)) (b := (168447719061 / 100000000000000 : ℝ)) (q := (2313935209183 / 100000000000000 : ℝ))
      (E := (cell12234 ⟨50, by decide⟩).energy) (xi := (347135273050673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12234 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12234]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12234])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12234) (a := (10294626554669 / 12500000000000 : ℝ)) (b := (168447719061 / 100000000000000 : ℝ)) (q := (2313935209183 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12234])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12234])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12234]

theorem cert12234_51 : CellCertificate 12234 (900185321060227 / 10000000000000000 : ℝ) (1716911211367999 / 1000000000000000000 : ℝ) (347135273050673 / 10000000000000000 : ℝ)
    (cell12234 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · have h := gap_lower (n := 12234) (a := (41161549885651 / 50000000000000 : ℝ)) (b := (168447719061 / 100000000000000 : ℝ)) (q := (2313939218929 / 100000000000000 : ℝ))
      (E := (cell12234 ⟨51, by decide⟩).energy) (xi := (347135273050673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12234 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12234]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12234])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12234) (a := (41161549885651 / 50000000000000 : ℝ)) (b := (168447719061 / 100000000000000 : ℝ)) (q := (2313939218929 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12234])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12234])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12234]

theorem cert12234_52 : CellCertificate 12234 (900185321060227 / 10000000000000000 : ℝ) (1716911211367999 / 1000000000000000000 : ℝ) (347135273050673 / 10000000000000000 : ℝ)
    (cell12234 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · have h := gap_lower (n := 12234) (a := (1285768916013 / 1562500000000 : ℝ)) (b := (168447719061 / 100000000000000 : ℝ)) (q := (72310724573 / 3125000000000 : ℝ))
      (E := (cell12234 ⟨52, by decide⟩).energy) (xi := (347135273050673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12234 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12234]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12234])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12234) (a := (1285768916013 / 1562500000000 : ℝ)) (b := (168447719061 / 100000000000000 : ℝ)) (q := (72310724573 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12234])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12234])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12234]

theorem cert12234_53 : CellCertificate 12234 (900185321060227 / 10000000000000000 : ℝ) (1716911211367999 / 1000000000000000000 : ℝ) (347135273050673 / 10000000000000000 : ℝ)
    (cell12234 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · have h := gap_lower (n := 12234) (a := (82255344969367 / 100000000000000 : ℝ)) (b := (168447719061 / 100000000000000 : ℝ)) (q := (2313947227149 / 100000000000000 : ℝ))
      (E := (cell12234 ⟨53, by decide⟩).energy) (xi := (347135273050673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12234 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12234]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12234])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12234) (a := (82255344969367 / 100000000000000 : ℝ)) (b := (168447719061 / 100000000000000 : ℝ)) (q := (2313947227149 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12234])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12234])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12234]

theorem cert12234_54 : CellCertificate 12234 (900185321060227 / 10000000000000000 : ℝ) (1716911211367999 / 1000000000000000000 : ℝ) (347135273050673 / 10000000000000000 : ℝ)
    (cell12234 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · have h := gap_lower (n := 12234) (a := (82221502776473 / 100000000000000 : ℝ)) (b := (168447719061 / 100000000000000 : ℝ)) (q := (1156975610487 / 50000000000000 : ℝ))
      (E := (cell12234 ⟨54, by decide⟩).energy) (xi := (347135273050673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12234 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12234]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12234])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12234) (a := (82221502776473 / 100000000000000 : ℝ)) (b := (168447719061 / 100000000000000 : ℝ)) (q := (1156975610487 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12234])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12234])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12234]

theorem cert12234_55 : CellCertificate 12234 (900185321060227 / 10000000000000000 : ℝ) (1716911211367999 / 1000000000000000000 : ℝ) (347135273050673 / 10000000000000000 : ℝ)
    (cell12234 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · have h := gap_lower (n := 12234) (a := (82187684017863 / 100000000000000 : ℝ)) (b := (168447719061 / 100000000000000 : ℝ)) (q := (1156977612087 / 50000000000000 : ℝ))
      (E := (cell12234 ⟨55, by decide⟩).energy) (xi := (347135273050673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12234 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12234]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12234])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12234) (a := (82187684017863 / 100000000000000 : ℝ)) (b := (168447719061 / 100000000000000 : ℝ)) (q := (1156977612087 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12234])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12234])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12234]

theorem cert12234_56 : CellCertificate 12234 (900185321060227 / 10000000000000000 : ℝ) (1716911211367999 / 1000000000000000000 : ℝ) (347135273050673 / 10000000000000000 : ℝ)
    (cell12234 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · have h := gap_lower (n := 12234) (a := (82153888665389 / 100000000000000 : ℝ)) (b := (168447719061 / 100000000000000 : ℝ)) (q := (2313959174843 / 100000000000000 : ℝ))
      (E := (cell12234 ⟨56, by decide⟩).energy) (xi := (347135273050673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12234 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12234]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12234])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12234) (a := (82153888665389 / 100000000000000 : ℝ)) (b := (168447719061 / 100000000000000 : ℝ)) (q := (2313959174843 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12234])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12234])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12234]

theorem cert12234_57 : CellCertificate 12234 (900185321060227 / 10000000000000000 : ℝ) (1716911211367999 / 1000000000000000000 : ℝ) (347135273050673 / 10000000000000000 : ℝ)
    (cell12234 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · have h := gap_lower (n := 12234) (a := (16424023338209 / 20000000000000 : ℝ)) (b := (168447719061 / 100000000000000 : ℝ)) (q := (2313963188069 / 100000000000000 : ℝ))
      (E := (cell12234 ⟨57, by decide⟩).energy) (xi := (347135273050673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12234 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12234]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12234])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12234) (a := (16424023338209 / 20000000000000 : ℝ)) (b := (168447719061 / 100000000000000 : ℝ)) (q := (2313963188069 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12234])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12234])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12234]

theorem cert12234_58 : CellCertificate 12234 (900185321060227 / 10000000000000000 : ℝ) (1716911211367999 / 1000000000000000000 : ℝ) (347135273050673 / 10000000000000000 : ℝ)
    (cell12234 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · have h := gap_lower (n := 12234) (a := (20521592016741 / 25000000000000 : ℝ)) (b := (168447719061 / 100000000000000 : ℝ)) (q := (144622950097 / 6250000000000 : ℝ))
      (E := (cell12234 ⟨58, by decide⟩).energy) (xi := (347135273050673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12234 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12234]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12234])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12234) (a := (20521592016741 / 25000000000000 : ℝ)) (b := (168447719061 / 100000000000000 : ℝ)) (q := (144622950097 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12234])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12234])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12234]

theorem cert12234_59 : CellCertificate 12234 (900185321060227 / 10000000000000000 : ℝ) (1716911211367999 / 1000000000000000000 : ℝ) (347135273050673 / 10000000000000000 : ℝ)
    (cell12234 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · have h := gap_lower (n := 12234) (a := (4102632138271 / 5000000000000 : ℝ)) (b := (168447719061 / 100000000000000 : ℝ)) (q := (462794242367 / 20000000000000 : ℝ))
      (E := (cell12234 ⟨59, by decide⟩).energy) (xi := (347135273050673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12234 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12234]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12234])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12234) (a := (4102632138271 / 5000000000000 : ℝ)) (b := (168447719061 / 100000000000000 : ℝ)) (q := (462794242367 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12234])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12234])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12234]

theorem cert12235_40 : CellCertificate 12235 (112519412929669 / 1250000000000000 : ℝ) (1716770835629093 / 1000000000000000000 : ℝ) (6942122742089 / 200000000000000 : ℝ)
    (cell12235 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · have h := gap_lower (n := 12235) (a := (82697435959237 / 100000000000000 : ℝ)) (b := (42108441523 / 25000000000000 : ℝ)) (q := (231374665089 / 10000000000000 : ℝ))
      (E := (cell12235 ⟨40, by decide⟩).energy) (xi := (6942122742089 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12235 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12235]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12235])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12235) (a := (82697435959237 / 100000000000000 : ℝ)) (b := (42108441523 / 25000000000000 : ℝ)) (q := (231374665089 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12235])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12235])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12235]

theorem cert12235_41 : CellCertificate 12235 (112519412929669 / 1250000000000000 : ℝ) (1716770835629093 / 1000000000000000000 : ℝ) (6942122742089 / 200000000000000 : ℝ)
    (cell12235 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · have h := gap_lower (n := 12235) (a := (82663286814177 / 100000000000000 : ℝ)) (b := (42108441523 / 25000000000000 : ℝ)) (q := (1156875310247 / 50000000000000 : ℝ))
      (E := (cell12235 ⟨41, by decide⟩).energy) (xi := (6942122742089 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12235 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12235]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12235])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12235) (a := (82663286814177 / 100000000000000 : ℝ)) (b := (42108441523 / 25000000000000 : ℝ)) (q := (1156875310247 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12235])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12235])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12235]

theorem cert12235_42 : CellCertificate 12235 (112519412929669 / 1250000000000000 : ℝ) (1716770835629093 / 1000000000000000000 : ℝ) (6942122742089 / 200000000000000 : ℝ)
    (cell12235 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · have h := gap_lower (n := 12235) (a := (82629161482083 / 100000000000000 : ℝ)) (b := (42108441523 / 25000000000000 : ℝ)) (q := (9255018471 / 400000000000 : ℝ))
      (E := (cell12235 ⟨42, by decide⟩).energy) (xi := (6942122742089 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12235 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12235]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12235])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12235) (a := (82629161482083 / 100000000000000 : ℝ)) (b := (42108441523 / 25000000000000 : ℝ)) (q := (9255018471 / 400000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12235])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12235])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12235]

theorem cert12235_43 : CellCertificate 12235 (112519412929669 / 1250000000000000 : ℝ) (1716770835629093 / 1000000000000000000 : ℝ) (6942122742089 / 200000000000000 : ℝ)
    (cell12235 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · have h := gap_lower (n := 12235) (a := (82595059932897 / 100000000000000 : ℝ)) (b := (42108441523 / 25000000000000 : ℝ)) (q := (289219830329 / 12500000000000 : ℝ))
      (E := (cell12235 ⟨43, by decide⟩).energy) (xi := (6942122742089 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12235 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12235]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12235])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12235) (a := (82595059932897 / 100000000000000 : ℝ)) (b := (42108441523 / 25000000000000 : ℝ)) (q := (289219830329 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12235])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12235])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12235]

theorem cert12235_44 : CellCertificate 12235 (112519412929669 / 1250000000000000 : ℝ) (1716770835629093 / 1000000000000000000 : ℝ) (6942122742089 / 200000000000000 : ℝ)
    (cell12235 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · have h := gap_lower (n := 12235) (a := (82560982136717 / 100000000000000 : ℝ)) (b := (42108441523 / 25000000000000 : ℝ)) (q := (462752527219 / 20000000000000 : ℝ))
      (E := (cell12235 ⟨44, by decide⟩).energy) (xi := (6942122742089 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12235 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12235]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12235])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12235) (a := (82560982136717 / 100000000000000 : ℝ)) (b := (42108441523 / 25000000000000 : ℝ)) (q := (462752527219 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12235])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12235])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12235]

theorem cert12235_45 : CellCertificate 12235 (112519412929669 / 1250000000000000 : ℝ) (1716770835629093 / 1000000000000000000 : ℝ) (6942122742089 / 200000000000000 : ℝ)
    (cell12235 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · have h := gap_lower (n := 12235) (a := (20631732015947 / 25000000000000 : ℝ)) (b := (42108441523 / 25000000000000 : ℝ)) (q := (2313766597601 / 100000000000000 : ℝ))
      (E := (cell12235 ⟨45, by decide⟩).energy) (xi := (6942122742089 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12235 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12235]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12235])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12235) (a := (20631732015947 / 25000000000000 : ℝ)) (b := (42108441523 / 25000000000000 : ℝ)) (q := (2313766597601 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12235])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12235])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12235]

theorem cert12235_46 : CellCertificate 12235 (112519412929669 / 1250000000000000 : ℝ) (1716770835629093 / 1000000000000000000 : ℝ) (6942122742089 / 200000000000000 : ℝ)
    (cell12235 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · have h := gap_lower (n := 12235) (a := (82492897684509 / 100000000000000 : ℝ)) (b := (42108441523 / 25000000000000 : ℝ)) (q := (231377058523 / 10000000000000 : ℝ))
      (E := (cell12235 ⟨46, by decide⟩).energy) (xi := (6942122742089 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12235 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12235]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12235])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12235) (a := (82492897684509 / 100000000000000 : ℝ)) (b := (42108441523 / 25000000000000 : ℝ)) (q := (231377058523 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12235])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12235])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12235]

theorem cert12235_47 : CellCertificate 12235 (112519412929669 / 1250000000000000 : ℝ) (1716770835629093 / 1000000000000000000 : ℝ) (6942122742089 / 200000000000000 : ℝ)
    (cell12235 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · have h := gap_lower (n := 12235) (a := (82458890969427 / 100000000000000 : ℝ)) (b := (42108441523 / 25000000000000 : ℝ)) (q := (1156887299039 / 50000000000000 : ℝ))
      (E := (cell12235 ⟨47, by decide⟩).energy) (xi := (6942122742089 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12235 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12235]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12235])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12235) (a := (82458890969427 / 100000000000000 : ℝ)) (b := (42108441523 / 25000000000000 : ℝ)) (q := (1156887299039 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12235])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12235])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12235]

theorem cert12235_48 : CellCertificate 12235 (112519412929669 / 1250000000000000 : ℝ) (1716770835629093 / 1000000000000000000 : ℝ) (6942122742089 / 200000000000000 : ℝ)
    (cell12235 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · have h := gap_lower (n := 12235) (a := (41212453944619 / 50000000000000 : ℝ)) (b := (42108441523 / 25000000000000 : ℝ)) (q := (578444644033 / 25000000000000 : ℝ))
      (E := (cell12235 ⟨48, by decide⟩).energy) (xi := (6942122742089 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12235 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12235]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12235])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12235) (a := (41212453944619 / 50000000000000 : ℝ)) (b := (42108441523 / 25000000000000 : ℝ)) (q := (578444644033 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12235])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12235])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12235]

theorem cert12235_49 : CellCertificate 12235 (112519412929669 / 1250000000000000 : ℝ) (1716770835629093 / 1000000000000000000 : ℝ) (6942122742089 / 200000000000000 : ℝ)
    (cell12235 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · have h := gap_lower (n := 12235) (a := (1287358568981 / 1562500000000 : ℝ)) (b := (42108441523 / 25000000000000 : ℝ)) (q := (9038213191 / 390625000000 : ℝ))
      (E := (cell12235 ⟨49, by decide⟩).energy) (xi := (6942122742089 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12235 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12235]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12235])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12235) (a := (1287358568981 / 1562500000000 : ℝ)) (b := (42108441523 / 25000000000000 : ℝ)) (q := (9038213191 / 390625000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12235])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12235])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12235]

theorem cert12235_50 : CellCertificate 12235 (112519412929669 / 1250000000000000 : ℝ) (1716770835629093 / 1000000000000000000 : ℝ) (6942122742089 / 200000000000000 : ℝ)
    (cell12235 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · have h := gap_lower (n := 12235) (a := (16471402503411 / 20000000000000 : ℝ)) (b := (42108441523 / 25000000000000 : ℝ)) (q := (72305831213 / 3125000000000 : ℝ))
      (E := (cell12235 ⟨50, by decide⟩).energy) (xi := (6942122742089 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12235 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12235]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12235])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12235) (a := (16471402503411 / 20000000000000 : ℝ)) (b := (42108441523 / 25000000000000 : ℝ)) (q := (72305831213 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12235])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12235])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12235]

theorem cert12235_51 : CellCertificate 12235 (112519412929669 / 1250000000000000 : ℝ) (1716770835629093 / 1000000000000000000 : ℝ) (6942122742089 / 200000000000000 : ℝ)
    (cell12235 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · have h := gap_lower (n := 12235) (a := (82323100167189 / 100000000000000 : ℝ)) (b := (42108441523 / 25000000000000 : ℝ)) (q := (1156895290581 / 50000000000000 : ℝ))
      (E := (cell12235 ⟨51, by decide⟩).energy) (xi := (6942122742089 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12235 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12235]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12235])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12235) (a := (82323100167189 / 100000000000000 : ℝ)) (b := (42108441523 / 25000000000000 : ℝ)) (q := (1156895290581 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12235])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12235])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12235]

theorem cert12235_52 : CellCertificate 12235 (112519412929669 / 1250000000000000 : ℝ) (1716770835629093 / 1000000000000000000 : ℝ) (6942122742089 / 200000000000000 : ℝ)
    (cell12235 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · have h := gap_lower (n := 12235) (a := (41144605668233 / 50000000000000 : ℝ)) (b := (42108441523 / 25000000000000 : ℝ)) (q := (2313794580863 / 100000000000000 : ℝ))
      (E := (cell12235 ⟨52, by decide⟩).energy) (xi := (6942122742089 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12235 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12235]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12235])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12235) (a := (41144605668233 / 50000000000000 : ℝ)) (b := (42108441523 / 25000000000000 : ℝ)) (q := (2313794580863 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12235])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12235])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12235]

theorem cert12235_53 : CellCertificate 12235 (112519412929669 / 1250000000000000 : ℝ) (1716770835629093 / 1000000000000000000 : ℝ) (6942122742089 / 200000000000000 : ℝ)
    (cell12235 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · have h := gap_lower (n := 12235) (a := (82255345996311 / 100000000000000 : ℝ)) (b := (42108441523 / 25000000000000 : ℝ)) (q := (92551943829 / 4000000000000 : ℝ))
      (E := (cell12235 ⟨53, by decide⟩).energy) (xi := (6942122742089 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12235 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12235]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12235])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12235) (a := (82255345996311 / 100000000000000 : ℝ)) (b := (42108441523 / 25000000000000 : ℝ)) (q := (92551943829 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12235])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12235])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12235]

theorem cert12235_54 : CellCertificate 12235 (112519412929669 / 1250000000000000 : ℝ) (1716770835629093 / 1000000000000000000 : ℝ) (6942122742089 / 200000000000000 : ℝ)
    (cell12235 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · have h := gap_lower (n := 12235) (a := (41110752059147 / 50000000000000 : ℝ)) (b := (42108441523 / 25000000000000 : ℝ)) (q := (2313802564309 / 100000000000000 : ℝ))
      (E := (cell12235 ⟨54, by decide⟩).energy) (xi := (6942122742089 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12235 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12235]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12235])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12235) (a := (41110752059147 / 50000000000000 : ℝ)) (b := (42108441523 / 25000000000000 : ℝ)) (q := (2313802564309 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12235])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12235])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12235]

theorem cert12235_55 : CellCertificate 12235 (112519412929669 / 1250000000000000 : ℝ) (1716770835629093 / 1000000000000000000 : ℝ) (6942122742089 / 200000000000000 : ℝ)
    (cell12235 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · have h := gap_lower (n := 12235) (a := (41093842837063 / 50000000000000 : ℝ)) (b := (42108441523 / 25000000000000 : ℝ)) (q := (2313806602031 / 100000000000000 : ℝ))
      (E := (cell12235 ⟨55, by decide⟩).energy) (xi := (6942122742089 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12235 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12235]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12235])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12235) (a := (41093842837063 / 50000000000000 : ℝ)) (b := (42108441523 / 25000000000000 : ℝ)) (q := (2313806602031 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12235])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12235])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12235]

theorem cert12235_56 : CellCertificate 12235 (112519412929669 / 1250000000000000 : ℝ) (1716770835629093 / 1000000000000000000 : ℝ) (6942122742089 / 200000000000000 : ℝ)
    (cell12235 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · have h := gap_lower (n := 12235) (a := (82153890635661 / 100000000000000 : ℝ)) (b := (42108441523 / 25000000000000 : ℝ)) (q := (1156905293989 / 50000000000000 : ℝ))
      (E := (cell12235 ⟨56, by decide⟩).energy) (xi := (6942122742089 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12235 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12235]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12235])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12235) (a := (82153890635661 / 100000000000000 : ℝ)) (b := (42108441523 / 25000000000000 : ℝ)) (q := (1156905293989 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12235])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12235])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12235]

theorem cert12235_57 : CellCertificate 12235 (112519412929669 / 1250000000000000 : ℝ) (1716770835629093 / 1000000000000000000 : ℝ) (6942122742089 / 200000000000000 : ℝ)
    (cell12235 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · have h := gap_lower (n := 12235) (a := (41060059487447 / 50000000000000 : ℝ)) (b := (42108441523 / 25000000000000 : ℝ)) (q := (1156907289069 / 50000000000000 : ℝ))
      (E := (cell12235 ⟨57, by decide⟩).energy) (xi := (6942122742089 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12235 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12235]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12235])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12235) (a := (41060059487447 / 50000000000000 : ℝ)) (b := (42108441523 / 25000000000000 : ℝ)) (q := (1156907289069 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12235])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12235])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12235]

theorem cert12235_58 : CellCertificate 12235 (112519412929669 / 1250000000000000 : ℝ) (1716770835629093 / 1000000000000000000 : ℝ) (6942122742089 / 200000000000000 : ℝ)
    (cell12235 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · have h := gap_lower (n := 12235) (a := (41043185331979 / 50000000000000 : ℝ)) (b := (42108441523 / 25000000000000 : ℝ)) (q := (2313818569263 / 100000000000000 : ℝ))
      (E := (cell12235 ⟨58, by decide⟩).energy) (xi := (6942122742089 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12235 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12235]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12235])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12235) (a := (41043185331979 / 50000000000000 : ℝ)) (b := (42108441523 / 25000000000000 : ℝ)) (q := (2313818569263 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12235])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12235])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12235]

theorem cert12235_59 : CellCertificate 12235 (112519412929669 / 1250000000000000 : ℝ) (1716770835629093 / 1000000000000000000 : ℝ) (6942122742089 / 200000000000000 : ℝ)
    (cell12235 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · have h := gap_lower (n := 12235) (a := (82052645675127 / 100000000000000 : ℝ)) (b := (42108441523 / 25000000000000 : ℝ)) (q := (289227819737 / 12500000000000 : ℝ))
      (E := (cell12235 ⟨59, by decide⟩).energy) (xi := (6942122742089 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12235 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12235]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12235])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12235) (a := (82052645675127 / 100000000000000 : ℝ)) (b := (42108441523 / 25000000000000 : ℝ)) (q := (289227819737 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12235])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12235])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12235]

theorem cert12236_40 : CellCertificate 12236 (450062645271501 / 5000000000000000 : ℝ) (68665219313709 / 40000000000000000 : ℝ) (17353850308867 / 500000000000000 : ℝ)
    (cell12236 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · have h := gap_lower (n := 12236) (a := (82697432853949 / 100000000000000 : ℝ)) (b := (84209907733 / 50000000000000 : ℝ)) (q := (289199764423 / 12500000000000 : ℝ))
      (E := (cell12236 ⟨40, by decide⟩).energy) (xi := (17353850308867 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12236 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12236]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12236])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12236) (a := (82697432853949 / 100000000000000 : ℝ)) (b := (84209907733 / 50000000000000 : ℝ)) (q := (289199764423 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12236])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12236])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12236]

theorem cert12236_41 : CellCertificate 12236 (450062645271501 / 5000000000000000 : ℝ) (68665219313709 / 40000000000000000 : ℝ) (17353850308867 / 500000000000000 : ℝ)
    (cell12236 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · have h := gap_lower (n := 12236) (a := (41331642014719 / 50000000000000 : ℝ)) (b := (84209907733 / 50000000000000 : ℝ)) (q := (1156801054547 / 50000000000000 : ℝ))
      (E := (cell12236 ⟨41, by decide⟩).energy) (xi := (17353850308867 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12236 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12236]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12236])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12236) (a := (41331642014719 / 50000000000000 : ℝ)) (b := (84209907733 / 50000000000000 : ℝ)) (q := (1156801054547 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12236])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12236])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12236]

theorem cert12236_42 : CellCertificate 12236 (450062645271501 / 5000000000000000 : ℝ) (68665219313709 / 40000000000000000 : ℝ) (17353850308867 / 500000000000000 : ℝ)
    (cell12236 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · have h := gap_lower (n := 12236) (a := (10328644877181 / 12500000000000 : ℝ)) (b := (84209907733 / 50000000000000 : ℝ)) (q := (2313606072479 / 100000000000000 : ℝ))
      (E := (cell12236 ⟨42, by decide⟩).energy) (xi := (17353850308867 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12236 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12236]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12236])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12236) (a := (10328644877181 / 12500000000000 : ℝ)) (b := (84209907733 / 50000000000000 : ℝ)) (q := (2313606072479 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12236])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12236])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12236]

theorem cert12236_43 : CellCertificate 12236 (450062645271501 / 5000000000000000 : ℝ) (68665219313709 / 40000000000000000 : ℝ) (17353850308867 / 500000000000000 : ℝ)
    (cell12236 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · have h := gap_lower (n := 12236) (a := (82595057787923 / 100000000000000 : ℝ)) (b := (84209907733 / 50000000000000 : ℝ)) (q := (1156805061489 / 50000000000000 : ℝ))
      (E := (cell12236 ⟨43, by decide⟩).energy) (xi := (17353850308867 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12236 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12236]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12236])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12236) (a := (82595057787923 / 100000000000000 : ℝ)) (b := (84209907733 / 50000000000000 : ℝ)) (q := (1156805061489 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12236])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12236])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12236]

theorem cert12236_44 : CellCertificate 12236 (450062645271501 / 5000000000000000 : ℝ) (68665219313709 / 40000000000000000 : ℝ) (17353850308867 / 500000000000000 : ℝ)
    (cell12236 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · have h := gap_lower (n := 12236) (a := (82560980310961 / 100000000000000 : ℝ)) (b := (84209907733 / 50000000000000 : ℝ)) (q := (231361408403 / 10000000000000 : ℝ))
      (E := (cell12236 ⟨44, by decide⟩).energy) (xi := (17353850308867 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12236 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12236]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12236])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12236) (a := (82560980310961 / 100000000000000 : ℝ)) (b := (84209907733 / 50000000000000 : ℝ)) (q := (231361408403 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12236])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12236])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12236]

theorem cert12236_45 : CellCertificate 12236 (450062645271501 / 5000000000000000 : ℝ) (68665219313709 / 40000000000000000 : ℝ) (17353850308867 / 500000000000000 : ℝ)
    (cell12236 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · have h := gap_lower (n := 12236) (a := (82526926556809 / 100000000000000 : ℝ)) (b := (84209907733 / 50000000000000 : ℝ)) (q := (1156809036329 / 50000000000000 : ℝ))
      (E := (cell12236 ⟨45, by decide⟩).energy) (xi := (17353850308867 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12236 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12236]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12236])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12236) (a := (82526926556809 / 100000000000000 : ℝ)) (b := (84209907733 / 50000000000000 : ℝ)) (q := (1156809036329 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12236])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12236])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12236]

theorem cert12236_46 : CellCertificate 12236 (450062645271501 / 5000000000000000 : ℝ) (68665219313709 / 40000000000000000 : ℝ) (17353850308867 / 500000000000000 : ℝ)
    (cell12236 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · have h := gap_lower (n := 12236) (a := (41246448247933 / 50000000000000 : ℝ)) (b := (84209907733 / 50000000000000 : ℝ)) (q := (1156811044087 / 50000000000000 : ℝ))
      (E := (cell12236 ⟨46, by decide⟩).energy) (xi := (17353850308867 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12236 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12236]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12236])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12236) (a := (41246448247933 / 50000000000000 : ℝ)) (b := (84209907733 / 50000000000000 : ℝ)) (q := (1156811044087 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12236])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12236])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12236]

theorem cert12236_47 : CellCertificate 12236 (450062645271501 / 5000000000000000 : ℝ) (68665219313709 / 40000000000000000 : ℝ) (17353850308867 / 500000000000000 : ℝ)
    (cell12236 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · have h := gap_lower (n := 12236) (a := (2061472252467 / 2500000000000 : ℝ)) (b := (84209907733 / 50000000000000 : ℝ)) (q := (2313626070807 / 100000000000000 : ℝ))
      (E := (cell12236 ⟨47, by decide⟩).energy) (xi := (17353850308867 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12236 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12236]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12236])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12236) (a := (2061472252467 / 2500000000000 : ℝ)) (b := (84209907733 / 50000000000000 : ℝ)) (q := (2313626070807 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12236])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12236])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12236]

theorem cert12236_48 : CellCertificate 12236 (450062645271501 / 5000000000000000 : ℝ) (68665219313709 / 40000000000000000 : ℝ) (17353850308867 / 500000000000000 : ℝ)
    (cell12236 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · have h := gap_lower (n := 12236) (a := (41212453667973 / 50000000000000 : ℝ)) (b := (84209907733 / 50000000000000 : ℝ)) (q := (578407519563 / 25000000000000 : ℝ))
      (E := (cell12236 ⟨48, by decide⟩).energy) (xi := (17353850308867 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12236 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12236]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12236])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12236) (a := (41212453667973 / 50000000000000 : ℝ)) (b := (84209907733 / 50000000000000 : ℝ)) (q := (578407519563 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12236])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12236])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12236]

theorem cert12236_49 : CellCertificate 12236 (450062645271501 / 5000000000000000 : ℝ) (68665219313709 / 40000000000000000 : ℝ) (17353850308867 / 500000000000000 : ℝ)
    (cell12236 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · have h := gap_lower (n := 12236) (a := (8239094817851 / 10000000000000 : ℝ)) (b := (84209907733 / 50000000000000 : ℝ)) (q := (1156817025127 / 50000000000000 : ℝ))
      (E := (cell12236 ⟨49, by decide⟩).energy) (xi := (17353850308867 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12236 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12236]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12236])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12236) (a := (8239094817851 / 10000000000000 : ℝ)) (b := (84209907733 / 50000000000000 : ℝ)) (q := (1156817025127 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12236])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12236])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12236]

theorem cert12236_50 : CellCertificate 12236 (450062645271501 / 5000000000000000 : ℝ) (68665219313709 / 40000000000000000 : ℝ) (17353850308867 / 500000000000000 : ℝ)
    (cell12236 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · have h := gap_lower (n := 12236) (a := (41178506298681 / 50000000000000 : ℝ)) (b := (84209907733 / 50000000000000 : ℝ)) (q := (18509104353 / 800000000000 : ℝ))
      (E := (cell12236 ⟨50, by decide⟩).energy) (xi := (17353850308867 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12236 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12236]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12236])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12236) (a := (41178506298681 / 50000000000000 : ℝ)) (b := (84209907733 / 50000000000000 : ℝ)) (q := (18509104353 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12236])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12236])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12236]

theorem cert12236_51 : CellCertificate 12236 (450062645271501 / 5000000000000000 : ℝ) (68665219313709 / 40000000000000000 : ℝ) (17353850308867 / 500000000000000 : ℝ)
    (cell12236 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · have h := gap_lower (n := 12236) (a := (82323100563639 / 100000000000000 : ℝ)) (b := (84209907733 / 50000000000000 : ℝ)) (q := (462728411619 / 20000000000000 : ℝ))
      (E := (cell12236 ⟨51, by decide⟩).energy) (xi := (17353850308867 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12236 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12236]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12236])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12236) (a := (82323100563639 / 100000000000000 : ℝ)) (b := (84209907733 / 50000000000000 : ℝ)) (q := (462728411619 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12236])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12236])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12236]

theorem cert12236_52 : CellCertificate 12236 (450062645271501 / 5000000000000000 : ℝ) (68665219313709 / 40000000000000000 : ℝ) (17353850308867 / 500000000000000 : ℝ)
    (cell12236 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · have h := gap_lower (n := 12236) (a := (41144606024311 / 50000000000000 : ℝ)) (b := (84209907733 / 50000000000000 : ℝ)) (q := (2313646031199 / 100000000000000 : ℝ))
      (E := (cell12236 ⟨52, by decide⟩).energy) (xi := (17353850308867 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12236 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12236]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12236])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12236) (a := (41144606024311 / 50000000000000 : ℝ)) (b := (84209907733 / 50000000000000 : ℝ)) (q := (2313646031199 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12236])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12236])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12236]

theorem cert12236_53 : CellCertificate 12236 (450062645271501 / 5000000000000000 : ℝ) (68665219313709 / 40000000000000000 : ℝ) (17353850308867 / 500000000000000 : ℝ)
    (cell12236 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · have h := gap_lower (n := 12236) (a := (82255347023739 / 100000000000000 : ℝ)) (b := (84209907733 / 50000000000000 : ℝ)) (q := (2313650020173 / 100000000000000 : ℝ))
      (E := (cell12236 ⟨53, by decide⟩).energy) (xi := (17353850308867 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12236 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12236]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12236])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12236) (a := (82255347023739 / 100000000000000 : ℝ)) (b := (84209907733 / 50000000000000 : ℝ)) (q := (2313650020173 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12236])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12236])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12236]

theorem cert12236_54 : CellCertificate 12236 (450062645271501 / 5000000000000000 : ℝ) (68665219313709 / 40000000000000000 : ℝ) (17353850308867 / 500000000000000 : ℝ)
    (cell12236 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · have h := gap_lower (n := 12236) (a := (82221505460559 / 100000000000000 : ℝ)) (b := (84209907733 / 50000000000000 : ℝ)) (q := (2313654022609 / 100000000000000 : ℝ))
      (E := (cell12236 ⟨54, by decide⟩).energy) (xi := (17353850308867 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12236 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12236]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12236])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12236) (a := (82221505460559 / 100000000000000 : ℝ)) (b := (84209907733 / 50000000000000 : ℝ)) (q := (2313654022609 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12236])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12236])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12236]

theorem cert12236_55 : CellCertificate 12236 (450062645271501 / 5000000000000000 : ℝ) (68665219313709 / 40000000000000000 : ℝ) (17353850308867 / 500000000000000 : ℝ)
    (cell12236 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · have h := gap_lower (n := 12236) (a := (41093843665397 / 50000000000000 : ℝ)) (b := (84209907733 / 50000000000000 : ℝ)) (q := (2313658035887 / 100000000000000 : ℝ))
      (E := (cell12236 ⟨55, by decide⟩).energy) (xi := (17353850308867 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12236 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12236]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12236])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12236) (a := (41093843665397 / 50000000000000 : ℝ)) (b := (84209907733 / 50000000000000 : ℝ)) (q := (2313658035887 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12236])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12236])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12236]

theorem cert12236_56 : CellCertificate 12236 (450062645271501 / 5000000000000000 : ℝ) (68665219313709 / 40000000000000000 : ℝ) (17353850308867 / 500000000000000 : ℝ)
    (cell12236 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · have h := gap_lower (n := 12236) (a := (82153892606299 / 100000000000000 : ℝ)) (b := (84209907733 / 50000000000000 : ℝ)) (q := (289207757147 / 12500000000000 : ℝ))
      (E := (cell12236 ⟨56, by decide⟩).energy) (xi := (17353850308867 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12236 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12236]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12236])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12236) (a := (82153892606299 / 100000000000000 : ℝ)) (b := (84209907733 / 50000000000000 : ℝ)) (q := (289207757147 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12236])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12236])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12236]

theorem cert12236_57 : CellCertificate 12236 (450062645271501 / 5000000000000000 : ℝ) (68665219313709 / 40000000000000000 : ℝ) (17353850308867 / 500000000000000 : ℝ)
    (cell12236 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · have h := gap_lower (n := 12236) (a := (20530030314767 / 25000000000000 : ℝ)) (b := (84209907733 / 50000000000000 : ℝ)) (q := (462733204867 / 20000000000000 : ℝ))
      (E := (cell12236 ⟨57, by decide⟩).energy) (xi := (17353850308867 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12236 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12236]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12236])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12236) (a := (20530030314767 / 25000000000000 : ℝ)) (b := (84209907733 / 50000000000000 : ℝ)) (q := (462733204867 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12236])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12236])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12236]

theorem cert12236_58 : CellCertificate 12236 (450062645271501 / 5000000000000000 : ℝ) (68665219313709 / 40000000000000000 : ℝ) (17353850308867 / 500000000000000 : ℝ)
    (cell12236 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · have h := gap_lower (n := 12236) (a := (41043186630619 / 50000000000000 : ℝ)) (b := (84209907733 / 50000000000000 : ℝ)) (q := (2313670052289 / 100000000000000 : ℝ))
      (E := (cell12236 ⟨58, by decide⟩).energy) (xi := (17353850308867 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12236 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12236]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12236])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12236) (a := (41043186630619 / 50000000000000 : ℝ)) (b := (84209907733 / 50000000000000 : ℝ)) (q := (2313670052289 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12236])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12236])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12236]

theorem cert12236_59 : CellCertificate 12236 (450062645271501 / 5000000000000000 : ℝ) (68665219313709 / 40000000000000000 : ℝ) (17353850308867 / 500000000000000 : ℝ)
    (cell12236 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · have h := gap_lower (n := 12236) (a := (41026324292541 / 50000000000000 : ℝ)) (b := (84209907733 / 50000000000000 : ℝ)) (q := (1156837009679 / 50000000000000 : ℝ))
      (E := (cell12236 ⟨59, by decide⟩).energy) (xi := (17353850308867 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12236 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12236]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12236])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12236) (a := (41026324292541 / 50000000000000 : ℝ)) (b := (84209907733 / 50000000000000 : ℝ)) (q := (1156837009679 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12236])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12236])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12236]

theorem cert12237_40 : CellCertificate 12237 (112511910297001 / 1250000000000000 : ℝ) (858245076501633 / 500000000000000000 : ℝ) (86761970066967 / 2500000000000000 : ℝ)
    (cell12237 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · have h := gap_lower (n := 12237) (a := (41348714874833 / 50000000000000 : ℝ)) (b := (84202933591 / 50000000000000 : ℝ)) (q := (2313449693607 / 100000000000000 : ℝ))
      (E := (cell12237 ⟨40, by decide⟩).energy) (xi := (86761970066967 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12237 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12237]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12237])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12237) (a := (41348714874833 / 50000000000000 : ℝ)) (b := (84202933591 / 50000000000000 : ℝ)) (q := (2313449693607 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12237])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12237])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12237]

theorem cert12237_41 : CellCertificate 12237 (112511910297001 / 1250000000000000 : ℝ) (858245076501633 / 500000000000000000 : ℝ) (86761970066967 / 2500000000000000 : ℝ)
    (cell12237 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · have h := gap_lower (n := 12237) (a := (41331640622831 / 50000000000000 : ℝ)) (b := (84202933591 / 50000000000000 : ℝ)) (q := (289181706599 / 12500000000000 : ℝ))
      (E := (cell12237 ⟨41, by decide⟩).energy) (xi := (86761970066967 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12237 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12237]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12237])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12237) (a := (41331640622831 / 50000000000000 : ℝ)) (b := (84202933591 / 50000000000000 : ℝ)) (q := (289181706599 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12237])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12237])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12237]

theorem cert12237_42 : CellCertificate 12237 (112511910297001 / 1250000000000000 : ℝ) (858245076501633 / 500000000000000000 : ℝ) (86761970066967 / 2500000000000000 : ℝ)
    (cell12237 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · have h := gap_lower (n := 12237) (a := (10328644569217 / 12500000000000 : ℝ)) (b := (84202933591 / 50000000000000 : ℝ)) (q := (578364410279 / 25000000000000 : ℝ))
      (E := (cell12237 ⟨42, by decide⟩).energy) (xi := (86761970066967 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12237 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12237]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12237])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12237) (a := (10328644569217 / 12500000000000 : ℝ)) (b := (84202933591 / 50000000000000 : ℝ)) (q := (578364410279 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12237])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12237])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12237]

theorem cert12237_43 : CellCertificate 12237 (112511910297001 / 1250000000000000 : ℝ) (858245076501633 / 500000000000000000 : ℝ) (86761970066967 / 2500000000000000 : ℝ)
    (cell12237 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · have h := gap_lower (n := 12237) (a := (10324381955479 / 12500000000000 : ℝ)) (b := (84202933591 / 50000000000000 : ℝ)) (q := (46269233171 / 2000000000000 : ℝ))
      (E := (cell12237 ⟨43, by decide⟩).energy) (xi := (86761970066967 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12237 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12237]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12237])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12237) (a := (10324381955479 / 12500000000000 : ℝ)) (b := (84202933591 / 50000000000000 : ℝ)) (q := (46269233171 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12237])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12237])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12237]

theorem cert12237_44 : CellCertificate 12237 (112511910297001 / 1250000000000000 : ℝ) (858245076501633 / 500000000000000000 : ℝ) (86761970066967 / 2500000000000000 : ℝ)
    (cell12237 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · have h := gap_lower (n := 12237) (a := (2580030577689 / 3125000000000 : ℝ)) (b := (84202933591 / 50000000000000 : ℝ)) (q := (2313465646049 / 100000000000000 : ℝ))
      (E := (cell12237 ⟨44, by decide⟩).energy) (xi := (86761970066967 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12237 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12237]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12237])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12237) (a := (2580030577689 / 3125000000000 : ℝ)) (b := (84202933591 / 50000000000000 : ℝ)) (q := (2313465646049 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12237])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12237])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12237]

theorem cert12237_45 : CellCertificate 12237 (112511910297001 / 1250000000000000 : ℝ) (858245076501633 / 500000000000000000 : ℝ) (86761970066967 / 2500000000000000 : ℝ)
    (cell12237 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · have h := gap_lower (n := 12237) (a := (10315865631329 / 12500000000000 : ℝ)) (b := (84202933591 / 50000000000000 : ℝ)) (q := (231346966189 / 10000000000000 : ℝ))
      (E := (cell12237 ⟨45, by decide⟩).energy) (xi := (86761970066967 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12237 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12237]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12237])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12237) (a := (10315865631329 / 12500000000000 : ℝ)) (b := (84202933591 / 50000000000000 : ℝ)) (q := (231346966189 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12237])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12237])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12237]

theorem cert12237_46 : CellCertificate 12237 (112511910297001 / 1250000000000000 : ℝ) (858245076501633 / 500000000000000000 : ℝ) (86761970066967 / 2500000000000000 : ℝ)
    (cell12237 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · have h := gap_lower (n := 12237) (a := (16498579061597 / 20000000000000 : ℝ)) (b := (84202933591 / 50000000000000 : ℝ)) (q := (2313473646541 / 100000000000000 : ℝ))
      (E := (cell12237 ⟨46, by decide⟩).energy) (xi := (86761970066967 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12237 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12237]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12237])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12237) (a := (16498579061597 / 20000000000000 : ℝ)) (b := (84202933591 / 50000000000000 : ℝ)) (q := (2313473646541 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12237])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12237])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12237]

theorem cert12237_47 : CellCertificate 12237 (112511910297001 / 1250000000000000 : ℝ) (858245076501633 / 500000000000000000 : ℝ) (86761970066967 / 2500000000000000 : ℝ)
    (cell12237 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · have h := gap_lower (n := 12237) (a := (41229444614327 / 50000000000000 : ℝ)) (b := (84202933591 / 50000000000000 : ℝ)) (q := (2313477657889 / 100000000000000 : ℝ))
      (E := (cell12237 ⟨47, by decide⟩).energy) (xi := (86761970066967 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12237 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12237]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12237])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12237) (a := (41229444614327 / 50000000000000 : ℝ)) (b := (84202933591 / 50000000000000 : ℝ)) (q := (2313477657889 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12237])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12237])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12237]

theorem cert12237_48 : CellCertificate 12237 (112511910297001 / 1250000000000000 : ℝ) (858245076501633 / 500000000000000000 : ℝ) (86761970066967 / 2500000000000000 : ℝ)
    (cell12237 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · have h := gap_lower (n := 12237) (a := (82424906783337 / 100000000000000 : ℝ)) (b := (84202933591 / 50000000000000 : ℝ)) (q := (2313481635921 / 100000000000000 : ℝ))
      (E := (cell12237 ⟨48, by decide⟩).energy) (xi := (86761970066967 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12237 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12237]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12237])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12237) (a := (82424906783337 / 100000000000000 : ℝ)) (b := (84202933591 / 50000000000000 : ℝ)) (q := (2313481635921 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12237])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12237])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12237]

theorem cert12237_49 : CellCertificate 12237 (112511910297001 / 1250000000000000 : ℝ) (858245076501633 / 500000000000000000 : ℝ) (86761970066967 / 2500000000000000 : ℝ)
    (cell12237 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · have h := gap_lower (n := 12237) (a := (82390947942879 / 100000000000000 : ℝ)) (b := (84202933591 / 50000000000000 : ℝ)) (q := (2313485638139 / 100000000000000 : ℝ))
      (E := (cell12237 ⟨49, by decide⟩).energy) (xi := (86761970066967 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12237 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12237]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12237])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12237) (a := (82390947942879 / 100000000000000 : ℝ)) (b := (84202933591 / 50000000000000 : ℝ)) (q := (2313485638139 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12237])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12237])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12237]

theorem cert12237_50 : CellCertificate 12237 (112511910297001 / 1250000000000000 : ℝ) (858245076501633 / 500000000000000000 : ℝ) (86761970066967 / 2500000000000000 : ℝ)
    (cell12237 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · have h := gap_lower (n := 12237) (a := (82357012678271 / 100000000000000 : ℝ)) (b := (84202933591 / 50000000000000 : ℝ)) (q := (2313489604051 / 100000000000000 : ℝ))
      (E := (cell12237 ⟨50, by decide⟩).energy) (xi := (86761970066967 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12237 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12237]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12237])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12237) (a := (82357012678271 / 100000000000000 : ℝ)) (b := (84202933591 / 50000000000000 : ℝ)) (q := (2313489604051 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12237])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12237])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12237]

theorem cert12237_51 : CellCertificate 12237 (112511910297001 / 1250000000000000 : ℝ) (858245076501633 / 500000000000000000 : ℝ) (86761970066967 / 2500000000000000 : ℝ)
    (cell12237 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · have h := gap_lower (n := 12237) (a := (20580775240163 / 25000000000000 : ℝ)) (b := (84202933591 / 50000000000000 : ℝ)) (q := (2313493590773 / 100000000000000 : ℝ))
      (E := (cell12237 ⟨51, by decide⟩).energy) (xi := (86761970066967 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12237 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12237]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12237])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12237) (a := (20580775240163 / 25000000000000 : ℝ)) (b := (84202933591 / 50000000000000 : ℝ)) (q := (2313493590773 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12237])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12237])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12237]

theorem cert12237_52 : CellCertificate 12237 (112511910297001 / 1250000000000000 : ℝ) (858245076501633 / 500000000000000000 : ℝ) (86761970066967 / 2500000000000000 : ℝ)
    (cell12237 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · have h := gap_lower (n := 12237) (a := (41144606380651 / 50000000000000 : ℝ)) (b := (84202933591 / 50000000000000 : ℝ)) (q := (578374399081 / 25000000000000 : ℝ))
      (E := (cell12237 ⟨52, by decide⟩).energy) (xi := (86761970066967 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12237 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12237]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12237])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12237) (a := (41144606380651 / 50000000000000 : ℝ)) (b := (84202933591 / 50000000000000 : ℝ)) (q := (578374399081 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12237])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12237])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12237]

theorem cert12237_53 : CellCertificate 12237 (112511910297001 / 1250000000000000 : ℝ) (858245076501633 / 500000000000000000 : ℝ) (86761970066967 / 2500000000000000 : ℝ)
    (cell12237 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · have h := gap_lower (n := 12237) (a := (82255348051651 / 100000000000000 : ℝ)) (b := (84202933591 / 50000000000000 : ℝ)) (q := (289187702313 / 12500000000000 : ℝ))
      (E := (cell12237 ⟨53, by decide⟩).energy) (xi := (86761970066967 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12237 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12237]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12237])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12237) (a := (82255348051651 / 100000000000000 : ℝ)) (b := (84202933591 / 50000000000000 : ℝ)) (q := (289187702313 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12237])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12237])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12237]

theorem cert12237_54 : CellCertificate 12237 (112511910297001 / 1250000000000000 : ℝ) (858245076501633 / 500000000000000000 : ℝ) (86761970066967 / 2500000000000000 : ℝ)
    (cell12237 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · have h := gap_lower (n := 12237) (a := (20555376700817 / 25000000000000 : ℝ)) (b := (84202933591 / 50000000000000 : ℝ)) (q := (18508044767 / 800000000000 : ℝ))
      (E := (cell12237 ⟨54, by decide⟩).energy) (xi := (86761970066967 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12237 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12237]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12237])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12237) (a := (20555376700817 / 25000000000000 : ℝ)) (b := (84202933591 / 50000000000000 : ℝ)) (q := (18508044767 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12237])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12237])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12237]

theorem cert12237_55 : CellCertificate 12237 (112511910297001 / 1250000000000000 : ℝ) (858245076501633 / 500000000000000000 : ℝ) (86761970066967 / 2500000000000000 : ℝ)
    (cell12237 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · have h := gap_lower (n := 12237) (a := (82187688987867 / 100000000000000 : ℝ)) (b := (84202933591 / 50000000000000 : ℝ)) (q := (2313509584797 / 100000000000000 : ℝ))
      (E := (cell12237 ⟨55, by decide⟩).energy) (xi := (86761970066967 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12237 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12237]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12237])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12237) (a := (82187688987867 / 100000000000000 : ℝ)) (b := (84202933591 / 50000000000000 : ℝ)) (q := (2313509584797 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12237])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12237])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12237]

theorem cert12237_56 : CellCertificate 12237 (112511910297001 / 1250000000000000 : ℝ) (858245076501633 / 500000000000000000 : ℝ) (86761970066967 / 2500000000000000 : ℝ)
    (cell12237 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · have h := gap_lower (n := 12237) (a := (41076947288651 / 50000000000000 : ℝ)) (b := (84202933591 / 50000000000000 : ℝ)) (q := (2313513582439 / 100000000000000 : ℝ))
      (E := (cell12237 ⟨56, by decide⟩).energy) (xi := (86761970066967 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12237 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12237]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12237])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12237) (a := (41076947288651 / 50000000000000 : ℝ)) (b := (84202933591 / 50000000000000 : ℝ)) (q := (2313513582439 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12237])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12237])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12237]

theorem cert12237_57 : CellCertificate 12237 (112511910297001 / 1250000000000000 : ℝ) (858245076501633 / 500000000000000000 : ℝ) (86761970066967 / 2500000000000000 : ℝ)
    (cell12237 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · have h := gap_lower (n := 12237) (a := (82120123543569 / 100000000000000 : ℝ)) (b := (84202933591 / 50000000000000 : ℝ)) (q := (14459484911 / 625000000000 : ℝ))
      (E := (cell12237 ⟨57, by decide⟩).energy) (xi := (86761970066967 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12237 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12237]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12237])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12237) (a := (82120123543569 / 100000000000000 : ℝ)) (b := (84202933591 / 50000000000000 : ℝ)) (q := (14459484911 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12237])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12237])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12237]

theorem cert12237_58 : CellCertificate 12237 (112511910297001 / 1250000000000000 : ℝ) (858245076501633 / 500000000000000000 : ℝ) (86761970066967 / 2500000000000000 : ℝ)
    (cell12237 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · have h := gap_lower (n := 12237) (a := (20521593964701 / 25000000000000 : ℝ)) (b := (84202933591 / 50000000000000 : ℝ)) (q := (2313521591509 / 100000000000000 : ℝ))
      (E := (cell12237 ⟨58, by decide⟩).energy) (xi := (86761970066967 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12237 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12237]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12237])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12237) (a := (20521593964701 / 25000000000000 : ℝ)) (b := (84202933591 / 50000000000000 : ℝ)) (q := (2313521591509 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12237])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12237])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12237]

theorem cert12237_59 : CellCertificate 12237 (112511910297001 / 1250000000000000 : ℝ) (858245076501633 / 500000000000000000 : ℝ) (86761970066967 / 2500000000000000 : ℝ)
    (cell12237 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · have h := gap_lower (n := 12237) (a := (82052651495283 / 100000000000000 : ℝ)) (b := (84202933591 / 50000000000000 : ℝ)) (q := (2313525596227 / 100000000000000 : ℝ))
      (E := (cell12237 ⟨59, by decide⟩).energy) (xi := (86761970066967 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12237 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12237]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12237])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12237) (a := (82052651495283 / 100000000000000 : ℝ)) (b := (84202933591 / 50000000000000 : ℝ)) (q := (2313525596227 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12237])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12237])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12237]

theorem cert12238_40 : CellCertificate 12238 (1125081598669 / 12500000000000 : ℝ) (171634984610509 / 100000000000000000 : ℝ) (173509379687279 / 5000000000000000 : ℝ)
    (cell12238 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · have h := gap_lower (n := 12238) (a := (41348713323193 / 50000000000000 : ℝ)) (b := (168391921239 / 100000000000000 : ℝ)) (q := (462660265373 / 20000000000000 : ℝ))
      (E := (cell12238 ⟨40, by decide⟩).energy) (xi := (173509379687279 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12238 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12238]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12238])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12238) (a := (41348713323193 / 50000000000000 : ℝ)) (b := (168391921239 / 100000000000000 : ℝ)) (q := (462660265373 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12238])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12238])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12238]

theorem cert12238_41 : CellCertificate 12238 (1125081598669 / 12500000000000 : ℝ) (171634984610509 / 100000000000000000 : ℝ) (173509379687279 / 5000000000000000 : ℝ)
    (cell12238 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · have h := gap_lower (n := 12238) (a := (1653265569257 / 2000000000000 : ℝ)) (b := (168391921239 / 100000000000000 : ℝ)) (q := (2313305310311 / 100000000000000 : ℝ))
      (E := (cell12238 ⟨41, by decide⟩).energy) (xi := (173509379687279 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12238 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12238]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12238])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12238) (a := (1653265569257 / 2000000000000 : ℝ)) (b := (168391921239 / 100000000000000 : ℝ)) (q := (2313305310311 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12238])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12238])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12238]

theorem cert12238_42 : CellCertificate 12238 (1125081598669 / 12500000000000 : ℝ) (171634984610509 / 100000000000000000 : ℝ) (173509379687279 / 5000000000000000 : ℝ)
    (cell12238 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · have h := gap_lower (n := 12238) (a := (41314577045473 / 50000000000000 : ℝ)) (b := (168391921239 / 100000000000000 : ℝ)) (q := (462661864733 / 20000000000000 : ℝ))
      (E := (cell12238 ⟨42, by decide⟩).energy) (xi := (173509379687279 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12238 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12238]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12238])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12238) (a := (41314577045473 / 50000000000000 : ℝ)) (b := (168391921239 / 100000000000000 : ℝ)) (q := (462661864733 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12238])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12238])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12238]

theorem cert12238_43 : CellCertificate 12238 (1125081598669 / 12500000000000 : ℝ) (171634984610509 / 100000000000000000 : ℝ) (173509379687279 / 5000000000000000 : ℝ)
    (cell12238 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · have h := gap_lower (n := 12238) (a := (82595053500623 / 100000000000000 : ℝ)) (b := (168391921239 / 100000000000000 : ℝ)) (q := (1156656654061 / 50000000000000 : ℝ))
      (E := (cell12238 ⟨43, by decide⟩).energy) (xi := (173509379687279 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12238 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12238]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12238])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12238) (a := (82595053500623 / 100000000000000 : ℝ)) (b := (168391921239 / 100000000000000 : ℝ)) (q := (1156656654061 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12238])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12238])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12238]

theorem cert12238_44 : CellCertificate 12238 (1125081598669 / 12500000000000 : ℝ) (171634984610509 / 100000000000000000 : ℝ) (173509379687279 / 5000000000000000 : ℝ)
    (cell12238 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · have h := gap_lower (n := 12238) (a := (10320122082747 / 12500000000000 : ℝ)) (b := (168391921239 / 100000000000000 : ℝ)) (q := (578329315841 / 25000000000000 : ℝ))
      (E := (cell12238 ⟨44, by decide⟩).energy) (xi := (173509379687279 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12238 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12238]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12238])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12238) (a := (10320122082747 / 12500000000000 : ℝ)) (b := (168391921239 / 100000000000000 : ℝ)) (q := (578329315841 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12238])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12238])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12238]

theorem cert12238_45 : CellCertificate 12238 (1125081598669 / 12500000000000 : ℝ) (171634984610509 / 100000000000000000 : ℝ) (173509379687279 / 5000000000000000 : ℝ)
    (cell12238 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · have h := gap_lower (n := 12238) (a := (41263461772629 / 50000000000000 : ℝ)) (b := (168391921239 / 100000000000000 : ℝ)) (q := (28916516331 / 1250000000000 : ℝ))
      (E := (cell12238 ⟨45, by decide⟩).energy) (xi := (173509379687279 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12238 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12238]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12238])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12238) (a := (41263461772629 / 50000000000000 : ℝ)) (b := (168391921239 / 100000000000000 : ℝ)) (q := (28916516331 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12238])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12238])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12238]

theorem cert12238_46 : CellCertificate 12238 (1125081598669 / 12500000000000 : ℝ) (171634984610509 / 100000000000000000 : ℝ) (173509379687279 / 5000000000000000 : ℝ)
    (cell12238 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · have h := gap_lower (n := 12238) (a := (41246447060433 / 50000000000000 : ℝ)) (b := (168391921239 / 100000000000000 : ℝ)) (q := (231332526033 / 10000000000000 : ℝ))
      (E := (cell12238 ⟨46, by decide⟩).energy) (xi := (173509379687279 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12238 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12238]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12238])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12238) (a := (41246447060433 / 50000000000000 : ℝ)) (b := (168391921239 / 100000000000000 : ℝ)) (q := (231332526033 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12238])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12238])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12238]

theorem cert12238_47 : CellCertificate 12238 (1125081598669 / 12500000000000 : ℝ) (171634984610509 / 100000000000000000 : ℝ) (173509379687279 / 5000000000000000 : ℝ)
    (cell12238 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · have h := gap_lower (n := 12238) (a := (82458888359351 / 100000000000000 : ℝ)) (b := (168391921239 / 100000000000000 : ℝ)) (q := (2313329300457 / 100000000000000 : ℝ))
      (E := (cell12238 ⟨47, by decide⟩).energy) (xi := (173509379687279 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12238 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12238]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12238])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12238) (a := (82458888359351 / 100000000000000 : ℝ)) (b := (168391921239 / 100000000000000 : ℝ)) (q := (2313329300457 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12238])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12238])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12238]

theorem cert12238_48 : CellCertificate 12238 (1125081598669 / 12500000000000 : ℝ) (171634984610509 / 100000000000000000 : ℝ) (173509379687279 / 5000000000000000 : ℝ)
    (cell12238 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · have h := gap_lower (n := 12238) (a := (82424906231411 / 100000000000000 : ℝ)) (b := (168391921239 / 100000000000000 : ℝ)) (q := (2313333249143 / 100000000000000 : ℝ))
      (E := (cell12238 ⟨48, by decide⟩).energy) (xi := (173509379687279 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12238 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12238]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12238])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12238) (a := (82424906231411 / 100000000000000 : ℝ)) (b := (168391921239 / 100000000000000 : ℝ)) (q := (2313333249143 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12238])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12238])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12238]

theorem cert12238_49 : CellCertificate 12238 (1125081598669 / 12500000000000 : ℝ) (171634984610509 / 100000000000000000 : ℝ) (173509379687279 / 5000000000000000 : ℝ)
    (cell12238 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · have h := gap_lower (n := 12238) (a := (82390947707891 / 100000000000000 : ℝ)) (b := (168391921239 / 100000000000000 : ℝ)) (q := (57833432041 / 2500000000000 : ℝ))
      (E := (cell12238 ⟨49, by decide⟩).energy) (xi := (173509379687279 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12238 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12238]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12238])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12238) (a := (82390947707891 / 100000000000000 : ℝ)) (b := (168391921239 / 100000000000000 : ℝ)) (q := (57833432041 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12238])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12238])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12238]

theorem cert12238_50 : CellCertificate 12238 (1125081598669 / 12500000000000 : ℝ) (171634984610509 / 100000000000000000 : ℝ) (173509379687279 / 5000000000000000 : ℝ)
    (cell12238 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · have h := gap_lower (n := 12238) (a := (82357012759783 / 100000000000000 : ℝ)) (b := (168391921239 / 100000000000000 : ℝ)) (q := (18072978739 / 781250000000 : ℝ))
      (E := (cell12238 ⟨50, by decide⟩).energy) (xi := (173509379687279 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12238 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12238]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12238])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12238) (a := (82357012759783 / 100000000000000 : ℝ)) (b := (168391921239 / 100000000000000 : ℝ)) (q := (18072978739 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12238])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12238])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12238]

theorem cert12238_51 : CellCertificate 12238 (1125081598669 / 12500000000000 : ℝ) (171634984610509 / 100000000000000000 : ℝ) (173509379687279 / 5000000000000000 : ℝ)
    (cell12238 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · have h := gap_lower (n := 12238) (a := (82323101358227 / 100000000000000 : ℝ)) (b := (168391921239 / 100000000000000 : ℝ)) (q := (578336309539 / 25000000000000 : ℝ))
      (E := (cell12238 ⟨51, by decide⟩).energy) (xi := (173509379687279 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12238 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12238]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12238])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12238) (a := (82323101358227 / 100000000000000 : ℝ)) (b := (168391921239 / 100000000000000 : ℝ)) (q := (578336309539 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12238])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12238])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12238]

theorem cert12238_52 : CellCertificate 12238 (1125081598669 / 12500000000000 : ℝ) (171634984610509 / 100000000000000000 : ℝ) (173509379687279 / 5000000000000000 : ℝ)
    (cell12238 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · have h := gap_lower (n := 12238) (a := (41144606737253 / 50000000000000 : ℝ)) (b := (168391921239 / 100000000000000 : ℝ)) (q := (2313349276241 / 100000000000000 : ℝ))
      (E := (cell12238 ⟨52, by decide⟩).energy) (xi := (173509379687279 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12238 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12238]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12238])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12238) (a := (41144606737253 / 50000000000000 : ℝ)) (b := (168391921239 / 100000000000000 : ℝ)) (q := (2313349276241 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12238])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12238])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12238]

theorem cert12238_53 : CellCertificate 12238 (1125081598669 / 12500000000000 : ℝ) (171634984610509 / 100000000000000000 : ℝ) (173509379687279 / 5000000000000000 : ℝ)
    (cell12238 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · have h := gap_lower (n := 12238) (a := (82255349080047 / 100000000000000 : ℝ)) (b := (168391921239 / 100000000000000 : ℝ)) (q := (2313353272709 / 100000000000000 : ℝ))
      (E := (cell12238 ⟨53, by decide⟩).energy) (xi := (173509379687279 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12238 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12238]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12238])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12238) (a := (82255349080047 / 100000000000000 : ℝ)) (b := (168391921239 / 100000000000000 : ℝ)) (q := (2313353272709 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12238])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12238])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12238]

theorem cert12238_54 : CellCertificate 12238 (1125081598669 / 12500000000000 : ℝ) (171634984610509 / 100000000000000000 : ℝ) (173509379687279 / 5000000000000000 : ℝ)
    (cell12238 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · have h := gap_lower (n := 12238) (a := (82221508146421 / 100000000000000 : ℝ)) (b := (168391921239 / 100000000000000 : ℝ)) (q := (2313357225079 / 100000000000000 : ℝ))
      (E := (cell12238 ⟨54, by decide⟩).energy) (xi := (173509379687279 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12238 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12238]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12238])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12238) (a := (82221508146421 / 100000000000000 : ℝ)) (b := (168391921239 / 100000000000000 : ℝ)) (q := (2313357225079 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12238])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12238])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12238]

theorem cert12238_55 : CellCertificate 12238 (1125081598669 / 12500000000000 : ℝ) (171634984610509 / 100000000000000000 : ℝ) (173509379687279 / 5000000000000000 : ℝ)
    (cell12238 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · have h := gap_lower (n := 12238) (a := (2568365332667 / 3125000000000 : ℝ)) (b := (168391921239 / 100000000000000 : ℝ)) (q := (1156680624381 / 50000000000000 : ℝ))
      (E := (cell12238 ⟨55, by decide⟩).energy) (xi := (173509379687279 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12238 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12238]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12238])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12238) (a := (2568365332667 / 3125000000000 : ℝ)) (b := (168391921239 / 100000000000000 : ℝ)) (q := (1156680624381 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12238])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12238])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12238]

theorem cert12238_56 : CellCertificate 12238 (1125081598669 / 12500000000000 : ℝ) (171634984610509 / 100000000000000000 : ℝ) (173509379687279 / 5000000000000000 : ℝ)
    (cell12238 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · have h := gap_lower (n := 12238) (a := (82153896548669 / 100000000000000 : ℝ)) (b := (168391921239 / 100000000000000 : ℝ)) (q := (2313365222847 / 100000000000000 : ℝ))
      (E := (cell12238 ⟨56, by decide⟩).energy) (xi := (173509379687279 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12238 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12238]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12238])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12238) (a := (82153896548669 / 100000000000000 : ℝ)) (b := (168391921239 / 100000000000000 : ℝ)) (q := (2313365222847 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12238])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12238])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12238]

theorem cert12238_57 : CellCertificate 12238 (1125081598669 / 12500000000000 : ℝ) (171634984610509 / 100000000000000000 : ℝ) (173509379687279 / 5000000000000000 : ℝ)
    (cell12238 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · have h := gap_lower (n := 12238) (a := (16424025165679 / 20000000000000 : ℝ)) (b := (168391921239 / 100000000000000 : ℝ)) (q := (2313369262417 / 100000000000000 : ℝ))
      (E := (cell12238 ⟨57, by decide⟩).energy) (xi := (173509379687279 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12238 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12238]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12238])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12238) (a := (16424025165679 / 20000000000000 : ℝ)) (b := (168391921239 / 100000000000000 : ℝ)) (q := (2313369262417 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12238])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12238])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12238]

theorem cert12238_58 : CellCertificate 12238 (1125081598669 / 12500000000000 : ℝ) (171634984610509 / 100000000000000000 : ℝ) (173509379687279 / 5000000000000000 : ℝ)
    (cell12238 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · have h := gap_lower (n := 12238) (a := (82086378456657 / 100000000000000 : ℝ)) (b := (168391921239 / 100000000000000 : ℝ)) (q := (2313373246047 / 100000000000000 : ℝ))
      (E := (cell12238 ⟨58, by decide⟩).energy) (xi := (173509379687279 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12238 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12238]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12238])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12238) (a := (82086378456657 / 100000000000000 : ℝ)) (b := (168391921239 / 100000000000000 : ℝ)) (q := (2313373246047 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12238])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12238])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12238]

theorem cert12238_59 : CellCertificate 12238 (1125081598669 / 12500000000000 : ℝ) (171634984610509 / 100000000000000000 : ℝ) (173509379687279 / 5000000000000000 : ℝ)
    (cell12238 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · have h := gap_lower (n := 12238) (a := (20513163601433 / 25000000000000 : ℝ)) (b := (168391921239 / 100000000000000 : ℝ)) (q := (2313377229353 / 100000000000000 : ℝ))
      (E := (cell12238 ⟨59, by decide⟩).energy) (xi := (173509379687279 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12238 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12238]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12238])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12238) (a := (20513163601433 / 25000000000000 : ℝ)) (b := (168391921239 / 100000000000000 : ℝ)) (q := (2313377229353 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12238])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12238])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12238]

theorem cert12239_40 : CellCertificate 12239 (900035280219407 / 10000000000000000 : ℝ) (171620956214257 / 100000000000000000 : ℝ) (346989643495939 / 10000000000000000 : ℝ)
    (cell12239 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · have h := gap_lower (n := 12239) (a := (20674355886027 / 25000000000000 : ℝ)) (b := (168377977637 / 100000000000000 : ℝ)) (q := (2313153073859 / 100000000000000 : ℝ))
      (E := (cell12239 ⟨40, by decide⟩).energy) (xi := (346989643495939 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12239 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12239]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12239])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12239) (a := (20674355886027 / 25000000000000 : ℝ)) (b := (168377977637 / 100000000000000 : ℝ)) (q := (2313153073859 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12239])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12239])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12239]

theorem cert12239_41 : CellCertificate 12239 (900035280219407 / 10000000000000000 : ℝ) (171620956214257 / 100000000000000000 : ℝ) (346989643495939 / 10000000000000000 : ℝ)
    (cell12239 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · have h := gap_lower (n := 12239) (a := (82663275680999 / 100000000000000 : ℝ)) (b := (168377977637 / 100000000000000 : ℝ)) (q := (2313157022931 / 100000000000000 : ℝ))
      (E := (cell12239 ⟨41, by decide⟩).energy) (xi := (346989643495939 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12239 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12239]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12239])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12239) (a := (82663275680999 / 100000000000000 : ℝ)) (b := (168377977637 / 100000000000000 : ℝ)) (q := (2313157022931 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12239])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12239])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12239]

theorem cert12239_42 : CellCertificate 12239 (900035280219407 / 10000000000000000 : ℝ) (171620956214257 / 100000000000000000 : ℝ) (346989643495939 / 10000000000000000 : ℝ)
    (cell12239 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · have h := gap_lower (n := 12239) (a := (82629151629079 / 100000000000000 : ℝ)) (b := (168377977637 / 100000000000000 : ℝ)) (q := (1156580530689 / 50000000000000 : ℝ))
      (E := (cell12239 ⟨42, by decide⟩).energy) (xi := (346989643495939 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12239 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12239]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12239])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12239) (a := (82629151629079 / 100000000000000 : ℝ)) (b := (168377977637 / 100000000000000 : ℝ)) (q := (1156580530689 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12239])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12239])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12239]

theorem cert12239_43 : CellCertificate 12239 (900035280219407 / 10000000000000000 : ℝ) (171620956214257 / 100000000000000000 : ℝ) (346989643495939 / 10000000000000000 : ℝ)
    (cell12239 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · have h := gap_lower (n := 12239) (a := (10324381419787 / 12500000000000 : ℝ)) (b := (168377977637 / 100000000000000 : ℝ)) (q := (578291253231 / 25000000000000 : ℝ))
      (E := (cell12239 ⟨43, by decide⟩).energy) (xi := (346989643495939 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12239 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12239]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12239])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12239) (a := (10324381419787 / 12500000000000 : ℝ)) (b := (168377977637 / 100000000000000 : ℝ)) (q := (578291253231 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12239])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12239])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12239]

theorem cert12239_44 : CellCertificate 12239 (900035280219407 / 10000000000000000 : ℝ) (171620956214257 / 100000000000000000 : ℝ) (346989643495939 / 10000000000000000 : ℝ)
    (cell12239 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · have h := gap_lower (n := 12239) (a := (82560974838747 / 100000000000000 : ℝ)) (b := (168377977637 / 100000000000000 : ℝ)) (q := (57829226339 / 2500000000000 : ℝ))
      (E := (cell12239 ⟨44, by decide⟩).energy) (xi := (346989643495939 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12239 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12239]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12239])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12239) (a := (82560974838747 / 100000000000000 : ℝ)) (b := (168377977637 / 100000000000000 : ℝ)) (q := (57829226339 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12239])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12239])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12239]

theorem cert12239_45 : CellCertificate 12239 (900035280219407 / 10000000000000000 : ℝ) (171620956214257 / 100000000000000000 : ℝ) (346989643495939 / 10000000000000000 : ℝ)
    (cell12239 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · have h := gap_lower (n := 12239) (a := (16505384408137 / 20000000000000 : ℝ)) (b := (168377977637 / 100000000000000 : ℝ)) (q := (231317300643 / 10000000000000 : ℝ))
      (E := (cell12239 ⟨45, by decide⟩).energy) (xi := (346989643495939 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12239 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12239]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12239])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12239) (a := (16505384408137 / 20000000000000 : ℝ)) (b := (168377977637 / 100000000000000 : ℝ)) (q := (231317300643 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12239])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12239])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12239]

theorem cert12239_46 : CellCertificate 12239 (900035280219407 / 10000000000000000 : ℝ) (171620956214257 / 100000000000000000 : ℝ) (346989643495939 / 10000000000000000 : ℝ)
    (cell12239 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · have h := gap_lower (n := 12239) (a := (82492892934509 / 100000000000000 : ℝ)) (b := (168377977637 / 100000000000000 : ℝ)) (q := (92527081889 / 4000000000000 : ℝ))
      (E := (cell12239 ⟨46, by decide⟩).energy) (xi := (346989643495939 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12239 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12239]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12239])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12239) (a := (82492892934509 / 100000000000000 : ℝ)) (b := (168377977637 / 100000000000000 : ℝ)) (q := (92527081889 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12239])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12239])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12239]

theorem cert12239_47 : CellCertificate 12239 (900035280219407 / 10000000000000000 : ℝ) (171620956214257 / 100000000000000000 : ℝ) (346989643495939 / 10000000000000000 : ℝ)
    (cell12239 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · have h := gap_lower (n := 12239) (a := (8245888749077 / 10000000000000 : ℝ)) (b := (168377977637 / 100000000000000 : ℝ)) (q := (1156590499257 / 50000000000000 : ℝ))
      (E := (cell12239 ⟨47, by decide⟩).energy) (xi := (346989643495939 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12239 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12239]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12239])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12239) (a := (8245888749077 / 10000000000000 : ℝ)) (b := (168377977637 / 100000000000000 : ℝ)) (q := (1156590499257 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12239])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12239])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12239]

theorem cert12239_48 : CellCertificate 12239 (900035280219407 / 10000000000000000 : ℝ) (171620956214257 / 100000000000000000 : ℝ) (346989643495939 / 10000000000000000 : ℝ)
    (cell12239 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · have h := gap_lower (n := 12239) (a := (41212452840083 / 50000000000000 : ℝ)) (b := (168377977637 / 100000000000000 : ℝ)) (q := (462637007139 / 20000000000000 : ℝ))
      (E := (cell12239 ⟨48, by decide⟩).energy) (xi := (346989643495939 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12239 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12239]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12239])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12239) (a := (41212452840083 / 50000000000000 : ℝ)) (b := (168377977637 / 100000000000000 : ℝ)) (q := (462637007139 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12239])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12239])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12239]

theorem cert12239_49 : CellCertificate 12239 (900035280219407 / 10000000000000000 : ℝ) (171620956214257 / 100000000000000000 : ℝ) (346989643495939 / 10000000000000000 : ℝ)
    (cell12239 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · have h := gap_lower (n := 12239) (a := (10298868434193 / 12500000000000 : ℝ)) (b := (168377977637 / 100000000000000 : ℝ)) (q := (2313188980759 / 100000000000000 : ℝ))
      (E := (cell12239 ⟨49, by decide⟩).energy) (xi := (346989643495939 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12239 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12239]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12239])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12239) (a := (10298868434193 / 12500000000000 : ℝ)) (b := (168377977637 / 100000000000000 : ℝ)) (q := (2313188980759 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12239])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12239])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12239]

theorem cert12239_50 : CellCertificate 12239 (900035280219407 / 10000000000000000 : ℝ) (171620956214257 / 100000000000000000 : ℝ) (346989643495939 / 10000000000000000 : ℝ)
    (cell12239 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · have h := gap_lower (n := 12239) (a := (41178506420949 / 50000000000000 : ℝ)) (b := (168377977637 / 100000000000000 : ℝ)) (q := (462638601763 / 20000000000000 : ℝ))
      (E := (cell12239 ⟨50, by decide⟩).energy) (xi := (346989643495939 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12239 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12239]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12239])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12239) (a := (41178506420949 / 50000000000000 : ℝ)) (b := (168377977637 / 100000000000000 : ℝ)) (q := (462638601763 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12239])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12239])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12239]

theorem cert12239_51 : CellCertificate 12239 (900035280219407 / 10000000000000000 : ℝ) (171620956214257 / 100000000000000000 : ℝ) (346989643495939 / 10000000000000000 : ℝ)
    (cell12239 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · have h := gap_lower (n := 12239) (a := (41161550878183 / 50000000000000 : ℝ)) (b := (168377977637 / 100000000000000 : ℝ)) (q := (2313197000243 / 100000000000000 : ℝ))
      (E := (cell12239 ⟨51, by decide⟩).energy) (xi := (346989643495939 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12239 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12239]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12239])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12239) (a := (41161550878183 / 50000000000000 : ℝ)) (b := (168377977637 / 100000000000000 : ℝ)) (q := (2313197000243 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12239])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12239])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12239]

theorem cert12239_52 : CellCertificate 12239 (900035280219407 / 10000000000000000 : ℝ) (171620956214257 / 100000000000000000 : ℝ) (346989643495939 / 10000000000000000 : ℝ)
    (cell12239 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · have h := gap_lower (n := 12239) (a := (10286151773529 / 12500000000000 : ℝ)) (b := (168377977637 / 100000000000000 : ℝ)) (q := (231320101197 / 10000000000000 : ℝ))
      (E := (cell12239 ⟨52, by decide⟩).energy) (xi := (346989643495939 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12239 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12239]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12239])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12239) (a := (10286151773529 / 12500000000000 : ℝ)) (b := (168377977637 / 100000000000000 : ℝ)) (q := (231320101197 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12239])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12239])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12239]

theorem cert12239_53 : CellCertificate 12239 (900035280219407 / 10000000000000000 : ℝ) (171620956214257 / 100000000000000000 : ℝ) (346989643495939 / 10000000000000000 : ℝ)
    (cell12239 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · have h := gap_lower (n := 12239) (a := (41127675054463 / 50000000000000 : ℝ)) (b := (168377977637 / 100000000000000 : ℝ)) (q := (2313204982789 / 100000000000000 : ℝ))
      (E := (cell12239 ⟨53, by decide⟩).energy) (xi := (346989643495939 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12239 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12239]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12239])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12239) (a := (41127675054463 / 50000000000000 : ℝ)) (b := (168377977637 / 100000000000000 : ℝ)) (q := (2313204982789 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12239])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12239])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12239]

theorem cert12239_54 : CellCertificate 12239 (900035280219407 / 10000000000000000 : ℝ) (171620956214257 / 100000000000000000 : ℝ) (346989643495939 / 10000000000000000 : ℝ)
    (cell12239 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · have h := gap_lower (n := 12239) (a := (41110754745009 / 50000000000000 : ℝ)) (b := (168377977637 / 100000000000000 : ℝ)) (q := (578302242313 / 25000000000000 : ℝ))
      (E := (cell12239 ⟨54, by decide⟩).energy) (xi := (346989643495939 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12239 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12239]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12239])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12239) (a := (41110754745009 / 50000000000000 : ℝ)) (b := (168377977637 / 100000000000000 : ℝ)) (q := (578302242313 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12239])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12239])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12239]

theorem cert12239_55 : CellCertificate 12239 (900035280219407 / 10000000000000000 : ℝ) (171620956214257 / 100000000000000000 : ℝ) (346989643495939 / 10000000000000000 : ℝ)
    (cell12239 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · have h := gap_lower (n := 12239) (a := (3287507692129 / 4000000000000 : ℝ)) (b := (168377977637 / 100000000000000 : ℝ)) (q := (578303242183 / 25000000000000 : ℝ))
      (E := (cell12239 ⟨55, by decide⟩).energy) (xi := (346989643495939 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12239 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12239]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12239])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12239) (a := (3287507692129 / 4000000000000 : ℝ)) (b := (168377977637 / 100000000000000 : ℝ)) (q := (578303242183 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12239])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12239])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12239]

theorem cert12239_56 : CellCertificate 12239 (900035280219407 / 10000000000000000 : ℝ) (171620956214257 / 100000000000000000 : ℝ) (346989643495939 / 10000000000000000 : ℝ)
    (cell12239 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · have h := gap_lower (n := 12239) (a := (41076949260201 / 50000000000000 : ℝ)) (b := (168377977637 / 100000000000000 : ℝ)) (q := (2313216978397 / 100000000000000 : ℝ))
      (E := (cell12239 ⟨56, by decide⟩).energy) (xi := (346989643495939 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12239 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12239]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12239])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12239) (a := (41076949260201 / 50000000000000 : ℝ)) (b := (168377977637 / 100000000000000 : ℝ)) (q := (2313216978397 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12239])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12239])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12239]

theorem cert12239_57 : CellCertificate 12239 (900035280219407 / 10000000000000000 : ℝ) (171620956214257 / 100000000000000000 : ℝ) (346989643495939 / 10000000000000000 : ℝ)
    (cell12239 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · have h := gap_lower (n := 12239) (a := (41060064056773 / 50000000000000 : ℝ)) (b := (168377977637 / 100000000000000 : ℝ)) (q := (1156610497603 / 50000000000000 : ℝ))
      (E := (cell12239 ⟨57, by decide⟩).energy) (xi := (346989643495939 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12239 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12239]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12239])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12239) (a := (41060064056773 / 50000000000000 : ℝ)) (b := (168377977637 / 100000000000000 : ℝ)) (q := (1156610497603 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12239])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12239])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12239]

theorem cert12239_58 : CellCertificate 12239 (900035280219407 / 10000000000000000 : ℝ) (171620956214257 / 100000000000000000 : ℝ) (346989643495939 / 10000000000000000 : ℝ)
    (cell12239 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · have h := gap_lower (n := 12239) (a := (20521595263699 / 25000000000000 : ℝ)) (b := (168377977637 / 100000000000000 : ℝ)) (q := (2313224956781 / 100000000000000 : ℝ))
      (E := (cell12239 ⟨58, by decide⟩).energy) (xi := (346989643495939 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12239 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12239]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12239])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12239) (a := (20521595263699 / 25000000000000 : ℝ)) (b := (168377977637 / 100000000000000 : ℝ)) (q := (2313224956781 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12239])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12239])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12239]

theorem cert12239_59 : CellCertificate 12239 (900035280219407 / 10000000000000000 : ℝ) (171620956214257 / 100000000000000000 : ℝ) (346989643495939 / 10000000000000000 : ℝ)
    (cell12239 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · have h := gap_lower (n := 12239) (a := (82052657316427 / 100000000000000 : ℝ)) (b := (168377977637 / 100000000000000 : ℝ)) (q := (1156614488943 / 50000000000000 : ℝ))
      (E := (cell12239 ⟨59, by decide⟩).energy) (xi := (346989643495939 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12239 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12239]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12239])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12239) (a := (82052657316427 / 100000000000000 : ℝ)) (b := (168377977637 / 100000000000000 : ℝ)) (q := (1156614488943 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12239])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12239])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12239]

theorem cert12240_40 : CellCertificate 12240 (900005286227463 / 10000000000000000 : ℝ) (343213860222017 / 200000000000000000 : ℝ) (69392106526107 / 2000000000000000 : ℝ)
    (cell12240 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · have h := gap_lower (n := 12240) (a := (82697420442833 / 100000000000000 : ℝ)) (b := (1346912291 / 800000000000 : ℝ)) (q := (2313004875889 / 100000000000000 : ℝ))
      (E := (cell12240 ⟨40, by decide⟩).energy) (xi := (69392106526107 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12240 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12240]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12240])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12240) (a := (82697420442833 / 100000000000000 : ℝ)) (b := (1346912291 / 800000000000 : ℝ)) (q := (2313004875889 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12240])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12240])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12240]

theorem cert12240_41 : CellCertificate 12240 (900005286227463 / 10000000000000000 : ℝ) (343213860222017 / 200000000000000000 : ℝ) (69392106526107 / 2000000000000000 : ℝ)
    (cell12240 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · have h := gap_lower (n := 12240) (a := (82663272900111 / 100000000000000 : ℝ)) (b := (1346912291 / 800000000000 : ℝ)) (q := (72281526543 / 3125000000000 : ℝ))
      (E := (cell12240 ⟨41, by decide⟩).energy) (xi := (69392106526107 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12240 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12240]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12240])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12240) (a := (82663272900111 / 100000000000000 : ℝ)) (b := (1346912291 / 800000000000 : ℝ)) (q := (72281526543 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12240])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12240])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12240]

theorem cert12240_42 : CellCertificate 12240 (900005286227463 / 10000000000000000 : ℝ) (343213860222017 / 200000000000000000 : ℝ) (69392106526107 / 2000000000000000 : ℝ)
    (cell12240 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · have h := gap_lower (n := 12240) (a := (41314574584067 / 50000000000000 : ℝ)) (b := (1346912291 / 800000000000 : ℝ)) (q := (2313012854257 / 100000000000000 : ℝ))
      (E := (cell12240 ⟨42, by decide⟩).energy) (xi := (69392106526107 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12240 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12240]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12240])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12240) (a := (41314574584067 / 50000000000000 : ℝ)) (b := (1346912291 / 800000000000 : ℝ)) (q := (2313012854257 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12240])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12240])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12240]

theorem cert12240_43 : CellCertificate 12240 (900005286227463 / 10000000000000000 : ℝ) (343213860222017 / 200000000000000000 : ℝ) (69392106526107 / 2000000000000000 : ℝ)
    (cell12240 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · have h := gap_lower (n := 12240) (a := (82595049216851 / 100000000000000 : ℝ)) (b := (1346912291 / 800000000000 : ℝ)) (q := (2313016831727 / 100000000000000 : ℝ))
      (E := (cell12240 ⟨43, by decide⟩).energy) (xi := (69392106526107 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12240 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12240]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12240])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12240) (a := (82595049216851 / 100000000000000 : ℝ)) (b := (1346912291 / 800000000000 : ℝ)) (q := (2313016831727 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12240])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12240])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12240]

theorem cert12240_44 : CellCertificate 12240 (900005286227463 / 10000000000000000 : ℝ) (343213860222017 / 200000000000000000 : ℝ) (69392106526107 / 2000000000000000 : ℝ)
    (cell12240 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · have h := gap_lower (n := 12240) (a := (2064024325409 / 2500000000000 : ℝ)) (b := (1346912291 / 800000000000 : ℝ)) (q := (1156510420129 / 50000000000000 : ℝ))
      (E := (cell12240 ⟨44, by decide⟩).energy) (xi := (69392106526107 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12240 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12240]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12240])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12240) (a := (2064024325409 / 2500000000000 : ℝ)) (b := (1346912291 / 800000000000 : ℝ)) (q := (1156510420129 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12240])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12240])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12240]

theorem cert12240_45 : CellCertificate 12240 (900005286227463 / 10000000000000000 : ℝ) (343213860222017 / 200000000000000000 : ℝ) (69392106526107 / 2000000000000000 : ℝ)
    (cell12240 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · have h := gap_lower (n := 12240) (a := (41263460268457 / 50000000000000 : ℝ)) (b := (1346912291 / 800000000000 : ℝ)) (q := (2313024820557 / 100000000000000 : ℝ))
      (E := (cell12240 ⟨45, by decide⟩).energy) (xi := (69392106526107 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12240 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12240]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12240])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12240) (a := (41263460268457 / 50000000000000 : ℝ)) (b := (1346912291 / 800000000000 : ℝ)) (q := (2313024820557 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12240])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12240])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12240]

theorem cert12240_46 : CellCertificate 12240 (900005286227463 / 10000000000000000 : ℝ) (343213860222017 / 200000000000000000 : ℝ) (69392106526107 / 2000000000000000 : ℝ)
    (cell12240 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · have h := gap_lower (n := 12240) (a := (82492891748913 / 100000000000000 : ℝ)) (b := (1346912291 / 800000000000 : ℝ)) (q := (1156514415353 / 50000000000000 : ℝ))
      (E := (cell12240 ⟨46, by decide⟩).energy) (xi := (69392106526107 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12240 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12240]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12240])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12240) (a := (82492891748913 / 100000000000000 : ℝ)) (b := (1346912291 / 800000000000 : ℝ)) (q := (1156514415353 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12240])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12240])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12240]

theorem cert12240_47 : CellCertificate 12240 (900005286227463 / 10000000000000000 : ℝ) (343213860222017 / 200000000000000000 : ℝ) (69392106526107 / 2000000000000000 : ℝ)
    (cell12240 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · have h := gap_lower (n := 12240) (a := (8245888662291 / 10000000000000 : ℝ)) (b := (1346912291 / 800000000000 : ℝ)) (q := (2313032810927 / 100000000000000 : ℝ))
      (E := (cell12240 ⟨47, by decide⟩).energy) (xi := (69392106526107 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12240 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12240]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12240])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12240) (a := (8245888662291 / 10000000000000 : ℝ)) (b := (1346912291 / 800000000000 : ℝ)) (q := (2313032810927 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12240])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12240])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12240]

theorem cert12240_48 : CellCertificate 12240 (900005286227463 / 10000000000000000 : ℝ) (343213860222017 / 200000000000000000 : ℝ) (69392106526107 / 2000000000000000 : ℝ)
    (cell12240 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · have h := gap_lower (n := 12240) (a := (82424905129603 / 100000000000000 : ℝ)) (b := (1346912291 / 800000000000 : ℝ)) (q := (2313036818913 / 100000000000000 : ℝ))
      (E := (cell12240 ⟨48, by decide⟩).energy) (xi := (69392106526107 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12240 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12240]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12240])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12240) (a := (82424905129603 / 100000000000000 : ℝ)) (b := (1346912291 / 800000000000 : ℝ)) (q := (2313036818913 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12240])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12240])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12240]

theorem cert12240_49 : CellCertificate 12240 (900005286227463 / 10000000000000000 : ℝ) (343213860222017 / 200000000000000000 : ℝ) (69392106526107 / 2000000000000000 : ℝ)
    (cell12240 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · have h := gap_lower (n := 12240) (a := (514943420249 / 625000000000 : ℝ)) (b := (1346912291 / 800000000000 : ℝ)) (q := (2313040853321 / 100000000000000 : ℝ))
      (E := (cell12240 ⟨49, by decide⟩).energy) (xi := (69392106526107 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12240 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12240]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12240])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12240) (a := (514943420249 / 625000000000 : ℝ)) (b := (1346912291 / 800000000000 : ℝ)) (q := (2313040853321 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12240])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12240])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12240]

theorem cert12240_50 : CellCertificate 12240 (900005286227463 / 10000000000000000 : ℝ) (343213860222017 / 200000000000000000 : ℝ) (69392106526107 / 2000000000000000 : ℝ)
    (cell12240 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · have h := gap_lower (n := 12240) (a := (41178506462307 / 50000000000000 : ℝ)) (b := (1346912291 / 800000000000 : ℝ)) (q := (1156522426829 / 50000000000000 : ℝ))
      (E := (cell12240 ⟨50, by decide⟩).energy) (xi := (69392106526107 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12240 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12240]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12240])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12240) (a := (41178506462307 / 50000000000000 : ℝ)) (b := (1346912291 / 800000000000 : ℝ)) (q := (1156522426829 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12240])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12240])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12240]

theorem cert12240_51 : CellCertificate 12240 (900005286227463 / 10000000000000000 : ℝ) (343213860222017 / 200000000000000000 : ℝ) (69392106526107 / 2000000000000000 : ℝ)
    (cell12240 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · have h := gap_lower (n := 12240) (a := (41161551077533 / 50000000000000 : ℝ)) (b := (1346912291 / 800000000000 : ℝ)) (q := (2313048818079 / 100000000000000 : ℝ))
      (E := (cell12240 ⟨51, by decide⟩).energy) (xi := (69392106526107 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12240 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12240]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12240])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12240) (a := (41161551077533 / 50000000000000 : ℝ)) (b := (1346912291 / 800000000000 : ℝ)) (q := (2313048818079 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12240])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12240])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12240]

theorem cert12240_52 : CellCertificate 12240 (900005286227463 / 10000000000000000 : ℝ) (343213860222017 / 200000000000000000 : ℝ) (69392106526107 / 2000000000000000 : ℝ)
    (cell12240 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · have h := gap_lower (n := 12240) (a := (82289214902481 / 100000000000000 : ℝ)) (b := (1346912291 / 800000000000 : ℝ)) (q := (2313052803511 / 100000000000000 : ℝ))
      (E := (cell12240 ⟨52, by decide⟩).energy) (xi := (69392106526107 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12240 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12240]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12240])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12240) (a := (82289214902481 / 100000000000000 : ℝ)) (b := (1346912291 / 800000000000 : ℝ)) (q := (2313052803511 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12240])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12240])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12240]

theorem cert12240_53 : CellCertificate 12240 (900005286227463 / 10000000000000000 : ℝ) (343213860222017 / 200000000000000000 : ℝ) (69392106526107 / 2000000000000000 : ℝ)
    (cell12240 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · have h := gap_lower (n := 12240) (a := (5140959446143 / 6250000000000 : ℝ)) (b := (1346912291 / 800000000000 : ℝ)) (q := (2313056807753 / 100000000000000 : ℝ))
      (E := (cell12240 ⟨53, by decide⟩).energy) (xi := (69392106526107 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12240 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12240]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12240])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12240) (a := (5140959446143 / 6250000000000 : ℝ)) (b := (1346912291 / 800000000000 : ℝ)) (q := (2313056807753 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12240])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12240])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12240]

theorem cert12240_54 : CellCertificate 12240 (900005286227463 / 10000000000000000 : ℝ) (343213860222017 / 200000000000000000 : ℝ) (69392106526107 / 2000000000000000 : ℝ)
    (cell12240 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · have h := gap_lower (n := 12240) (a := (82221510834059 / 100000000000000 : ℝ)) (b := (1346912291 / 800000000000 : ℝ)) (q := (462612165679 / 20000000000000 : ℝ))
      (E := (cell12240 ⟨54, by decide⟩).energy) (xi := (69392106526107 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12240 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12240]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12240])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12240) (a := (82221510834059 / 100000000000000 : ℝ)) (b := (1346912291 / 800000000000 : ℝ)) (q := (462612165679 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12240])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12240])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12240]

theorem cert12240_55 : CellCertificate 12240 (900005286227463 / 10000000000000000 : ℝ) (343213860222017 / 200000000000000000 : ℝ) (69392106526107 / 2000000000000000 : ℝ)
    (cell12240 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · have h := gap_lower (n := 12240) (a := (8218769396151 / 10000000000000 : ℝ)) (b := (1346912291 / 800000000000 : ℝ)) (q := (2313064803759 / 100000000000000 : ℝ))
      (E := (cell12240 ⟨55, by decide⟩).energy) (xi := (69392106526107 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12240 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12240]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12240])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12240) (a := (8218769396151 / 10000000000000 : ℝ)) (b := (1346912291 / 800000000000 : ℝ)) (q := (2313064803759 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12240])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12240])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12240]

theorem cert12240_56 : CellCertificate 12240 (900005286227463 / 10000000000000000 : ℝ) (343213860222017 / 200000000000000000 : ℝ) (69392106526107 / 2000000000000000 : ℝ)
    (cell12240 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · have h := gap_lower (n := 12240) (a := (82153900492499 / 100000000000000 : ℝ)) (b := (1346912291 / 800000000000 : ℝ)) (q := (1156534395009 / 50000000000000 : ℝ))
      (E := (cell12240 ⟨56, by decide⟩).energy) (xi := (69392106526107 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12240 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12240]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12240])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12240) (a := (82153900492499 / 100000000000000 : ℝ)) (b := (1346912291 / 800000000000 : ℝ)) (q := (1156534395009 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12240])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12240])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12240]

theorem cert12240_57 : CellCertificate 12240 (900005286227463 / 10000000000000000 : ℝ) (343213860222017 / 200000000000000000 : ℝ) (69392106526107 / 2000000000000000 : ℝ)
    (cell12240 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · have h := gap_lower (n := 12240) (a := (82120130399023 / 100000000000000 : ℝ)) (b := (1346912291 / 800000000000 : ℝ)) (q := (9035440563 / 390625000000 : ℝ))
      (E := (cell12240 ⟨57, by decide⟩).energy) (xi := (69392106526107 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12240 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12240]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12240])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12240) (a := (82120130399023 / 100000000000000 : ℝ)) (b := (1346912291 / 800000000000 : ℝ)) (q := (9035440563 / 390625000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12240])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12240])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12240]

theorem cert12240_58 : CellCertificate 12240 (900005286227463 / 10000000000000000 : ℝ) (343213860222017 / 200000000000000000 : ℝ) (69392106526107 / 2000000000000000 : ℝ)
    (cell12240 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · have h := gap_lower (n := 12240) (a := (4104319182661 / 5000000000000 : ℝ)) (b := (1346912291 / 800000000000 : ℝ)) (q := (578269195709 / 25000000000000 : ℝ))
      (E := (cell12240 ⟨58, by decide⟩).energy) (xi := (69392106526107 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12240 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12240]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12240])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12240) (a := (4104319182661 / 5000000000000 : ℝ)) (b := (1346912291 / 800000000000 : ℝ)) (q := (578269195709 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12240])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12240])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12240]

theorem cert12240_59 : CellCertificate 12240 (900005286227463 / 10000000000000000 : ℝ) (343213860222017 / 200000000000000000 : ℝ) (69392106526107 / 2000000000000000 : ℝ)
    (cell12240 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · have h := gap_lower (n := 12240) (a := (82052660227369 / 100000000000000 : ℝ)) (b := (1346912291 / 800000000000 : ℝ)) (q := (57827019567 / 2500000000000 : ℝ))
      (E := (cell12240 ⟨59, by decide⟩).energy) (xi := (69392106526107 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12240 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12240]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12240])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12240) (a := (82052660227369 / 100000000000000 : ℝ)) (b := (1346912291 / 800000000000 : ℝ)) (q := (57827019567 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12240])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12240])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12240]

theorem cert12241_40 : CellCertificate 12241 (449987648479099 / 5000000000000000 : ℝ) (1715929063002011 / 1000000000000000000 : ℝ) (346931426776877 / 10000000000000000 : ℝ)
    (cell12241 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · have h := gap_lower (n := 12241) (a := (82697417342561 / 100000000000000 : ℝ)) (b := (168350097453 / 100000000000000 : ℝ)) (q := (462571358331 / 20000000000000 : ℝ))
      (E := (cell12241 ⟨40, by decide⟩).energy) (xi := (346931426776877 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12241 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12241]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12241])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12241) (a := (82697417342561 / 100000000000000 : ℝ)) (b := (168350097453 / 100000000000000 : ℝ)) (q := (462571358331 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12241])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12241])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12241]

theorem cert12241_41 : CellCertificate 12241 (449987648479099 / 5000000000000000 : ℝ) (1715929063002011 / 1000000000000000000 : ℝ) (346931426776877 / 10000000000000000 : ℝ)
    (cell12241 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · have h := gap_lower (n := 12241) (a := (16532654024037 / 20000000000000 : ℝ)) (b := (168350097453 / 100000000000000 : ℝ)) (q := (2312860789647 / 100000000000000 : ℝ))
      (E := (cell12241 ⟨41, by decide⟩).energy) (xi := (346931426776877 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12241 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12241]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12241])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12241) (a := (16532654024037 / 20000000000000 : ℝ)) (b := (168350097453 / 100000000000000 : ℝ)) (q := (2312860789647 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12241])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12241])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12241]

theorem cert12241_42 : CellCertificate 12241 (449987648479099 / 5000000000000000 : ℝ) (1715929063002011 / 1000000000000000000 : ℝ) (346931426776877 / 10000000000000000 : ℝ)
    (cell12241 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · have h := gap_lower (n := 12241) (a := (82629146708111 / 100000000000000 : ℝ)) (b := (168350097453 / 100000000000000 : ℝ)) (q := (2312864761051 / 100000000000000 : ℝ))
      (E := (cell12241 ⟨42, by decide⟩).energy) (xi := (346931426776877 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12241 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12241]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12241])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12241) (a := (82629146708111 / 100000000000000 : ℝ)) (b := (168350097453 / 100000000000000 : ℝ)) (q := (2312864761051 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12241])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12241])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12241]

theorem cert12241_43 : CellCertificate 12241 (449987648479099 / 5000000000000000 : ℝ) (1715929063002011 / 1000000000000000000 : ℝ) (346931426776877 / 10000000000000000 : ℝ)
    (cell12241 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · have h := gap_lower (n := 12241) (a := (82595047076287 / 100000000000000 : ℝ)) (b := (168350097453 / 100000000000000 : ℝ)) (q := (1156434382267 / 50000000000000 : ℝ))
      (E := (cell12241 ⟨43, by decide⟩).energy) (xi := (346931426776877 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12241 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12241]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12241])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12241) (a := (82595047076287 / 100000000000000 : ℝ)) (b := (168350097453 / 100000000000000 : ℝ)) (q := (1156434382267 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12241])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12241])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12241]

theorem cert12241_44 : CellCertificate 12241 (449987648479099 / 5000000000000000 : ℝ) (1715929063002011 / 1000000000000000000 : ℝ) (346931426776877 / 10000000000000000 : ℝ)
    (cell12241 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · have h := gap_lower (n := 12241) (a := (41280485597407 / 50000000000000 : ℝ)) (b := (168350097453 / 100000000000000 : ℝ)) (q := (289109092631 / 12500000000000 : ℝ))
      (E := (cell12241 ⟨44, by decide⟩).energy) (xi := (346931426776877 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12241 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12241]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12241])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12241) (a := (41280485597407 / 50000000000000 : ℝ)) (b := (168350097453 / 100000000000000 : ℝ)) (q := (289109092631 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12241])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12241])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12241]

theorem cert12241_45 : CellCertificate 12241 (449987648479099 / 5000000000000000 : ℝ) (1715929063002011 / 1000000000000000000 : ℝ) (346931426776877 / 10000000000000000 : ℝ)
    (cell12241 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · have h := gap_lower (n := 12241) (a := (10315864879243 / 12500000000000 : ℝ)) (b := (168350097453 / 100000000000000 : ℝ)) (q := (462575349773 / 20000000000000 : ℝ))
      (E := (cell12241 ⟨45, by decide⟩).energy) (xi := (346931426776877 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12241 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12241]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12241])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12241) (a := (10315864879243 / 12500000000000 : ℝ)) (b := (168350097453 / 100000000000000 : ℝ)) (q := (462575349773 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12241])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12241])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12241]

theorem cert12241_46 : CellCertificate 12241 (449987648479099 / 5000000000000000 : ℝ) (1715929063002011 / 1000000000000000000 : ℝ) (346931426776877 / 10000000000000000 : ℝ)
    (cell12241 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · have h := gap_lower (n := 12241) (a := (82492890564079 / 100000000000000 : ℝ)) (b := (168350097453 / 100000000000000 : ℝ)) (q := (2312880728453 / 100000000000000 : ℝ))
      (E := (cell12241 ⟨46, by decide⟩).energy) (xi := (346931426776877 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12241 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12241]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12241])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12241) (a := (82492890564079 / 100000000000000 : ℝ)) (b := (168350097453 / 100000000000000 : ℝ)) (q := (2312880728453 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12241])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12241])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12241]

theorem cert12241_47 : CellCertificate 12241 (449987648479099 / 5000000000000000 : ℝ) (1715929063002011 / 1000000000000000000 : ℝ) (346931426776877 / 10000000000000000 : ℝ)
    (cell12241 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · have h := gap_lower (n := 12241) (a := (20614721438943 / 25000000000000 : ℝ)) (b := (168350097453 / 100000000000000 : ℝ)) (q := (1156442368847 / 50000000000000 : ℝ))
      (E := (cell12241 ⟨47, by decide⟩).energy) (xi := (346931426776877 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12241 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12241]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12241])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12241) (a := (20614721438943 / 25000000000000 : ℝ)) (b := (168350097453 / 100000000000000 : ℝ)) (q := (1156442368847 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12241])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12241])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12241]

theorem cert12241_48 : CellCertificate 12241 (449987648479099 / 5000000000000000 : ℝ) (1715929063002011 / 1000000000000000000 : ℝ) (346931426776877 / 10000000000000000 : ℝ)
    (cell12241 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · have h := gap_lower (n := 12241) (a := (41212452289861 / 50000000000000 : ℝ)) (b := (168350097453 / 100000000000000 : ℝ)) (q := (2312888775463 / 100000000000000 : ℝ))
      (E := (cell12241 ⟨48, by decide⟩).energy) (xi := (346931426776877 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12241 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12241]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12241])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12241) (a := (41212452289861 / 50000000000000 : ℝ)) (b := (168350097453 / 100000000000000 : ℝ)) (q := (2312888775463 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12241])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12241])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12241]

theorem cert12241_49 : CellCertificate 12241 (449987648479099 / 5000000000000000 : ℝ) (1715929063002011 / 1000000000000000000 : ℝ) (346931426776877 / 10000000000000000 : ℝ)
    (cell12241 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · have h := gap_lower (n := 12241) (a := (82390947006777 / 100000000000000 : ℝ)) (b := (168350097453 / 100000000000000 : ℝ)) (q := (2312892722591 / 100000000000000 : ℝ))
      (E := (cell12241 ⟨49, by decide⟩).energy) (xi := (346931426776877 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12241 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12241]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12241])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12241) (a := (82390947006777 / 100000000000000 : ℝ)) (b := (168350097453 / 100000000000000 : ℝ)) (q := (2312892722591 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12241])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12241])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12241]

theorem cert12241_50 : CellCertificate 12241 (449987648479099 / 5000000000000000 : ℝ) (1715929063002011 / 1000000000000000000 : ℝ) (346931426776877 / 10000000000000000 : ℝ)
    (cell12241 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · have h := gap_lower (n := 12241) (a := (82357013007933 / 100000000000000 : ℝ)) (b := (168350097453 / 100000000000000 : ℝ)) (q := (289112094273 / 12500000000000 : ℝ))
      (E := (cell12241 ⟨50, by decide⟩).energy) (xi := (346931426776877 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12241 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12241]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12241])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12241) (a := (82357013007933 / 100000000000000 : ℝ)) (b := (168350097453 / 100000000000000 : ℝ)) (q := (289112094273 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12241])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12241])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12241]

theorem cert12241_51 : CellCertificate 12241 (449987648479099 / 5000000000000000 : ℝ) (1715929063002011 / 1000000000000000000 : ℝ) (346931426776877 / 10000000000000000 : ℝ)
    (cell12241 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · have h := gap_lower (n := 12241) (a := (82323102554329 / 100000000000000 : ℝ)) (b := (168350097453 / 100000000000000 : ℝ)) (q := (1156450375311 / 50000000000000 : ℝ))
      (E := (cell12241 ⟨51, by decide⟩).energy) (xi := (346931426776877 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12241 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12241]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12241])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12241) (a := (82323102554329 / 100000000000000 : ℝ)) (b := (168350097453 / 100000000000000 : ℝ)) (q := (1156450375311 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12241])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12241])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12241]

theorem cert12241_52 : CellCertificate 12241 (449987648479099 / 5000000000000000 : ℝ) (1715929063002011 / 1000000000000000000 : ℝ) (346931426776877 / 10000000000000000 : ℝ)
    (cell12241 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · have h := gap_lower (n := 12241) (a := (20572303904313 / 25000000000000 : ℝ)) (b := (168350097453 / 100000000000000 : ℝ)) (q := (2312904709847 / 100000000000000 : ℝ))
      (E := (cell12241 ⟨52, by decide⟩).energy) (xi := (346931426776877 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12241 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12241]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12241])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12241) (a := (20572303904313 / 25000000000000 : ℝ)) (b := (168350097453 / 100000000000000 : ℝ)) (q := (2312904709847 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12241])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12241])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12241]

theorem cert12241_53 : CellCertificate 12241 (449987648479099 / 5000000000000000 : ℝ) (1715929063002011 / 1000000000000000000 : ℝ) (346931426776877 / 10000000000000000 : ℝ)
    (cell12241 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · have h := gap_lower (n := 12241) (a := (20563838042033 / 25000000000000 : ℝ)) (b := (168350097453 / 100000000000000 : ℝ)) (q := (2312908747601 / 100000000000000 : ℝ))
      (E := (cell12241 ⟨53, by decide⟩).energy) (xi := (346931426776877 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12241 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12241]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12241])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12241) (a := (20563838042033 / 25000000000000 : ℝ)) (b := (168350097453 / 100000000000000 : ℝ)) (q := (2312908747601 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12241])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12241])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12241]

theorem cert12241_54 : CellCertificate 12241 (449987648479099 / 5000000000000000 : ℝ) (1715929063002011 / 1000000000000000000 : ℝ) (346931426776877 / 10000000000000000 : ℝ)
    (cell12241 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · have h := gap_lower (n := 12241) (a := (82221512178543 / 100000000000000 : ℝ)) (b := (168350097453 / 100000000000000 : ℝ)) (q := (57822818587 / 2500000000000 : ℝ))
      (E := (cell12241 ⟨54, by decide⟩).energy) (xi := (346931426776877 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12241 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12241]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12241])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12241) (a := (82221512178543 / 100000000000000 : ℝ)) (b := (168350097453 / 100000000000000 : ℝ)) (q := (57822818587 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12241])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12241])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12241]

theorem cert12241_55 : CellCertificate 12241 (449987648479099 / 5000000000000000 : ℝ) (1715929063002011 / 1000000000000000000 : ℝ) (346931426776877 / 10000000000000000 : ℝ)
    (cell12241 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · have h := gap_lower (n := 12241) (a := (82187695620199 / 100000000000000 : ℝ)) (b := (168350097453 / 100000000000000 : ℝ)) (q := (289114586849 / 12500000000000 : ℝ))
      (E := (cell12241 ⟨55, by decide⟩).energy) (xi := (346931426776877 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12241 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12241]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12241])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12241) (a := (82187695620199 / 100000000000000 : ℝ)) (b := (168350097453 / 100000000000000 : ℝ)) (q := (289114586849 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12241])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12241])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12241]

theorem cert12241_56 : CellCertificate 12241 (449987648479099 / 5000000000000000 : ℝ) (1715929063002011 / 1000000000000000000 : ℝ) (346931426776877 / 10000000000000000 : ℝ)
    (cell12241 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · have h := gap_lower (n := 12241) (a := (256730945203 / 312500000000 : ℝ)) (b := (168350097453 / 100000000000000 : ℝ)) (q := (462584143357 / 20000000000000 : ℝ))
      (E := (cell12241 ⟨56, by decide⟩).energy) (xi := (346931426776877 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12241 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12241]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12241])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12241) (a := (256730945203 / 312500000000 : ℝ)) (b := (168350097453 / 100000000000000 : ℝ)) (q := (462584143357 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12241])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12241])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12241]

theorem cert12241_57 : CellCertificate 12241 (449987648479099 / 5000000000000000 : ℝ) (1715929063002011 / 1000000000000000000 : ℝ) (346931426776877 / 10000000000000000 : ℝ)
    (cell12241 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · have h := gap_lower (n := 12241) (a := (3284805307393 / 4000000000000 : ℝ)) (b := (168350097453 / 100000000000000 : ℝ)) (q := (2312924688283 / 100000000000000 : ℝ))
      (E := (cell12241 ⟨57, by decide⟩).energy) (xi := (346931426776877 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12241 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12241]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12241])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12241) (a := (3284805307393 / 4000000000000 : ℝ)) (b := (168350097453 / 100000000000000 : ℝ)) (q := (2312924688283 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12241])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12241])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12241]

theorem cert12241_58 : CellCertificate 12241 (449987648479099 / 5000000000000000 : ℝ) (1715929063002011 / 1000000000000000000 : ℝ) (346931426776877 / 10000000000000000 : ℝ)
    (cell12241 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · have h := gap_lower (n := 12241) (a := (82086386251931 / 100000000000000 : ℝ)) (b := (168350097453 / 100000000000000 : ℝ)) (q := (578232181053 / 25000000000000 : ℝ))
      (E := (cell12241 ⟨58, by decide⟩).energy) (xi := (346931426776877 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12241 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12241]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12241])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12241) (a := (82086386251931 / 100000000000000 : ℝ)) (b := (168350097453 / 100000000000000 : ℝ)) (q := (578232181053 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12241])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12241])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12241]

theorem cert12241_59 : CellCertificate 12241 (449987648479099 / 5000000000000000 : ℝ) (1715929063002011 / 1000000000000000000 : ℝ) (346931426776877 / 10000000000000000 : ℝ)
    (cell12241 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · have h := gap_lower (n := 12241) (a := (41026331569279 / 50000000000000 : ℝ)) (b := (168350097453 / 100000000000000 : ℝ)) (q := (2312932702883 / 100000000000000 : ℝ))
      (E := (cell12241 ⟨59, by decide⟩).energy) (xi := (346931426776877 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12241 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12241]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12241])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12241) (a := (41026331569279 / 50000000000000 : ℝ)) (b := (168350097453 / 100000000000000 : ℝ)) (q := (2312932702883 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12241])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12241])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12241]

theorem cert12242_40 : CellCertificate 12242 (899945312410443 / 10000000000000000 : ℝ) (1715788847812729 / 1000000000000000000 : ℝ) (346902325933491 / 10000000000000000 : ℝ)
    (cell12242 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · have h := gap_lower (n := 12242) (a := (82697414243291 / 100000000000000 : ℝ)) (b := (16833616087 / 10000000000000 : ℝ)) (q := (2312708762461 / 100000000000000 : ℝ))
      (E := (cell12242 ⟨40, by decide⟩).energy) (xi := (346902325933491 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12242 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12242]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12242])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12242) (a := (82697414243291 / 100000000000000 : ℝ)) (b := (16833616087 / 10000000000000 : ℝ)) (q := (2312708762461 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12242])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12242])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12242]

theorem cert12242_41 : CellCertificate 12242 (899945312410443 / 10000000000000000 : ℝ) (1715788847812729 / 1000000000000000000 : ℝ) (346902325933491 / 10000000000000000 : ℝ)
    (cell12242 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · have h := gap_lower (n := 12242) (a := (82663267341221 / 100000000000000 : ℝ)) (b := (16833616087 / 10000000000000 : ℝ)) (q := (1156356392511 / 50000000000000 : ℝ))
      (E := (cell12242 ⟨41, by decide⟩).energy) (xi := (346902325933491 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12242 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12242]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12242])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12242) (a := (82663267341221 / 100000000000000 : ℝ)) (b := (16833616087 / 10000000000000 : ℝ)) (q := (1156356392511 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12242])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12242])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12242]

theorem cert12242_42 : CellCertificate 12242 (899945312410443 / 10000000000000000 : ℝ) (1715788847812729 / 1000000000000000000 : ℝ) (346902325933491 / 10000000000000000 : ℝ)
    (cell12242 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · have h := gap_lower (n := 12242) (a := (82629144249009 / 100000000000000 : ℝ)) (b := (16833616087 / 10000000000000 : ℝ)) (q := (2312716781761 / 100000000000000 : ℝ))
      (E := (cell12242 ⟨42, by decide⟩).energy) (xi := (346902325933491 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12242 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12242]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12242])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12242) (a := (82629144249009 / 100000000000000 : ℝ)) (b := (16833616087 / 10000000000000 : ℝ)) (q := (2312716781761 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12242])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12242])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12242]

theorem cert12242_43 : CellCertificate 12242 (899945312410443 / 10000000000000000 : ℝ) (1715788847812729 / 1000000000000000000 : ℝ) (346902325933491 / 10000000000000000 : ℝ)
    (cell12242 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · have h := gap_lower (n := 12242) (a := (16519008987321 / 20000000000000 : ℝ)) (b := (16833616087 / 10000000000000 : ℝ)) (q := (1156360376287 / 50000000000000 : ℝ))
      (E := (cell12242 ⟨43, by decide⟩).energy) (xi := (346902325933491 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12242 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12242]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12242])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12242) (a := (16519008987321 / 20000000000000 : ℝ)) (b := (16833616087 / 10000000000000 : ℝ)) (q := (1156360376287 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12242])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12242])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12242]

theorem cert12242_44 : CellCertificate 12242 (899945312410443 / 10000000000000000 : ℝ) (1715788847812729 / 1000000000000000000 : ℝ) (346902325933491 / 10000000000000000 : ℝ)
    (cell12242 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · have h := gap_lower (n := 12242) (a := (82560969374109 / 100000000000000 : ℝ)) (b := (16833616087 / 10000000000000 : ℝ)) (q := (231272475593 / 10000000000000 : ℝ))
      (E := (cell12242 ⟨44, by decide⟩).energy) (xi := (346902325933491 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12242 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12242]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12242])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12242) (a := (82560969374109 / 100000000000000 : ℝ)) (b := (16833616087 / 10000000000000 : ℝ)) (q := (231272475593 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12242])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12242])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12242]

theorem cert12242_45 : CellCertificate 12242 (899945312410443 / 10000000000000000 : ℝ) (1715788847812729 / 1000000000000000000 : ℝ) (346902325933491 / 10000000000000000 : ℝ)
    (cell12242 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · have h := gap_lower (n := 12242) (a := (3301076701271 / 4000000000000 : ℝ)) (b := (16833616087 / 10000000000000 : ℝ)) (q := (1156364395677 / 50000000000000 : ℝ))
      (E := (cell12242 ⟨45, by decide⟩).energy) (xi := (346902325933491 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12242 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12242]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12242])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12242) (a := (3301076701271 / 4000000000000 : ℝ)) (b := (16833616087 / 10000000000000 : ℝ)) (q := (1156364395677 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12242])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12242])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12242]

theorem cert12242_46 : CellCertificate 12242 (899945312410443 / 10000000000000000 : ℝ) (1715788847812729 / 1000000000000000000 : ℝ) (346902325933491 / 10000000000000000 : ℝ)
    (cell12242 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · have h := gap_lower (n := 12242) (a := (41246444690003 / 50000000000000 : ℝ)) (b := (16833616087 / 10000000000000 : ℝ)) (q := (231273274047 / 10000000000000 : ℝ))
      (E := (cell12242 ⟨46, by decide⟩).energy) (xi := (346902325933491 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12242 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12242]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12242])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12242) (a := (41246444690003 / 50000000000000 : ℝ)) (b := (16833616087 / 10000000000000 : ℝ)) (q := (231273274047 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12242])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12242])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12242]

theorem cert12242_47 : CellCertificate 12242 (899945312410443 / 10000000000000000 : ℝ) (1715788847812729 / 1000000000000000000 : ℝ) (346902325933491 / 10000000000000000 : ℝ)
    (cell12242 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · have h := gap_lower (n := 12242) (a := (16491776977871 / 20000000000000 : ℝ)) (b := (16833616087 / 10000000000000 : ℝ)) (q := (115636838941 / 5000000000000 : ℝ))
      (E := (cell12242 ⟨47, by decide⟩).energy) (xi := (346902325933491 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12242 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12242]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12242])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12242) (a := (16491776977871 / 20000000000000 : ℝ)) (b := (16833616087 / 10000000000000 : ℝ)) (q := (115636838941 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12242])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12242])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12242]

theorem cert12242_48 : CellCertificate 12242 (899945312410443 / 10000000000000000 : ℝ) (1715788847812729 / 1000000000000000000 : ℝ) (346902325933491 / 10000000000000000 : ℝ)
    (cell12242 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · have h := gap_lower (n := 12242) (a := (41212452015261 / 50000000000000 : ℝ)) (b := (16833616087 / 10000000000000 : ℝ)) (q := (1156370364341 / 50000000000000 : ℝ))
      (E := (cell12242 ⟨48, by decide⟩).energy) (xi := (346902325933491 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12242 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12242]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12242])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12242) (a := (41212452015261 / 50000000000000 : ℝ)) (b := (16833616087 / 10000000000000 : ℝ)) (q := (1156370364341 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12242])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12242])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12242]

theorem cert12242_49 : CellCertificate 12242 (899945312410443 / 10000000000000000 : ℝ) (1715788847812729 / 1000000000000000000 : ℝ) (346902325933491 / 10000000000000000 : ℝ)
    (cell12242 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · have h := gap_lower (n := 12242) (a := (20597736693589 / 25000000000000 : ℝ)) (b := (16833616087 / 10000000000000 : ℝ)) (q := (1156372382653 / 50000000000000 : ℝ))
      (E := (cell12242 ⟨49, by decide⟩).energy) (xi := (346902325933491 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12242 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12242]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12242])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12242) (a := (20597736693589 / 25000000000000 : ℝ)) (b := (16833616087 / 10000000000000 : ℝ)) (q := (1156372382653 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12242])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12242])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12242]

theorem cert12242_50 : CellCertificate 12242 (899945312410443 / 10000000000000000 : ℝ) (1715788847812729 / 1000000000000000000 : ℝ) (346902325933491 / 10000000000000000 : ℝ)
    (cell12242 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · have h := gap_lower (n := 12242) (a := (82357013091853 / 100000000000000 : ℝ)) (b := (16833616087 / 10000000000000 : ℝ)) (q := (2312748769333 / 100000000000000 : ℝ))
      (E := (cell12242 ⟨50, by decide⟩).energy) (xi := (346902325933491 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12242 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12242]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12242])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12242) (a := (82357013091853 / 100000000000000 : ℝ)) (b := (16833616087 / 10000000000000 : ℝ)) (q := (2312748769333 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12242])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12242])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12242]

theorem cert12242_51 : CellCertificate 12242 (899945312410443 / 10000000000000000 : ℝ) (1715788847812729 / 1000000000000000000 : ℝ) (346902325933491 / 10000000000000000 : ℝ)
    (cell12242 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · have h := gap_lower (n := 12242) (a := (41161551477077 / 50000000000000 : ℝ)) (b := (16833616087 / 10000000000000 : ℝ)) (q := (578188184729 / 25000000000000 : ℝ))
      (E := (cell12242 ⟨51, by decide⟩).energy) (xi := (346902325933491 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12242 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12242]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12242])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12242) (a := (41161551477077 / 50000000000000 : ℝ)) (b := (16833616087 / 10000000000000 : ℝ)) (q := (578188184729 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12242])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12242])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12242]

theorem cert12242_52 : CellCertificate 12242 (899945312410443 / 10000000000000000 : ℝ) (1715788847812729 / 1000000000000000000 : ℝ) (346902325933491 / 10000000000000000 : ℝ)
    (cell12242 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · have h := gap_lower (n := 12242) (a := (41144608166273 / 50000000000000 : ℝ)) (b := (16833616087 / 10000000000000 : ℝ)) (q := (2312756730981 / 100000000000000 : ℝ))
      (E := (cell12242 ⟨52, by decide⟩).energy) (xi := (346902325933491 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12242 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12242]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12242])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12242) (a := (41144608166273 / 50000000000000 : ℝ)) (b := (16833616087 / 10000000000000 : ℝ)) (q := (2312756730981 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12242])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12242])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12242]

theorem cert12242_53 : CellCertificate 12242 (899945312410443 / 10000000000000000 : ℝ) (1715788847812729 / 1000000000000000000 : ℝ) (346902325933491 / 10000000000000000 : ℝ)
    (cell12242 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · have h := gap_lower (n := 12242) (a := (4112767659923 / 5000000000000 : ℝ)) (b := (16833616087 / 10000000000000 : ℝ)) (q := (1156380371663 / 50000000000000 : ℝ))
      (E := (cell12242 ⟨53, by decide⟩).energy) (xi := (346902325933491 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12242 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12242]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12242])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12242) (a := (4112767659923 / 5000000000000 : ℝ)) (b := (16833616087 / 10000000000000 : ℝ)) (q := (1156380371663 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12242])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12242])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12242]

theorem cert12242_54 : CellCertificate 12242 (899945312410443 / 10000000000000000 : ℝ) (1715788847812729 / 1000000000000000000 : ℝ) (346902325933491 / 10000000000000000 : ℝ)
    (cell12242 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · have h := gap_lower (n := 12242) (a := (8222151352347 / 10000000000000 : ℝ)) (b := (16833616087 / 10000000000000 : ℝ)) (q := (578191178627 / 25000000000000 : ℝ))
      (E := (cell12242 ⟨54, by decide⟩).energy) (xi := (346902325933491 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12242 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12242]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12242])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12242) (a := (8222151352347 / 10000000000000 : ℝ)) (b := (16833616087 / 10000000000000 : ℝ)) (q := (578191178627 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12242])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12242])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12242]

theorem cert12242_55 : CellCertificate 12242 (899945312410443 / 10000000000000000 : ℝ) (1715788847812729 / 1000000000000000000 : ℝ) (346902325933491 / 10000000000000000 : ℝ)
    (cell12242 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · have h := gap_lower (n := 12242) (a := (20546924319823 / 25000000000000 : ℝ)) (b := (16833616087 / 10000000000000 : ℝ)) (q := (1156384350443 / 50000000000000 : ℝ))
      (E := (cell12242 ⟨55, by decide⟩).energy) (xi := (346902325933491 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12242 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12242]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12242])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12242) (a := (20546924319823 / 25000000000000 : ℝ)) (b := (16833616087 / 10000000000000 : ℝ)) (q := (1156384350443 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12242])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12242])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12242]

theorem cert12242_56 : CellCertificate 12242 (899945312410443 / 10000000000000000 : ℝ) (1715788847812729 / 1000000000000000000 : ℝ) (346902325933491 / 10000000000000000 : ℝ)
    (cell12242 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · have h := gap_lower (n := 12242) (a := (41076952218893 / 50000000000000 : ℝ)) (b := (16833616087 / 10000000000000 : ℝ)) (q := (2312772699623 / 100000000000000 : ℝ))
      (E := (cell12242 ⟨56, by decide⟩).energy) (xi := (346902325933491 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12242 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12242]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12242])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12242) (a := (41076952218893 / 50000000000000 : ℝ)) (b := (16833616087 / 10000000000000 : ℝ)) (q := (2312772699623 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12242])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12242])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12242]

theorem cert12242_57 : CellCertificate 12242 (899945312410443 / 10000000000000000 : ℝ) (1715788847812729 / 1000000000000000000 : ℝ) (346902325933491 / 10000000000000000 : ℝ)
    (cell12242 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · have h := gap_lower (n := 12242) (a := (82120134970951 / 100000000000000 : ℝ)) (b := (16833616087 / 10000000000000 : ℝ)) (q := (578194176919 / 25000000000000 : ℝ))
      (E := (cell12242 ⟨57, by decide⟩).energy) (xi := (346902325933491 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12242 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12242]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12242])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12242) (a := (82120134970951 / 100000000000000 : ℝ)) (b := (16833616087 / 10000000000000 : ℝ)) (q := (578194176919 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12242])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12242])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12242]

theorem cert12242_58 : CellCertificate 12242 (899945312410443 / 10000000000000000 : ℝ) (1715788847812729 / 1000000000000000000 : ℝ) (346902325933491 / 10000000000000000 : ℝ)
    (cell12242 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · have h := gap_lower (n := 12242) (a := (82086388850927 / 100000000000000 : ℝ)) (b := (16833616087 / 10000000000000 : ℝ)) (q := (578195180447 / 25000000000000 : ℝ))
      (E := (cell12242 ⟨58, by decide⟩).energy) (xi := (346902325933491 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12242 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12242]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12242])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12242) (a := (82086388850927 / 100000000000000 : ℝ)) (b := (16833616087 / 10000000000000 : ℝ)) (q := (578195180447 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12242])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12242])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12242]

theorem cert12242_59 : CellCertificate 12242 (899945312410443 / 10000000000000000 : ℝ) (1715788847812729 / 1000000000000000000 : ℝ) (346902325933491 / 10000000000000000 : ℝ)
    (cell12242 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · have h := gap_lower (n := 12242) (a := (82052666049993 / 100000000000000 : ℝ)) (b := (16833616087 / 10000000000000 : ℝ)) (q := (46255693587 / 2000000000000 : ℝ))
      (E := (cell12242 ⟨59, by decide⟩).energy) (xi := (346902325933491 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12242 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12242]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12242])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12242) (a := (82052666049993 / 100000000000000 : ℝ)) (b := (16833616087 / 10000000000000 : ℝ)) (q := (46255693587 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12242])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12242])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12242]

theorem cert12243_40 : CellCertificate 12243 (899915332583033 / 10000000000000000 : ℝ) (857824327768311 / 500000000000000000 : ℝ) (346873230098909 / 10000000000000000 : ℝ)
    (cell12243 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · have h := gap_lower (n := 12243) (a := (41348705572511 / 50000000000000 : ℝ)) (b := (1346577813 / 800000000000 : ℝ)) (q := (2312560905709 / 100000000000000 : ℝ))
      (E := (cell12243 ⟨40, by decide⟩).energy) (xi := (346873230098909 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12243 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12243]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12243])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12243) (a := (41348705572511 / 50000000000000 : ℝ)) (b := (1346577813 / 800000000000 : ℝ)) (q := (2312560905709 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12243])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12243])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12243]

theorem cert12243_41 : CellCertificate 12243 (899915332583033 / 10000000000000000 : ℝ) (857824327768311 / 500000000000000000 : ℝ) (346873230098909 / 10000000000000000 : ℝ)
    (cell12243 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · have h := gap_lower (n := 12243) (a := (41331632281609 / 50000000000000 : ℝ)) (b := (1346577813 / 800000000000 : ℝ)) (q := (2312564894227 / 100000000000000 : ℝ))
      (E := (cell12243 ⟨41, by decide⟩).energy) (xi := (346873230098909 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12243 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12243]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12243])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12243) (a := (41331632281609 / 50000000000000 : ℝ)) (b := (1346577813 / 800000000000 : ℝ)) (q := (2312564894227 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12243])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12243])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12243]

theorem cert12243_42 : CellCertificate 12243 (899915332583033 / 10000000000000000 : ℝ) (857824327768311 / 500000000000000000 : ℝ) (346873230098909 / 10000000000000000 : ℝ)
    (cell12243 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · have h := gap_lower (n := 12243) (a := (82629141790829 / 100000000000000 : ℝ)) (b := (1346577813 / 800000000000 : ℝ)) (q := (1156284428821 / 50000000000000 : ℝ))
      (E := (cell12243 ⟨42, by decide⟩).energy) (xi := (346873230098909 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12243 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12243]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12243])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12243) (a := (82629141790829 / 100000000000000 : ℝ)) (b := (1346577813 / 800000000000 : ℝ)) (q := (1156284428821 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12243])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12243])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12243]

theorem cert12243_43 : CellCertificate 12243 (899915332583033 / 10000000000000000 : ℝ) (857824327768311 / 500000000000000000 : ℝ) (346873230098909 / 10000000000000000 : ℝ)
    (cell12243 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · have h := gap_lower (n := 12243) (a := (20648760699451 / 25000000000000 : ℝ)) (b := (1346577813 / 800000000000 : ℝ)) (q := (2312572854621 / 100000000000000 : ℝ))
      (E := (cell12243 ⟨43, by decide⟩).energy) (xi := (346873230098909 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12243 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12243]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12243])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12243) (a := (20648760699451 / 25000000000000 : ℝ)) (b := (1346577813 / 800000000000 : ℝ)) (q := (2312572854621 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12243])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12243])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12243]

theorem cert12243_44 : CellCertificate 12243 (899915332583033 / 10000000000000000 : ℝ) (857824327768311 / 500000000000000000 : ℝ) (346873230098909 / 10000000000000000 : ℝ)
    (cell12243 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · have h := gap_lower (n := 12243) (a := (16512193510849 / 20000000000000 : ℝ)) (b := (1346577813 / 800000000000 : ℝ)) (q := (578144221227 / 25000000000000 : ℝ))
      (E := (cell12243 ⟨44, by decide⟩).energy) (xi := (346873230098909 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12243 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12243]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12243])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12243) (a := (16512193510849 / 20000000000000 : ℝ)) (b := (1346577813 / 800000000000 : ℝ)) (q := (578144221227 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12243])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12243])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12243]

theorem cert12243_45 : CellCertificate 12243 (899915332583033 / 10000000000000000 : ℝ) (857824327768311 / 500000000000000000 : ℝ) (346873230098909 / 10000000000000000 : ℝ)
    (cell12243 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · have h := gap_lower (n := 12243) (a := (10315864503801 / 12500000000000 : ℝ)) (b := (1346577813 / 800000000000 : ℝ)) (q := (2312580830389 / 100000000000000 : ℝ))
      (E := (cell12243 ⟨45, by decide⟩).energy) (xi := (346873230098909 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12243 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12243]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12243])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12243) (a := (10315864503801 / 12500000000000 : ℝ)) (b := (1346577813 / 800000000000 : ℝ)) (q := (2312580830389 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12243])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12243])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12243]

theorem cert12243_46 : CellCertificate 12243 (899915332583033 / 10000000000000000 : ℝ) (857824327768311 / 500000000000000000 : ℝ) (346873230098909 / 10000000000000000 : ℝ)
    (cell12243 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · have h := gap_lower (n := 12243) (a := (41246444098347 / 50000000000000 : ℝ)) (b := (1346577813 / 800000000000 : ℝ)) (q := (1156292433379 / 50000000000000 : ℝ))
      (E := (cell12243 ⟨46, by decide⟩).energy) (xi := (346873230098909 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12243 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12243]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12243])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12243) (a := (41246444098347 / 50000000000000 : ℝ)) (b := (1346577813 / 800000000000 : ℝ)) (q := (1156292433379 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12243])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12243])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12243]

theorem cert12243_47 : CellCertificate 12243 (899915332583033 / 10000000000000000 : ℝ) (857824327768311 / 500000000000000000 : ℝ) (346873230098909 / 10000000000000000 : ℝ)
    (cell12243 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · have h := gap_lower (n := 12243) (a := (82458884023659 / 100000000000000 : ℝ)) (b := (1346577813 / 800000000000 : ℝ)) (q := (1156294408287 / 50000000000000 : ℝ))
      (E := (cell12243 ⟨47, by decide⟩).energy) (xi := (346873230098909 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12243 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12243]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12243])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12243) (a := (82458884023659 / 100000000000000 : ℝ)) (b := (1346577813 / 800000000000 : ℝ)) (q := (1156294408287 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12243])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12243])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12243]

theorem cert12243_48 : CellCertificate 12243 (899915332583033 / 10000000000000000 : ℝ) (857824327768311 / 500000000000000000 : ℝ) (346873230098909 / 10000000000000000 : ℝ)
    (cell12243 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · have h := gap_lower (n := 12243) (a := (82424903482003 / 100000000000000 : ℝ)) (b := (1346577813 / 800000000000 : ℝ)) (q := (2312592855237 / 100000000000000 : ℝ))
      (E := (cell12243 ⟨48, by decide⟩).energy) (xi := (346873230098909 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12243 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12243]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12243])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12243) (a := (82424903482003 / 100000000000000 : ℝ)) (b := (1346577813 / 800000000000 : ℝ)) (q := (2312592855237 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12243])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12243])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12243]

theorem cert12243_49 : CellCertificate 12243 (899915332583033 / 10000000000000000 : ℝ) (857824327768311 / 500000000000000000 : ℝ) (346873230098909 / 10000000000000000 : ℝ)
    (cell12243 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · have h := gap_lower (n := 12243) (a := (5149434158911 / 6250000000000 : ℝ)) (b := (1346577813 / 800000000000 : ℝ)) (q := (462519372729 / 20000000000000 : ℝ))
      (E := (cell12243 ⟨49, by decide⟩).energy) (xi := (346873230098909 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12243 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12243]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12243])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12243) (a := (5149434158911 / 6250000000000 : ℝ)) (b := (1346577813 / 800000000000 : ℝ)) (q := (462519372729 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12243])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12243])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12243]

theorem cert12243_50 : CellCertificate 12243 (899915332583033 / 10000000000000000 : ℝ) (857824327768311 / 500000000000000000 : ℝ) (346873230098909 / 10000000000000000 : ℝ)
    (cell12243 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · have h := gap_lower (n := 12243) (a := (41178506588187 / 50000000000000 : ℝ)) (b := (1346577813 / 800000000000 : ℝ)) (q := (2312600840169 / 100000000000000 : ℝ))
      (E := (cell12243 ⟨50, by decide⟩).energy) (xi := (346873230098909 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12243 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12243]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12243])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12243) (a := (41178506588187 / 50000000000000 : ℝ)) (b := (1346577813 / 800000000000 : ℝ)) (q := (2312600840169 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12243])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12243])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12243]

theorem cert12243_51 : CellCertificate 12243 (899915332583033 / 10000000000000000 : ℝ) (857824327768311 / 500000000000000000 : ℝ) (346873230098909 / 10000000000000000 : ℝ)
    (cell12243 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · have h := gap_lower (n := 12243) (a := (82323103354541 / 100000000000000 : ℝ)) (b := (1346577813 / 800000000000 : ℝ)) (q := (2312604841921 / 100000000000000 : ℝ))
      (E := (cell12243 ⟨51, by decide⟩).energy) (xi := (346873230098909 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12243 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12243]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12243])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12243) (a := (82323103354541 / 100000000000000 : ℝ)) (b := (1346577813 / 800000000000 : ℝ)) (q := (2312604841921 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12243])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12243])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12243]

theorem cert12243_52 : CellCertificate 12243 (899915332583033 / 10000000000000000 : ℝ) (857824327768311 / 500000000000000000 : ℝ) (346873230098909 / 10000000000000000 : ℝ)
    (cell12243 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · have h := gap_lower (n := 12243) (a := (41144608524181 / 50000000000000 : ℝ)) (b := (1346577813 / 800000000000 : ℝ)) (q := (2312608807931 / 100000000000000 : ℝ))
      (E := (cell12243 ⟨52, by decide⟩).energy) (xi := (346873230098909 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12243 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12243]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12243])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12243) (a := (41144608524181 / 50000000000000 : ℝ)) (b := (1346577813 / 800000000000 : ℝ)) (q := (2312608807931 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12243])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12243])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12243]

theorem cert12243_53 : CellCertificate 12243 (899915332583033 / 10000000000000000 : ℝ) (857824327768311 / 500000000000000000 : ℝ) (346873230098909 / 10000000000000000 : ℝ)
    (cell12243 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · have h := gap_lower (n := 12243) (a := (8225535422927 / 10000000000000 : ℝ)) (b := (1346577813 / 800000000000 : ℝ)) (q := (2312612794933 / 100000000000000 : ℝ))
      (E := (cell12243 ⟨53, by decide⟩).energy) (xi := (346873230098909 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12243 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12243]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12243])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12243) (a := (8225535422927 / 10000000000000 : ℝ)) (b := (1346577813 / 800000000000 : ℝ)) (q := (2312612794933 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12243])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12243])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12243]

theorem cert12243_54 : CellCertificate 12243 (899915332583033 / 10000000000000000 : ℝ) (857824327768311 / 500000000000000000 : ℝ) (346873230098909 / 10000000000000000 : ℝ)
    (cell12243 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · have h := gap_lower (n := 12243) (a := (2055537871721 / 2500000000000 : ℝ)) (b := (1346577813 / 800000000000 : ℝ)) (q := (2312616800511 / 100000000000000 : ℝ))
      (E := (cell12243 ⟨54, by decide⟩).energy) (xi := (346873230098909 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12243 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12243]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12243])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12243) (a := (2055537871721 / 2500000000000 : ℝ)) (b := (1346577813 / 800000000000 : ℝ)) (q := (2312616800511 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12243])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12243])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12243]

theorem cert12243_55 : CellCertificate 12243 (899915332583033 / 10000000000000000 : ℝ) (857824327768311 / 500000000000000000 : ℝ) (346873230098909 / 10000000000000000 : ℝ)
    (cell12243 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · have h := gap_lower (n := 12243) (a := (82187698938789 / 100000000000000 : ℝ)) (b := (1346577813 / 800000000000 : ℝ)) (q := (1156310411021 / 50000000000000 : ℝ))
      (E := (cell12243 ⟨55, by decide⟩).energy) (xi := (346873230098909 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12243 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12243]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12243])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12243) (a := (82187698938789 / 100000000000000 : ℝ)) (b := (1346577813 / 800000000000 : ℝ)) (q := (1156310411021 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12243])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12243])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12243]

theorem cert12243_56 : CellCertificate 12243 (899915332583033 / 10000000000000000 : ℝ) (857824327768311 / 500000000000000000 : ℝ) (346873230098909 / 10000000000000000 : ℝ)
    (cell12243 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · have h := gap_lower (n := 12243) (a := (2567309575343 / 3125000000000 : ℝ)) (b := (1346577813 / 800000000000 : ℝ)) (q := (578156199403 / 25000000000000 : ℝ))
      (E := (cell12243 ⟨56, by decide⟩).energy) (xi := (346873230098909 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12243 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12243]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12243])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12243) (a := (2567309575343 / 3125000000000 : ℝ)) (b := (1346577813 / 800000000000 : ℝ)) (q := (578156199403 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12243])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12243])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12243]

theorem cert12243_57 : CellCertificate 12243 (899915332583033 / 10000000000000000 : ℝ) (857824327768311 / 500000000000000000 : ℝ) (346873230098909 / 10000000000000000 : ℝ)
    (cell12243 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · have h := gap_lower (n := 12243) (a := (82120137257403 / 100000000000000 : ℝ)) (b := (1346577813 / 800000000000 : ℝ)) (q := (578157195801 / 25000000000000 : ℝ))
      (E := (cell12243 ⟨57, by decide⟩).energy) (xi := (346873230098909 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12243 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12243]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12243])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12243) (a := (82120137257403 / 100000000000000 : ℝ)) (b := (1346577813 / 800000000000 : ℝ)) (q := (578157195801 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12243])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12243])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12243]

theorem cert12243_58 : CellCertificate 12243 (899915332583033 / 10000000000000000 : ℝ) (857824327768311 / 500000000000000000 : ℝ) (346873230098909 / 10000000000000000 : ℝ)
    (cell12243 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · have h := gap_lower (n := 12243) (a := (82086391450209 / 100000000000000 : ℝ)) (b := (1346577813 / 800000000000 : ℝ)) (q := (578158193891 / 25000000000000 : ℝ))
      (E := (cell12243 ⟨58, by decide⟩).energy) (xi := (346873230098909 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12243 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12243]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12243])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12243) (a := (82086391450209 / 100000000000000 : ℝ)) (b := (1346577813 / 800000000000 : ℝ)) (q := (578158193891 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12243])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12243])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12243]

theorem cert12243_59 : CellCertificate 12243 (899915332583033 / 10000000000000000 : ℝ) (857824327768311 / 500000000000000000 : ℝ) (346873230098909 / 10000000000000000 : ℝ)
    (cell12243 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · have h := gap_lower (n := 12243) (a := (41026334480837 / 50000000000000 : ℝ)) (b := (1346577813 / 800000000000 : ℝ)) (q := (2312636771229 / 100000000000000 : ℝ))
      (E := (cell12243 ⟨59, by decide⟩).energy) (xi := (346873230098909 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12243 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12243]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12243])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12243) (a := (41026334480837 / 50000000000000 : ℝ)) (b := (1346577813 / 800000000000 : ℝ)) (q := (2312636771229 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12243])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12243])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12243]

theorem cert12244_40 : CellCertificate 12244 (449942678737399 / 5000000000000000 : ℝ) (1715508486168073 / 1000000000000000000 : ℝ) (17342206963583 / 500000000000000 : ℝ)
    (cell12244 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · have h := gap_lower (n := 12244) (a := (16539481609551 / 20000000000000 : ℝ)) (b := (168308294717 / 100000000000000 : ℝ)) (q := (2312413045299 / 100000000000000 : ℝ))
      (E := (cell12244 ⟨40, by decide⟩).energy) (xi := (17342206963583 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12244 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12244]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12244])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12244) (a := (16539481609551 / 20000000000000 : ℝ)) (b := (168308294717 / 100000000000000 : ℝ)) (q := (2312413045299 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12244])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12244])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12244]

theorem cert12244_41 : CellCertificate 12244 (449942678737399 / 5000000000000000 : ℝ) (1715508486168073 / 1000000000000000000 : ℝ) (17342206963583 / 500000000000000 : ℝ)
    (cell12244 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · have h := gap_lower (n := 12244) (a := (82663261786177 / 100000000000000 : ℝ)) (b := (168308294717 / 100000000000000 : ℝ)) (q := (2312417058539 / 100000000000000 : ℝ))
      (E := (cell12244 ⟨41, by decide⟩).energy) (xi := (17342206963583 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12244 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12244]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12244])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12244) (a := (82663261786177 / 100000000000000 : ℝ)) (b := (168308294717 / 100000000000000 : ℝ)) (q := (2312417058539 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12244])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12244])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12244]

theorem cert12244_42 : CellCertificate 12244 (449942678737399 / 5000000000000000 : ℝ) (1715508486168073 / 1000000000000000000 : ℝ) (17342206963583 / 500000000000000 : ℝ)
    (cell12244 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · have h := gap_lower (n := 12244) (a := (82629139333569 / 100000000000000 : ℝ)) (b := (168308294717 / 100000000000000 : ℝ)) (q := (2312421047443 / 100000000000000 : ℝ))
      (E := (cell12244 ⟨42, by decide⟩).energy) (xi := (17342206963583 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12244 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12244]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12244])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12244) (a := (82629139333569 / 100000000000000 : ℝ)) (b := (168308294717 / 100000000000000 : ℝ)) (q := (2312421047443 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12244])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12244])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12244]

theorem cert12244_43 : CellCertificate 12244 (449942678737399 / 5000000000000000 : ℝ) (1715508486168073 / 1000000000000000000 : ℝ) (17342206963583 / 500000000000000 : ℝ)
    (cell12244 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · have h := gap_lower (n := 12244) (a := (82595040659883 / 100000000000000 : ℝ)) (b := (168308294717 / 100000000000000 : ℝ)) (q := (2312425070677 / 100000000000000 : ℝ))
      (E := (cell12244 ⟨43, by decide⟩).energy) (xi := (17342206963583 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12244 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12244]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12244])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12244) (a := (82595040659883 / 100000000000000 : ℝ)) (b := (168308294717 / 100000000000000 : ℝ)) (q := (2312425070677 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12244])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12244])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12244]

theorem cert12244_44 : CellCertificate 12244 (449942678737399 / 5000000000000000 : ℝ) (1715508486168073 / 1000000000000000000 : ℝ) (17342206963583 / 500000000000000 : ℝ)
    (cell12244 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · have h := gap_lower (n := 12244) (a := (41280482867611 / 50000000000000 : ℝ)) (b := (168308294717 / 100000000000000 : ℝ)) (q := (289053626299 / 12500000000000 : ℝ))
      (E := (cell12244 ⟨44, by decide⟩).energy) (xi := (17342206963583 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12244 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12244]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12244])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12244) (a := (41280482867611 / 50000000000000 : ℝ)) (b := (168308294717 / 100000000000000 : ℝ)) (q := (289053626299 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12244])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12244])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12244]

theorem cert12244_45 : CellCertificate 12244 (449942678737399 / 5000000000000000 : ℝ) (1715508486168073 / 1000000000000000000 : ℝ) (17342206963583 / 500000000000000 : ℝ)
    (cell12244 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · have h := gap_lower (n := 12244) (a := (82526914529841 / 100000000000000 : ℝ)) (b := (168308294717 / 100000000000000 : ℝ)) (q := (578108260607 / 25000000000000 : ℝ))
      (E := (cell12244 ⟨45, by decide⟩).energy) (xi := (17342206963583 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12244 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12244]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12244])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12244) (a := (82526914529841 / 100000000000000 : ℝ)) (b := (168308294717 / 100000000000000 : ℝ)) (q := (578108260607 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12244])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12244])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12244]

theorem cert12244_46 : CellCertificate 12244 (449942678737399 / 5000000000000000 : ℝ) (1715508486168073 / 1000000000000000000 : ℝ) (17342206963583 / 500000000000000 : ℝ)
    (cell12244 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · have h := gap_lower (n := 12244) (a := (82492887014143 / 100000000000000 : ℝ)) (b := (168308294717 / 100000000000000 : ℝ)) (q := (2312437048477 / 100000000000000 : ℝ))
      (E := (cell12244 ⟨46, by decide⟩).energy) (xi := (17342206963583 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12244 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12244]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12244])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12244) (a := (82492887014143 / 100000000000000 : ℝ)) (b := (168308294717 / 100000000000000 : ℝ)) (q := (2312437048477 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12244])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12244])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12244]

theorem cert12244_47 : CellCertificate 12244 (449942678737399 / 5000000000000000 : ℝ) (1715508486168073 / 1000000000000000000 : ℝ) (17342206963583 / 500000000000000 : ℝ)
    (cell12244 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · have h := gap_lower (n := 12244) (a := (82458883158683 / 100000000000000 : ℝ)) (b := (168308294717 / 100000000000000 : ℝ)) (q := (578110256889 / 25000000000000 : ℝ))
      (E := (cell12244 ⟨47, by decide⟩).energy) (xi := (17342206963583 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12244 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12244]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12244])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12244) (a := (82458883158683 / 100000000000000 : ℝ)) (b := (168308294717 / 100000000000000 : ℝ)) (q := (578110256889 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12244])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12244])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12244]

theorem cert12244_48 : CellCertificate 12244 (449942678737399 / 5000000000000000 : ℝ) (1715508486168073 / 1000000000000000000 : ℝ) (17342206963583 / 500000000000000 : ℝ)
    (cell12244 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · have h := gap_lower (n := 12244) (a := (20606225733541 / 25000000000000 : ℝ)) (b := (168308294717 / 100000000000000 : ℝ)) (q := (2312445037353 / 100000000000000 : ℝ))
      (E := (cell12244 ⟨48, by decide⟩).energy) (xi := (17342206963583 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12244 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12244]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12244])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12244) (a := (20606225733541 / 25000000000000 : ℝ)) (b := (168308294717 / 100000000000000 : ℝ)) (q := (2312445037353 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12244])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12244])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12244]

theorem cert12244_49 : CellCertificate 12244 (449942678737399 / 5000000000000000 : ℝ) (1715508486168073 / 1000000000000000000 : ℝ) (17342206963583 / 500000000000000 : ℝ)
    (cell12244 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · have h := gap_lower (n := 12244) (a := (82390946311437 / 100000000000000 : ℝ)) (b := (168308294717 / 100000000000000 : ℝ)) (q := (2312449017609 / 100000000000000 : ℝ))
      (E := (cell12244 ⟨49, by decide⟩).energy) (xi := (17342206963583 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12244 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12244]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12244])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12244) (a := (82390946311437 / 100000000000000 : ℝ)) (b := (168308294717 / 100000000000000 : ℝ)) (q := (2312449017609 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12244])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12244])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12244]

theorem cert12244_50 : CellCertificate 12244 (449942678737399 / 5000000000000000 : ℝ) (1715508486168073 / 1000000000000000000 : ℝ) (17342206963583 / 500000000000000 : ℝ)
    (cell12244 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · have h := gap_lower (n := 12244) (a := (82357013261497 / 100000000000000 : ℝ)) (b := (168308294717 / 100000000000000 : ℝ)) (q := (2312453025631 / 100000000000000 : ℝ))
      (E := (cell12244 ⟨50, by decide⟩).energy) (xi := (17342206963583 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12244 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12244]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12244])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12244) (a := (82357013261497 / 100000000000000 : ℝ)) (b := (168308294717 / 100000000000000 : ℝ)) (q := (2312453025631 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12244])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12244])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12244]

theorem cert12244_51 : CellCertificate 12244 (449942678737399 / 5000000000000000 : ℝ) (1715508486168073 / 1000000000000000000 : ℝ) (17342206963583 / 500000000000000 : ℝ)
    (cell12244 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · have h := gap_lower (n := 12244) (a := (82323103755489 / 100000000000000 : ℝ)) (b := (168308294717 / 100000000000000 : ℝ)) (q := (2312457000681 / 100000000000000 : ℝ))
      (E := (cell12244 ⟨51, by decide⟩).energy) (xi := (17342206963583 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12244 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12244]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12244])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12244) (a := (82323103755489 / 100000000000000 : ℝ)) (b := (168308294717 / 100000000000000 : ℝ)) (q := (2312457000681 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12244])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12244])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12244]

theorem cert12244_52 : CellCertificate 12244 (449942678737399 / 5000000000000000 : ℝ) (1715508486168073 / 1000000000000000000 : ℝ) (17342206963583 / 500000000000000 : ℝ)
    (cell12244 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · have h := gap_lower (n := 12244) (a := (822892177647 / 1000000000000 : ℝ)) (b := (168308294717 / 100000000000000 : ℝ)) (q := (2312460999683 / 100000000000000 : ℝ))
      (E := (cell12244 ⟨52, by decide⟩).energy) (xi := (17342206963583 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12244 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12244]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12244])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12244) (a := (822892177647 / 1000000000000 : ℝ)) (b := (168308294717 / 100000000000000 : ℝ)) (q := (2312460999683 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12244])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12244])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12244]

theorem cert12244_53 : CellCertificate 12244 (449942678737399 / 5000000000000000 : ℝ) (1715508486168073 / 1000000000000000000 : ℝ) (17342206963583 / 500000000000000 : ℝ)
    (cell12244 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · have h := gap_lower (n := 12244) (a := (82255355260563 / 100000000000000 : ℝ)) (b := (168308294717 / 100000000000000 : ℝ)) (q := (1156232510217 / 50000000000000 : ℝ))
      (E := (cell12244 ⟨53, by decide⟩).energy) (xi := (17342206963583 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12244 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12244]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12244])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12244) (a := (82255355260563 / 100000000000000 : ℝ)) (b := (168308294717 / 100000000000000 : ℝ)) (q := (1156232510217 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12244])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12244])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12244]

theorem cert12244_54 : CellCertificate 12244 (449942678737399 / 5000000000000000 : ℝ) (1715508486168073 / 1000000000000000000 : ℝ) (17342206963583 / 500000000000000 : ℝ)
    (cell12244 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · have h := gap_lower (n := 12244) (a := (82221516214653 / 100000000000000 : ℝ)) (b := (168308294717 / 100000000000000 : ℝ)) (q := (231246900149 / 10000000000000 : ℝ))
      (E := (cell12244 ⟨54, by decide⟩).energy) (xi := (17342206963583 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12244 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12244]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12244])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12244) (a := (82221516214653 / 100000000000000 : ℝ)) (b := (168308294717 / 100000000000000 : ℝ)) (q := (231246900149 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12244])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12244])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12244]

theorem cert12244_55 : CellCertificate 12244 (449942678737399 / 5000000000000000 : ℝ) (1715508486168073 / 1000000000000000000 : ℝ) (17342206963583 / 500000000000000 : ℝ)
    (cell12244 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · have h := gap_lower (n := 12244) (a := (82187700598689 / 100000000000000 : ℝ)) (b := (168308294717 / 100000000000000 : ℝ)) (q := (289059124901 / 12500000000000 : ℝ))
      (E := (cell12244 ⟨55, by decide⟩).energy) (xi := (17342206963583 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12244 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12244]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12244])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12244) (a := (82187700598689 / 100000000000000 : ℝ)) (b := (168308294717 / 100000000000000 : ℝ)) (q := (289059124901 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12244])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12244])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12244]

theorem cert12244_56 : CellCertificate 12244 (449942678737399 / 5000000000000000 : ℝ) (1715508486168073 / 1000000000000000000 : ℝ) (17342206963583 / 500000000000000 : ℝ)
    (cell12244 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · have h := gap_lower (n := 12244) (a := (8215390838453 / 10000000000000 : ℝ)) (b := (168308294717 / 100000000000000 : ℝ)) (q := (36132453293 / 1562500000000 : ℝ))
      (E := (cell12244 ⟨56, by decide⟩).energy) (xi := (17342206963583 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12244 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12244]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12244])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12244) (a := (8215390838453 / 10000000000000 : ℝ)) (b := (168308294717 / 100000000000000 : ℝ)) (q := (36132453293 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12244])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12244])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12244]

theorem cert12244_57 : CellCertificate 12244 (449942678737399 / 5000000000000000 : ℝ) (1715508486168073 / 1000000000000000000 : ℝ) (17342206963583 / 500000000000000 : ℝ)
    (cell12244 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · have h := gap_lower (n := 12244) (a := (82120139544179 / 100000000000000 : ℝ)) (b := (168308294717 / 100000000000000 : ℝ)) (q := (578120243493 / 25000000000000 : ℝ))
      (E := (cell12244 ⟨57, by decide⟩).energy) (xi := (17342206963583 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12244 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12244]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12244])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12244) (a := (82120139544179 / 100000000000000 : ℝ)) (b := (168308294717 / 100000000000000 : ℝ)) (q := (578120243493 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12244])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12244])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12244]

theorem cert12244_58 : CellCertificate 12244 (449942678737399 / 5000000000000000 : ℝ) (1715508486168073 / 1000000000000000000 : ℝ) (17342206963583 / 500000000000000 : ℝ)
    (cell12244 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · have h := gap_lower (n := 12244) (a := (5130399628111 / 6250000000000 : ℝ)) (b := (168308294717 / 100000000000000 : ℝ)) (q := (144530312737 / 6250000000000 : ℝ))
      (E := (cell12244 ⟨58, by decide⟩).energy) (xi := (17342206963583 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12244 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12244]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12244])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12244) (a := (5130399628111 / 6250000000000 : ℝ)) (b := (168308294717 / 100000000000000 : ℝ)) (q := (144530312737 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12244])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12244])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12244]

theorem cert12244_59 : CellCertificate 12244 (449942678737399 / 5000000000000000 : ℝ) (1715508486168073 / 1000000000000000000 : ℝ) (17342206963583 / 500000000000000 : ℝ)
    (cell12244 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · have h := gap_lower (n := 12244) (a := (82052671873601 / 100000000000000 : ℝ)) (b := (168308294717 / 100000000000000 : ℝ)) (q := (2312488978523 / 100000000000000 : ℝ))
      (E := (cell12244 ⟨59, by decide⟩).energy) (xi := (17342206963583 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12244 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12244]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12244])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12244) (a := (82052671873601 / 100000000000000 : ℝ)) (b := (168308294717 / 100000000000000 : ℝ)) (q := (2312488978523 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12244])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12244])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12244]

theorem cert12245_40 : CellCertificate 12245 (899855387084573 / 10000000000000000 : ℝ) (1715368339701469 / 1000000000000000000 : ℝ) (13872602138011 / 400000000000000 : ℝ)
    (cell12245 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · have h := gap_lower (n := 12245) (a := (1292146952367 / 1562500000000 : ℝ)) (b := (168294365147 / 100000000000000 : ℝ)) (q := (2312265298633 / 100000000000000 : ℝ))
      (E := (cell12245 ⟨40, by decide⟩).energy) (xi := (13872602138011 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12245 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12245]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12245])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12245) (a := (1292146952367 / 1562500000000 : ℝ)) (b := (168294365147 / 100000000000000 : ℝ)) (q := (2312265298633 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12245])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12245])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12245]

theorem cert12245_41 : CellCertificate 12245 (899855387084573 / 10000000000000000 : ℝ) (1715368339701469 / 1000000000000000000 : ℝ) (13872602138011 / 400000000000000 : ℝ)
    (cell12245 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · have h := gap_lower (n := 12245) (a := (5166453688131 / 6250000000000 : ℝ)) (b := (168294365147 / 100000000000000 : ℝ)) (q := (2312269336683 / 100000000000000 : ℝ))
      (E := (cell12245 ⟨41, by decide⟩).energy) (xi := (13872602138011 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12245 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12245]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12245])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12245) (a := (5166453688131 / 6250000000000 : ℝ)) (b := (168294365147 / 100000000000000 : ℝ)) (q := (2312269336683 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12245])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12245])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12245]

theorem cert12245_42 : CellCertificate 12245 (899855387084573 / 10000000000000000 : ℝ) (1715368339701469 / 1000000000000000000 : ℝ) (13872602138011 / 400000000000000 : ℝ)
    (cell12245 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · have h := gap_lower (n := 12245) (a := (8262913687723 / 10000000000000 : ℝ)) (b := (168294365147 / 100000000000000 : ℝ)) (q := (2312273292417 / 100000000000000 : ℝ))
      (E := (cell12245 ⟨42, by decide⟩).energy) (xi := (13872602138011 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12245 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12245]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12245])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12245) (a := (8262913687723 / 10000000000000 : ℝ)) (b := (168294365147 / 100000000000000 : ℝ)) (q := (2312273292417 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12245])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12245])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12245]

theorem cert12245_43 : CellCertificate 12245 (899855387084573 / 10000000000000000 : ℝ) (1715368339701469 / 1000000000000000000 : ℝ) (13872602138011 / 400000000000000 : ℝ)
    (cell12245 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · have h := gap_lower (n := 12245) (a := (82595038522843 / 100000000000000 : ℝ)) (b := (168294365147 / 100000000000000 : ℝ)) (q := (1156138641599 / 50000000000000 : ℝ))
      (E := (cell12245 ⟨43, by decide⟩).energy) (xi := (13872602138011 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12245 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12245]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12245])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12245) (a := (82595038522843 / 100000000000000 : ℝ)) (b := (168294365147 / 100000000000000 : ℝ)) (q := (1156138641599 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12245])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12245])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12245]

theorem cert12245_44 : CellCertificate 12245 (899855387084573 / 10000000000000000 : ℝ) (1715368339701469 / 1000000000000000000 : ℝ) (13872602138011 / 400000000000000 : ℝ)
    (cell12245 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · have h := gap_lower (n := 12245) (a := (82560963917039 / 100000000000000 : ℝ)) (b := (168294365147 / 100000000000000 : ℝ)) (q := (2312281308769 / 100000000000000 : ℝ))
      (E := (cell12245 ⟨44, by decide⟩).energy) (xi := (13872602138011 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12245 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12245]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12245])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12245) (a := (82560963917039 / 100000000000000 : ℝ)) (b := (168294365147 / 100000000000000 : ℝ)) (q := (2312281308769 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12245])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12245])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12245]

theorem cert12245_45 : CellCertificate 12245 (899855387084573 / 10000000000000000 : ℝ) (1715368339701469 / 1000000000000000000 : ℝ) (13872602138011 / 400000000000000 : ℝ)
    (cell12245 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · have h := gap_lower (n := 12245) (a := (41263456515037 / 50000000000000 : ℝ)) (b := (168294365147 / 100000000000000 : ℝ)) (q := (1156142654917 / 50000000000000 : ℝ))
      (E := (cell12245 ⟨45, by decide⟩).energy) (xi := (13872602138011 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12245 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12245]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12245])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12245) (a := (41263456515037 / 50000000000000 : ℝ)) (b := (168294365147 / 100000000000000 : ℝ)) (q := (1156142654917 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12245])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12245])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12245]

theorem cert12245_46 : CellCertificate 12245 (899855387084573 / 10000000000000000 : ℝ) (1715368339701469 / 1000000000000000000 : ℝ) (13872602138011 / 400000000000000 : ℝ)
    (cell12245 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · have h := gap_lower (n := 12245) (a := (2577902682261 / 3125000000000 : ℝ)) (b := (168294365147 / 100000000000000 : ℝ)) (q := (578072321407 / 25000000000000 : ℝ))
      (E := (cell12245 ⟨46, by decide⟩).energy) (xi := (13872602138011 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12245 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12245]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12245])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12245) (a := (2577902682261 / 3125000000000 : ℝ)) (b := (168294365147 / 100000000000000 : ℝ)) (q := (578072321407 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12245])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12245])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12245]

theorem cert12245_47 : CellCertificate 12245 (899855387084573 / 10000000000000000 : ℝ) (1715368339701469 / 1000000000000000000 : ℝ) (13872602138011 / 400000000000000 : ℝ)
    (cell12245 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · have h := gap_lower (n := 12245) (a := (20614720573607 / 25000000000000 : ℝ)) (b := (168294365147 / 100000000000000 : ℝ)) (q := (2312293294033 / 100000000000000 : ℝ))
      (E := (cell12245 ⟨47, by decide⟩).energy) (xi := (13872602138011 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12245 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12245]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12245])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12245) (a := (20614720573607 / 25000000000000 : ℝ)) (b := (168294365147 / 100000000000000 : ℝ)) (q := (2312293294033 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12245])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12245])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12245]

theorem cert12245_48 : CellCertificate 12245 (899855387084573 / 10000000000000000 : ℝ) (1715368339701469 / 1000000000000000000 : ℝ) (13872602138011 / 400000000000000 : ℝ)
    (cell12245 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · have h := gap_lower (n := 12245) (a := (82424902387007 / 100000000000000 : ℝ)) (b := (168294365147 / 100000000000000 : ℝ)) (q := (578074318757 / 25000000000000 : ℝ))
      (E := (cell12245 ⟨48, by decide⟩).energy) (xi := (13872602138011 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12245 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12245]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12245])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12245) (a := (82424902387007 / 100000000000000 : ℝ)) (b := (168294365147 / 100000000000000 : ℝ)) (q := (578074318757 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12245])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12245])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12245]

theorem cert12245_49 : CellCertificate 12245 (899855387084573 / 10000000000000000 : ℝ) (1715368339701469 / 1000000000000000000 : ℝ) (13872602138011 / 400000000000000 : ℝ)
    (cell12245 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · have h := gap_lower (n := 12245) (a := (41195473040469 / 50000000000000 : ℝ)) (b := (168294365147 / 100000000000000 : ℝ)) (q := (2312301286111 / 100000000000000 : ℝ))
      (E := (cell12245 ⟨49, by decide⟩).energy) (xi := (13872602138011 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12245 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12245]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12245])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12245) (a := (41195473040469 / 50000000000000 : ℝ)) (b := (168294365147 / 100000000000000 : ℝ)) (q := (2312301286111 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12245])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12245])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12245]

theorem cert12245_50 : CellCertificate 12245 (899855387084573 / 10000000000000000 : ℝ) (1715368339701469 / 1000000000000000000 : ℝ) (13872602138011 / 400000000000000 : ℝ)
    (cell12245 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · have h := gap_lower (n := 12245) (a := (82357013347221 / 100000000000000 : ℝ)) (b := (168294365147 / 100000000000000 : ℝ)) (q := (2312305266781 / 100000000000000 : ℝ))
      (E := (cell12245 ⟨50, by decide⟩).energy) (xi := (13872602138011 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12245 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12245]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12245])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12245) (a := (82357013347221 / 100000000000000 : ℝ)) (b := (168294365147 / 100000000000000 : ℝ)) (q := (2312305266781 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12245])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12245])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12245]

theorem cert12245_51 : CellCertificate 12245 (899855387084573 / 10000000000000000 : ℝ) (1715368339701469 / 1000000000000000000 : ℝ) (13872602138011 / 400000000000000 : ℝ)
    (cell12245 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · have h := gap_lower (n := 12245) (a := (41161552078499 / 50000000000000 : ℝ)) (b := (168294365147 / 100000000000000 : ℝ)) (q := (2312309274153 / 100000000000000 : ℝ))
      (E := (cell12245 ⟨51, by decide⟩).energy) (xi := (13872602138011 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12245 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12245]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12245])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12245) (a := (41161552078499 / 50000000000000 : ℝ)) (b := (168294365147 / 100000000000000 : ℝ)) (q := (2312309274153 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12245])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12245])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12245]

theorem cert12245_52 : CellCertificate 12245 (899855387084573 / 10000000000000000 : ℝ) (1715368339701469 / 1000000000000000000 : ℝ) (13872602138011 / 400000000000000 : ℝ)
    (cell12245 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · have h := gap_lower (n := 12245) (a := (2057230462039 / 2500000000000 : ℝ)) (b := (168294365147 / 100000000000000 : ℝ)) (q := (2312313247251 / 100000000000000 : ℝ))
      (E := (cell12245 ⟨52, by decide⟩).energy) (xi := (13872602138011 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12245 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12245]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12245])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12245) (a := (2057230462039 / 2500000000000 : ℝ)) (b := (168294365147 / 100000000000000 : ℝ)) (q := (2312313247251 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12245])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12245])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12245]

theorem cert12245_53 : CellCertificate 12245 (899855387084573 / 10000000000000000 : ℝ) (1715368339701469 / 1000000000000000000 : ℝ) (13872602138011 / 400000000000000 : ℝ)
    (cell12245 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · have h := gap_lower (n := 12245) (a := (82255356292337 / 100000000000000 : ℝ)) (b := (168294365147 / 100000000000000 : ℝ)) (q := (578079310703 / 25000000000000 : ℝ))
      (E := (cell12245 ⟨53, by decide⟩).energy) (xi := (13872602138011 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12245 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12245]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12245])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12245) (a := (82255356292337 / 100000000000000 : ℝ)) (b := (168294365147 / 100000000000000 : ℝ)) (q := (578079310703 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12245])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12245])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12245]

theorem cert12245_54 : CellCertificate 12245 (899855387084573 / 10000000000000000 : ℝ) (1715368339701469 / 1000000000000000000 : ℝ) (13872602138011 / 400000000000000 : ℝ)
    (cell12245 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · have h := gap_lower (n := 12245) (a := (20555379390227 / 25000000000000 : ℝ)) (b := (168294365147 / 100000000000000 : ℝ)) (q := (144520078651 / 6250000000000 : ℝ))
      (E := (cell12245 ⟨54, by decide⟩).energy) (xi := (13872602138011 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12245 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12245]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12245])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12245) (a := (20555379390227 / 25000000000000 : ℝ)) (b := (168294365147 / 100000000000000 : ℝ)) (q := (144520078651 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12245])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12245])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12245]

theorem cert12245_55 : CellCertificate 12245 (899855387084573 / 10000000000000000 : ℝ) (1715368339701469 / 1000000000000000000 : ℝ) (13872602138011 / 400000000000000 : ℝ)
    (cell12245 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · have h := gap_lower (n := 12245) (a := (5136731391187 / 6250000000000 : ℝ)) (b := (168294365147 / 100000000000000 : ℝ)) (q := (462465046477 / 20000000000000 : ℝ))
      (E := (cell12245 ⟨55, by decide⟩).energy) (xi := (13872602138011 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12245 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12245]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12245])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12245) (a := (5136731391187 / 6250000000000 : ℝ)) (b := (168294365147 / 100000000000000 : ℝ)) (q := (462465046477 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12245])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12245])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12245]

theorem cert12245_56 : CellCertificate 12245 (899855387084573 / 10000000000000000 : ℝ) (1715368339701469 / 1000000000000000000 : ℝ) (13872602138011 / 400000000000000 : ℝ)
    (cell12245 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · have h := gap_lower (n := 12245) (a := (5134619397403 / 6250000000000 : ℝ)) (b := (168294365147 / 100000000000000 : ℝ)) (q := (1156164639983 / 50000000000000 : ℝ))
      (E := (cell12245 ⟨56, by decide⟩).energy) (xi := (13872602138011 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12245 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12245]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12245])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12245) (a := (5134619397403 / 6250000000000 : ℝ)) (b := (168294365147 / 100000000000000 : ℝ)) (q := (1156164639983 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12245])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12245])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12245]

theorem cert12245_57 : CellCertificate 12245 (899855387084573 / 10000000000000000 : ℝ) (1715368339701469 / 1000000000000000000 : ℝ) (13872602138011 / 400000000000000 : ℝ)
    (cell12245 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · have h := gap_lower (n := 12245) (a := (1026501772891 / 1250000000000 : ℝ)) (b := (168294365147 / 100000000000000 : ℝ)) (q := (2312333279979 / 100000000000000 : ℝ))
      (E := (cell12245 ⟨57, by decide⟩).energy) (xi := (13872602138011 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12245 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12245]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12245])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12245) (a := (1026501772891 / 1250000000000 : ℝ)) (b := (168294365147 / 100000000000000 : ℝ)) (q := (2312333279979 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12245])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12245])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12245]

theorem cert12245_58 : CellCertificate 12245 (899855387084573 / 10000000000000000 : ℝ) (1715368339701469 / 1000000000000000000 : ℝ) (13872602138011 / 400000000000000 : ℝ)
    (cell12245 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · have h := gap_lower (n := 12245) (a := (20521599162407 / 25000000000000 : ℝ)) (b := (168294365147 / 100000000000000 : ℝ)) (q := (2312337229097 / 100000000000000 : ℝ))
      (E := (cell12245 ⟨58, by decide⟩).energy) (xi := (13872602138011 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12245 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12245]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12245])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12245) (a := (20521599162407 / 25000000000000 : ℝ)) (b := (168294365147 / 100000000000000 : ℝ)) (q := (2312337229097 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12245])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12245])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12245]

theorem cert12245_59 : CellCertificate 12245 (899855387084573 / 10000000000000000 : ℝ) (1715368339701469 / 1000000000000000000 : ℝ) (13872602138011 / 400000000000000 : ℝ)
    (cell12245 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · have h := gap_lower (n := 12245) (a := (3282106991431 / 4000000000000 : ℝ)) (b := (168294365147 / 100000000000000 : ℝ)) (q := (1156170621041 / 50000000000000 : ℝ))
      (E := (cell12245 ⟨59, by decide⟩).energy) (xi := (13872602138011 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12245 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12245]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12245])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12245) (a := (3282106991431 / 4000000000000 : ℝ)) (b := (168294365147 / 100000000000000 : ℝ)) (q := (1156170621041 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12245])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12245])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12245]

theorem cert12246_40 : CellCertificate 12246 (899825421411191 / 10000000000000000 : ℝ) (428807054032799 / 250000000000000000 : ℝ) (173392986316643 / 5000000000000000 : ℝ)
    (cell12246 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · have h := gap_lower (n := 12246) (a := (82697401856223 / 100000000000000 : ℝ)) (b := (84140218957 / 50000000000000 : ℝ)) (q := (2312117665711 / 100000000000000 : ℝ))
      (E := (cell12246 ⟨40, by decide⟩).energy) (xi := (173392986316643 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12246 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12246]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12246])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12246) (a := (82697401856223 / 100000000000000 : ℝ)) (b := (84140218957 / 50000000000000 : ℝ)) (q := (2312117665711 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12246])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12246])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12246]

theorem cert12246_41 : CellCertificate 12246 (899825421411191 / 10000000000000000 : ℝ) (428807054032799 / 250000000000000000 : ℝ) (173392986316643 / 5000000000000000 : ℝ)
    (cell12246 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · have h := gap_lower (n := 12246) (a := (2583226757343 / 3125000000000 : ℝ)) (b := (84140218957 / 50000000000000 : ℝ)) (q := (144507604371 / 6250000000000 : ℝ))
      (E := (cell12246 ⟨41, by decide⟩).energy) (xi := (173392986316643 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12246 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12246]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12246])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12246) (a := (2583226757343 / 3125000000000 : ℝ)) (b := (84140218957 / 50000000000000 : ℝ)) (q := (144507604371 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12246])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12246])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12246]

theorem cert12246_42 : CellCertificate 12246 (899825421411191 / 10000000000000000 : ℝ) (428807054032799 / 250000000000000000 : ℝ) (173392986316643 / 5000000000000000 : ℝ)
    (cell12246 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · have h := gap_lower (n := 12246) (a := (82629134421811 / 100000000000000 : ℝ)) (b := (84140218957 / 50000000000000 : ℝ)) (q := (144507853207 / 6250000000000 : ℝ))
      (E := (cell12246 ⟨42, by decide⟩).energy) (xi := (173392986316643 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12246 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12246]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12246])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12246) (a := (82629134421811 / 100000000000000 : ℝ)) (b := (84140218957 / 50000000000000 : ℝ)) (q := (144507853207 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12246])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12246])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12246]

theorem cert12246_43 : CellCertificate 12246 (899825421411191 / 10000000000000000 : ℝ) (428807054032799 / 250000000000000000 : ℝ) (173392986316643 / 5000000000000000 : ℝ)
    (cell12246 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · have h := gap_lower (n := 12246) (a := (20648759096671 / 25000000000000 : ℝ)) (b := (84140218957 / 50000000000000 : ℝ)) (q := (4624259337 / 200000000000 : ℝ))
      (E := (cell12246 ⟨43, by decide⟩).energy) (xi := (173392986316643 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12246 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12246]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12246])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12246) (a := (20648759096671 / 25000000000000 : ℝ)) (b := (84140218957 / 50000000000000 : ℝ)) (q := (4624259337 / 200000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12246])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12246])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12246]

theorem cert12246_44 : CellCertificate 12246 (899825421411191 / 10000000000000000 : ℝ) (428807054032799 / 250000000000000000 : ℝ) (173392986316643 / 5000000000000000 : ℝ)
    (cell12246 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · have h := gap_lower (n := 12246) (a := (82560962099697 / 100000000000000 : ℝ)) (b := (84140218957 / 50000000000000 : ℝ)) (q := (144508353903 / 6250000000000 : ℝ))
      (E := (cell12246 ⟨44, by decide⟩).energy) (xi := (173392986316643 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12246 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12246]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12246])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12246) (a := (82560962099697 / 100000000000000 : ℝ)) (b := (84140218957 / 50000000000000 : ℝ)) (q := (144508353903 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12246])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12246])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12246]

theorem cert12246_45 : CellCertificate 12246 (899825421411191 / 10000000000000000 : ℝ) (428807054032799 / 250000000000000000 : ℝ) (173392986316643 / 5000000000000000 : ℝ)
    (cell12246 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · have h := gap_lower (n := 12246) (a := (82526911531107 / 100000000000000 : ℝ)) (b := (84140218957 / 50000000000000 : ℝ)) (q := (72254301019 / 3125000000000 : ℝ))
      (E := (cell12246 ⟨45, by decide⟩).energy) (xi := (173392986316643 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12246 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12246]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12246])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12246) (a := (82526911531107 / 100000000000000 : ℝ)) (b := (84140218957 / 50000000000000 : ℝ)) (q := (72254301019 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12246])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12246])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12246]

theorem cert12246_46 : CellCertificate 12246 (899825421411191 / 10000000000000000 : ℝ) (428807054032799 / 250000000000000000 : ℝ) (173392986316643 / 5000000000000000 : ℝ)
    (cell12246 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · have h := gap_lower (n := 12246) (a := (82492884651321 / 100000000000000 : ℝ)) (b := (84140218957 / 50000000000000 : ℝ)) (q := (1156070818527 / 50000000000000 : ℝ))
      (E := (cell12246 ⟨46, by decide⟩).energy) (xi := (173392986316643 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12246 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12246]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12246])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12246) (a := (82492884651321 / 100000000000000 : ℝ)) (b := (84140218957 / 50000000000000 : ℝ)) (q := (1156070818527 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12246])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12246])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12246]

theorem cert12246_47 : CellCertificate 12246 (899825421411191 / 10000000000000000 : ℝ) (428807054032799 / 250000000000000000 : ℝ) (173392986316643 / 5000000000000000 : ℝ)
    (cell12246 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · have h := gap_lower (n := 12246) (a := (82458881430893 / 100000000000000 : ℝ)) (b := (84140218957 / 50000000000000 : ℝ)) (q := (2312145674873 / 100000000000000 : ℝ))
      (E := (cell12246 ⟨47, by decide⟩).energy) (xi := (173392986316643 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12246 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12246]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12246])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12246) (a := (82458881430893 / 100000000000000 : ℝ)) (b := (84140218957 / 50000000000000 : ℝ)) (q := (2312145674873 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12246])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12246])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12246]

theorem cert12246_48 : CellCertificate 12246 (899825421411191 / 10000000000000000 : ℝ) (428807054032799 / 250000000000000000 : ℝ) (173392986316643 / 5000000000000000 : ℝ)
    (cell12246 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · have h := gap_lower (n := 12246) (a := (82424901840529 / 100000000000000 : ℝ)) (b := (84140218957 / 50000000000000 : ℝ)) (q := (578037406789 / 25000000000000 : ℝ))
      (E := (cell12246 ⟨48, by decide⟩).energy) (xi := (173392986316643 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12246 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12246]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12246])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12246) (a := (82424901840529 / 100000000000000 : ℝ)) (b := (84140218957 / 50000000000000 : ℝ)) (q := (578037406789 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12246])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12246])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12246]

theorem cert12246_49 : CellCertificate 12246 (899825421411191 / 10000000000000000 : ℝ) (428807054032799 / 250000000000000000 : ℝ) (173392986316643 / 5000000000000000 : ℝ)
    (cell12246 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · have h := gap_lower (n := 12246) (a := (82390945851081 / 100000000000000 : ℝ)) (b := (84140218957 / 50000000000000 : ℝ)) (q := (1156076805119 / 50000000000000 : ℝ))
      (E := (cell12246 ⟨49, by decide⟩).energy) (xi := (173392986316643 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12246 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12246]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12246])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12246) (a := (82390945851081 / 100000000000000 : ℝ)) (b := (84140218957 / 50000000000000 : ℝ)) (q := (1156076805119 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12246])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12246])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12246]

theorem cert12246_50 : CellCertificate 12246 (899825421411191 / 10000000000000000 : ℝ) (428807054032799 / 250000000000000000 : ℝ) (173392986316643 / 5000000000000000 : ℝ)
    (cell12246 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · have h := gap_lower (n := 12246) (a := (41178506716773 / 50000000000000 : ℝ)) (b := (84140218957 / 50000000000000 : ℝ)) (q := (1156078811279 / 50000000000000 : ℝ))
      (E := (cell12246 ⟨50, by decide⟩).energy) (xi := (173392986316643 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12246 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12246]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12246])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12246) (a := (41178506716773 / 50000000000000 : ℝ)) (b := (84140218957 / 50000000000000 : ℝ)) (q := (1156078811279 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12246])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12246])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12246]

theorem cert12246_51 : CellCertificate 12246 (899825421411191 / 10000000000000000 : ℝ) (428807054032799 / 250000000000000000 : ℝ) (173392986316643 / 5000000000000000 : ℝ)
    (cell12246 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · have h := gap_lower (n := 12246) (a := (82323104559069 / 100000000000000 : ℝ)) (b := (84140218957 / 50000000000000 : ℝ)) (q := (115608080169 / 5000000000000 : ℝ))
      (E := (cell12246 ⟨51, by decide⟩).energy) (xi := (173392986316643 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12246 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12246]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12246])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12246) (a := (82323104559069 / 100000000000000 : ℝ)) (b := (84140218957 / 50000000000000 : ℝ)) (q := (115608080169 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12246])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12246])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12246]

theorem cert12246_52 : CellCertificate 12246 (899825421411191 / 10000000000000000 : ℝ) (428807054032799 / 250000000000000000 : ℝ) (173392986316643 / 5000000000000000 : ℝ)
    (cell12246 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · have h := gap_lower (n := 12246) (a := (82289219198941 / 100000000000000 : ℝ)) (b := (84140218957 / 50000000000000 : ℝ)) (q := (2312165609623 / 100000000000000 : ℝ))
      (E := (cell12246 ⟨52, by decide⟩).energy) (xi := (173392986316643 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12246 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12246]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12246])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12246) (a := (82289219198941 / 100000000000000 : ℝ)) (b := (84140218957 / 50000000000000 : ℝ)) (q := (2312165609623 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12246])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12246])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12246]

theorem cert12246_53 : CellCertificate 12246 (899825421411191 / 10000000000000000 : ℝ) (428807054032799 / 250000000000000000 : ℝ) (173392986316643 / 5000000000000000 : ℝ)
    (cell12246 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · have h := gap_lower (n := 12246) (a := (41127678662297 / 50000000000000 : ℝ)) (b := (84140218957 / 50000000000000 : ℝ)) (q := (462433927817 / 20000000000000 : ℝ))
      (E := (cell12246 ⟨53, by decide⟩).energy) (xi := (173392986316643 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12246 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12246]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12246])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12246) (a := (41127678662297 / 50000000000000 : ℝ)) (b := (84140218957 / 50000000000000 : ℝ)) (q := (462433927817 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12246])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12246])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12246]

theorem cert12246_54 : CellCertificate 12246 (899825421411191 / 10000000000000000 : ℝ) (428807054032799 / 250000000000000000 : ℝ) (173392986316643 / 5000000000000000 : ℝ)
    (cell12246 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · have h := gap_lower (n := 12246) (a := (41110759453803 / 50000000000000 : ℝ)) (b := (84140218957 / 50000000000000 : ℝ)) (q := (28902170379 / 1250000000000 : ℝ))
      (E := (cell12246 ⟨54, by decide⟩).energy) (xi := (173392986316643 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12246 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12246]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12246])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12246) (a := (41110759453803 / 50000000000000 : ℝ)) (b := (84140218957 / 50000000000000 : ℝ)) (q := (28902170379 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12246])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12246])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12246]

theorem cert12246_55 : CellCertificate 12246 (899825421411191 / 10000000000000000 : ℝ) (428807054032799 / 250000000000000000 : ℝ) (173392986316643 / 5000000000000000 : ℝ)
    (cell12246 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · have h := gap_lower (n := 12246) (a := (41093851959849 / 50000000000000 : ℝ)) (b := (84140218957 / 50000000000000 : ℝ)) (q := (2312177639681 / 100000000000000 : ℝ))
      (E := (cell12246 ⟨55, by decide⟩).energy) (xi := (173392986316643 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12246 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12246]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12246])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12246) (a := (41093851959849 / 50000000000000 : ℝ)) (b := (84140218957 / 50000000000000 : ℝ)) (q := (2312177639681 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12246])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12246])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12246]

theorem cert12246_56 : CellCertificate 12246 (899825421411191 / 10000000000000000 : ℝ) (428807054032799 / 250000000000000000 : ℝ) (173392986316643 / 5000000000000000 : ℝ)
    (cell12246 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · have h := gap_lower (n := 12246) (a := (8215391233273 / 10000000000000 : ℝ)) (b := (84140218957 / 50000000000000 : ℝ)) (q := (289022700657 / 12500000000000 : ℝ))
      (E := (cell12246 ⟨56, by decide⟩).energy) (xi := (173392986316643 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12246 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12246]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12246])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12246) (a := (8215391233273 / 10000000000000 : ℝ)) (b := (84140218957 / 50000000000000 : ℝ)) (q := (289022700657 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12246])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12246])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12246]

theorem cert12246_57 : CellCertificate 12246 (899825421411191 / 10000000000000000 : ℝ) (428807054032799 / 250000000000000000 : ℝ) (173392986316643 / 5000000000000000 : ℝ)
    (cell12246 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · have h := gap_lower (n := 12246) (a := (16424028823741 / 20000000000000 : ℝ)) (b := (84140218957 / 50000000000000 : ℝ)) (q := (144511598939 / 6250000000000 : ℝ))
      (E := (cell12246 ⟨57, by decide⟩).energy) (xi := (173392986316643 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12246 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12246]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12246])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12246) (a := (16424028823741 / 20000000000000 : ℝ)) (b := (84140218957 / 50000000000000 : ℝ)) (q := (144511598939 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12246])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12246])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12246]

theorem cert12246_58 : CellCertificate 12246 (899825421411191 / 10000000000000000 : ℝ) (428807054032799 / 250000000000000000 : ℝ) (173392986316643 / 5000000000000000 : ℝ)
    (cell12246 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · have h := gap_lower (n := 12246) (a := (16417279849953 / 20000000000000 : ℝ)) (b := (84140218957 / 50000000000000 : ℝ)) (q := (289023703607 / 12500000000000 : ℝ))
      (E := (cell12246 ⟨58, by decide⟩).energy) (xi := (173392986316643 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12246 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12246]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12246])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12246) (a := (16417279849953 / 20000000000000 : ℝ)) (b := (84140218957 / 50000000000000 : ℝ)) (q := (289023703607 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12246])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12246])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12246]

theorem cert12246_59 : CellCertificate 12246 (899825421411191 / 10000000000000000 : ℝ) (428807054032799 / 250000000000000000 : ℝ) (173392986316643 / 5000000000000000 : ℝ)
    (cell12246 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · have h := gap_lower (n := 12246) (a := (41026338849097 / 50000000000000 : ℝ)) (b := (84140218957 / 50000000000000 : ℝ)) (q := (2312193621057 / 100000000000000 : ℝ))
      (E := (cell12246 ⟨59, by decide⟩).energy) (xi := (173392986316643 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12246 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12246]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12246])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12246) (a := (41026338849097 / 50000000000000 : ℝ)) (b := (84140218957 / 50000000000000 : ℝ)) (q := (2312193621057 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12246])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12246])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12246]

theorem cert12247_40 : CellCertificate 12247 (179959092090697 / 2000000000000000 : ℝ) (343017623090329 / 200000000000000000 : ℝ) (173378448409613 / 5000000000000000 : ℝ)
    (cell12247 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · have h := gap_lower (n := 12247) (a := (41348699380979 / 50000000000000 : ℝ)) (b := (21033314127 / 12500000000000 : ℝ)) (q := (2311970146537 / 100000000000000 : ℝ))
      (E := (cell12247 ⟨40, by decide⟩).energy) (xi := (173378448409613 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12247 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12247]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12247])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12247) (a := (41348699380979 / 50000000000000 : ℝ)) (b := (21033314127 / 12500000000000 : ℝ)) (q := (2311970146537 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12247])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12247])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12247]

theorem cert12247_41 : CellCertificate 12247 (179959092090697 / 2000000000000000 : ℝ) (343017623090329 / 200000000000000000 : ℝ) (173378448409613 / 5000000000000000 : ℝ)
    (cell12247 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · have h := gap_lower (n := 12247) (a := (5166453341301 / 6250000000000 : ℝ)) (b := (21033314127 / 12500000000000 : ℝ)) (q := (1155987058513 / 50000000000000 : ℝ))
      (E := (cell12247 ⟨41, by decide⟩).energy) (xi := (173378448409613 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12247 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12247]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12247])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12247) (a := (5166453341301 / 6250000000000 : ℝ)) (b := (21033314127 / 12500000000000 : ℝ)) (q := (1155987058513 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12247])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12247])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12247]

theorem cert12247_42 : CellCertificate 12247 (179959092090697 / 2000000000000000 : ℝ) (343017623090329 / 200000000000000000 : ℝ) (173378448409613 / 5000000000000000 : ℝ)
    (cell12247 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · have h := gap_lower (n := 12247) (a := (82629131967313 / 100000000000000 : ℝ)) (b := (21033314127 / 12500000000000 : ℝ)) (q := (577994531033 / 25000000000000 : ℝ))
      (E := (cell12247 ⟨42, by decide⟩).energy) (xi := (173378448409613 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12247 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12247]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12247])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12247) (a := (82629131967313 / 100000000000000 : ℝ)) (b := (21033314127 / 12500000000000 : ℝ)) (q := (577994531033 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12247])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12247])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12247]

theorem cert12247_43 : CellCertificate 12247 (179959092090697 / 2000000000000000 : ℝ) (343017623090329 / 200000000000000000 : ℝ) (173378448409613 / 5000000000000000 : ℝ)
    (cell12247 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · have h := gap_lower (n := 12247) (a := (20648758562851 / 25000000000000 : ℝ)) (b := (21033314127 / 12500000000000 : ℝ)) (q := (577995527261 / 25000000000000 : ℝ))
      (E := (cell12247 ⟨43, by decide⟩).energy) (xi := (173378448409613 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12247 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12247]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12247])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12247) (a := (20648758562851 / 25000000000000 : ℝ)) (b := (21033314127 / 12500000000000 : ℝ)) (q := (577995527261 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12247])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12247])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12247]

theorem cert12247_44 : CellCertificate 12247 (179959092090697 / 2000000000000000 : ℝ) (343017623090329 / 200000000000000000 : ℝ) (173378448409613 / 5000000000000000 : ℝ)
    (cell12247 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · have h := gap_lower (n := 12247) (a := (41280480141597 / 50000000000000 : ℝ)) (b := (21033314127 / 12500000000000 : ℝ)) (q := (2311986130229 / 100000000000000 : ℝ))
      (E := (cell12247 ⟨44, by decide⟩).energy) (xi := (173378448409613 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12247 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12247]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12247])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12247) (a := (41280480141597 / 50000000000000 : ℝ)) (b := (21033314127 / 12500000000000 : ℝ)) (q := (2311986130229 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12247])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12247])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12247]

theorem cert12247_45 : CellCertificate 12247 (179959092090697 / 2000000000000000 : ℝ) (343017623090329 / 200000000000000000 : ℝ) (173378448409613 / 5000000000000000 : ℝ)
    (cell12247 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · have h := gap_lower (n := 12247) (a := (4126345501647 / 5000000000000 : ℝ)) (b := (21033314127 / 12500000000000 : ℝ)) (q := (2311990069571 / 100000000000000 : ℝ))
      (E := (cell12247 ⟨45, by decide⟩).energy) (xi := (173378448409613 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12247 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12247]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12247])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12247) (a := (4126345501647 / 5000000000000 : ℝ)) (b := (21033314127 / 12500000000000 : ℝ)) (q := (2311990069571 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12247])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12247])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12247]

theorem cert12247_46 : CellCertificate 12247 (179959092090697 / 2000000000000000 : ℝ) (343017623090329 / 200000000000000000 : ℝ) (173378448409613 / 5000000000000000 : ℝ)
    (cell12247 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · have h := gap_lower (n := 12247) (a := (82492883471049 / 100000000000000 : ℝ)) (b := (21033314127 / 12500000000000 : ℝ)) (q := (1155997051379 / 50000000000000 : ℝ))
      (E := (cell12247 ⟨46, by decide⟩).energy) (xi := (173378448409613 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12247 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12247]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12247])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12247) (a := (82492883471049 / 100000000000000 : ℝ)) (b := (21033314127 / 12500000000000 : ℝ)) (q := (1155997051379 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12247])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12247])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12247]

theorem cert12247_47 : CellCertificate 12247 (179959092090697 / 2000000000000000 : ℝ) (343017623090329 / 200000000000000000 : ℝ) (173378448409613 / 5000000000000000 : ℝ)
    (cell12247 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · have h := gap_lower (n := 12247) (a := (41229440284039 / 50000000000000 : ℝ)) (b := (21033314127 / 12500000000000 : ℝ)) (q := (1155999055607 / 50000000000000 : ℝ))
      (E := (cell12247 ⟨47, by decide⟩).energy) (xi := (173378448409613 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12247 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12247]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12247])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12247) (a := (41229440284039 / 50000000000000 : ℝ)) (b := (21033314127 / 12500000000000 : ℝ)) (q := (1155999055607 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12247])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12247])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12247]

theorem cert12247_48 : CellCertificate 12247 (179959092090697 / 2000000000000000 : ℝ) (343017623090329 / 200000000000000000 : ℝ) (173378448409613 / 5000000000000000 : ℝ)
    (cell12247 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · have h := gap_lower (n := 12247) (a := (20606225323683 / 25000000000000 : ℝ)) (b := (21033314127 / 12500000000000 : ℝ)) (q := (289000261717 / 12500000000000 : ℝ))
      (E := (cell12247 ⟨48, by decide⟩).energy) (xi := (173378448409613 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12247 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12247]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12247])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12247) (a := (20606225323683 / 25000000000000 : ℝ)) (b := (21033314127 / 12500000000000 : ℝ)) (q := (289000261717 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12247])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12247])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12247]

theorem cert12247_49 : CellCertificate 12247 (179959092090697 / 2000000000000000 : ℝ) (343017623090329 / 200000000000000000 : ℝ) (173378448409613 / 5000000000000000 : ℝ)
    (cell12247 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · have h := gap_lower (n := 12247) (a := (82390945621863 / 100000000000000 : ℝ)) (b := (21033314127 / 12500000000000 : ℝ)) (q := (115600305391 / 5000000000000 : ℝ))
      (E := (cell12247 ⟨49, by decide⟩).energy) (xi := (173378448409613 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12247 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12247]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12247])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12247) (a := (82390945621863 / 100000000000000 : ℝ)) (b := (21033314127 / 12500000000000 : ℝ)) (q := (115600305391 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12247])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12247])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12247]

theorem cert12247_50 : CellCertificate 12247 (179959092090697 / 2000000000000000 : ℝ) (343017623090329 / 200000000000000000 : ℝ) (173378448409613 / 5000000000000000 : ℝ)
    (cell12247 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · have h := gap_lower (n := 12247) (a := (82357013520471 / 100000000000000 : ℝ)) (b := (21033314127 / 12500000000000 : ℝ)) (q := (1156005046483 / 50000000000000 : ℝ))
      (E := (cell12247 ⟨50, by decide⟩).energy) (xi := (173378448409613 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12247 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12247]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12247])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12247) (a := (82357013520471 / 100000000000000 : ℝ)) (b := (21033314127 / 12500000000000 : ℝ)) (q := (1156005046483 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12247])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12247])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12247]

theorem cert12247_51 : CellCertificate 12247 (179959092090697 / 2000000000000000 : ℝ) (343017623090329 / 200000000000000000 : ℝ) (173378448409613 / 5000000000000000 : ℝ)
    (cell12247 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · have h := gap_lower (n := 12247) (a := (82323104961701 / 100000000000000 : ℝ)) (b := (21033314127 / 12500000000000 : ℝ)) (q := (578003511831 / 25000000000000 : ℝ))
      (E := (cell12247 ⟨51, by decide⟩).energy) (xi := (173378448409613 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12247 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12247]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12247])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12247) (a := (82323104961701 / 100000000000000 : ℝ)) (b := (21033314127 / 12500000000000 : ℝ)) (q := (578003511831 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12247])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12247])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12247]

theorem cert12247_52 : CellCertificate 12247 (179959092090697 / 2000000000000000 : ℝ) (343017623090329 / 200000000000000000 : ℝ) (173378448409613 / 5000000000000000 : ℝ)
    (cell12247 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · have h := gap_lower (n := 12247) (a := (82289219916843 / 100000000000000 : ℝ)) (b := (21033314127 / 12500000000000 : ℝ)) (q := (5780045217 / 250000000000 : ℝ))
      (E := (cell12247 ⟨52, by decide⟩).energy) (xi := (173378448409613 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12247 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12247]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12247])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12247) (a := (82289219916843 / 100000000000000 : ℝ)) (b := (21033314127 / 12500000000000 : ℝ)) (q := (5780045217 / 250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12247])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12247])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12247]

theorem cert12247_53 : CellCertificate 12247 (179959092090697 / 2000000000000000 : ℝ) (343017623090329 / 200000000000000000 : ℝ) (173378448409613 / 5000000000000000 : ℝ)
    (cell12247 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · have h := gap_lower (n := 12247) (a := (20563839589333 / 25000000000000 : ℝ)) (b := (21033314127 / 12500000000000 : ℝ)) (q := (1156011045623 / 50000000000000 : ℝ))
      (E := (cell12247 ⟨53, by decide⟩).energy) (xi := (173378448409613 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12247 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12247]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12247])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12247) (a := (20563839589333 / 25000000000000 : ℝ)) (b := (21033314127 / 12500000000000 : ℝ)) (q := (1156011045623 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12247])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12247])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12247]

theorem cert12247_54 : CellCertificate 12247 (179959092090697 / 2000000000000000 : ℝ) (343017623090329 / 200000000000000000 : ℝ) (173378448409613 / 5000000000000000 : ℝ)
    (cell12247 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · have h := gap_lower (n := 12247) (a := (41110760127373 / 50000000000000 : ℝ)) (b := (21033314127 / 12500000000000 : ℝ)) (q := (1156013029087 / 50000000000000 : ℝ))
      (E := (cell12247 ⟨54, by decide⟩).energy) (xi := (173378448409613 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12247 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12247]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12247])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12247) (a := (41110760127373 / 50000000000000 : ℝ)) (b := (21033314127 / 12500000000000 : ℝ)) (q := (1156013029087 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12247])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12247])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12247]

theorem cert12247_55 : CellCertificate 12247 (179959092090697 / 2000000000000000 : ℝ) (343017623090329 / 200000000000000000 : ℝ) (173378448409613 / 5000000000000000 : ℝ)
    (cell12247 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · have h := gap_lower (n := 12247) (a := (41093852790403 / 50000000000000 : ℝ)) (b := (21033314127 / 12500000000000 : ℝ)) (q := (2312030043939 / 100000000000000 : ℝ))
      (E := (cell12247 ⟨55, by decide⟩).energy) (xi := (173378448409613 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12247 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12247]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12247])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12247) (a := (41093852790403 / 50000000000000 : ℝ)) (b := (21033314127 / 12500000000000 : ℝ)) (q := (2312030043939 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12247])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12247])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12247]

theorem cert12247_56 : CellCertificate 12247 (179959092090697 / 2000000000000000 : ℝ) (343017623090329 / 200000000000000000 : ℝ) (173378448409613 / 5000000000000000 : ℝ)
    (cell12247 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · have h := gap_lower (n := 12247) (a := (41076957153687 / 50000000000000 : ℝ)) (b := (21033314127 / 12500000000000 : ℝ)) (q := (2312034045703 / 100000000000000 : ℝ))
      (E := (cell12247 ⟨56, by decide⟩).energy) (xi := (173378448409613 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12247 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12247]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12247])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12247) (a := (41076957153687 / 50000000000000 : ℝ)) (b := (21033314127 / 12500000000000 : ℝ)) (q := (2312034045703 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12247])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12247])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12247]

theorem cert12247_57 : CellCertificate 12247 (179959092090697 / 2000000000000000 : ℝ) (343017623090329 / 200000000000000000 : ℝ) (173378448409613 / 5000000000000000 : ℝ)
    (cell12247 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · have h := gap_lower (n := 12247) (a := (41060073203227 / 50000000000000 : ℝ)) (b := (21033314127 / 12500000000000 : ℝ)) (q := (462407612083 / 20000000000000 : ℝ))
      (E := (cell12247 ⟨57, by decide⟩).energy) (xi := (173378448409613 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12247 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12247]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12247])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12247) (a := (41060073203227 / 50000000000000 : ℝ)) (b := (21033314127 / 12500000000000 : ℝ)) (q := (462407612083 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12247])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12247])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12247]

theorem cert12247_58 : CellCertificate 12247 (179959092090697 / 2000000000000000 : ℝ) (343017623090329 / 200000000000000000 : ℝ) (173378448409613 / 5000000000000000 : ℝ)
    (cell12247 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · have h := gap_lower (n := 12247) (a := (82086401850187 / 100000000000000 : ℝ)) (b := (21033314127 / 12500000000000 : ℝ)) (q := (72251313303 / 3125000000000 : ℝ))
      (E := (cell12247 ⟨58, by decide⟩).energy) (xi := (173378448409613 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12247 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12247]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12247])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12247) (a := (82086401850187 / 100000000000000 : ℝ)) (b := (21033314127 / 12500000000000 : ℝ)) (q := (72251313303 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12247])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12247])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12247]

theorem cert12247_59 : CellCertificate 12247 (179959092090697 / 2000000000000000 : ℝ) (343017623090329 / 200000000000000000 : ℝ) (173378448409613 / 5000000000000000 : ℝ)
    (cell12247 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · have h := gap_lower (n := 12247) (a := (82052680610859 / 100000000000000 : ℝ)) (b := (21033314127 / 12500000000000 : ℝ)) (q := (1156023028151 / 50000000000000 : ℝ))
      (E := (cell12247 ⟨59, by decide⟩).energy) (xi := (173378448409613 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12247 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12247]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12247])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12247) (a := (82052680610859 / 100000000000000 : ℝ)) (b := (21033314127 / 12500000000000 : ℝ)) (q := (1156023028151 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12247])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12247])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12247]

theorem cert12248_40 : CellCertificate 12248 (899765504210291 / 10000000000000000 : ℝ) (342989607531441 / 200000000000000000 : ℝ) (86681956501657 / 2500000000000000 : ℝ)
    (cell12248 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · have h := gap_lower (n := 12248) (a := (41348697834347 / 50000000000000 : ℝ)) (b := (168252590453 / 100000000000000 : ℝ)) (q := (231182262371 / 10000000000000 : ℝ))
      (E := (cell12248 ⟨40, by decide⟩).energy) (xi := (86681956501657 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12248 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12248]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12248])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12248) (a := (41348697834347 / 50000000000000 : ℝ)) (b := (168252590453 / 100000000000000 : ℝ)) (q := (231182262371 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12248])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12248])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12248]

theorem cert12248_41 : CellCertificate 12248 (899765504210291 / 10000000000000000 : ℝ) (342989607531441 / 200000000000000000 : ℝ) (86681956501657 / 2500000000000000 : ℝ)
    (cell12248 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · have h := gap_lower (n := 12248) (a := (16532650137523 / 20000000000000 : ℝ)) (b := (168252590453 / 100000000000000 : ℝ)) (q := (2311826619229 / 100000000000000 : ℝ))
      (E := (cell12248 ⟨41, by decide⟩).energy) (xi := (86681956501657 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12248 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12248]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12248])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12248) (a := (16532650137523 / 20000000000000 : ℝ)) (b := (168252590453 / 100000000000000 : ℝ)) (q := (2311826619229 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12248])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12248])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12248]

theorem cert12248_42 : CellCertificate 12248 (899765504210291 / 10000000000000000 : ℝ) (342989607531441 / 200000000000000000 : ℝ) (86681956501657 / 2500000000000000 : ℝ)
    (cell12248 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · have h := gap_lower (n := 12248) (a := (41314564756867 / 50000000000000 : ℝ)) (b := (168252590453 / 100000000000000 : ℝ)) (q := (2311830652129 / 100000000000000 : ℝ))
      (E := (cell12248 ⟨42, by decide⟩).energy) (xi := (86681956501657 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12248 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12248]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12248])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12248) (a := (41314564756867 / 50000000000000 : ℝ)) (b := (168252590453 / 100000000000000 : ℝ)) (q := (2311830652129 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12248])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12248])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12248]

theorem cert12248_43 : CellCertificate 12248 (899765504210291 / 10000000000000000 : ℝ) (342989607531441 / 200000000000000000 : ℝ) (86681956501657 / 2500000000000000 : ℝ)
    (cell12248 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · have h := gap_lower (n := 12248) (a := (82595032117003 / 100000000000000 : ℝ)) (b := (168252590453 / 100000000000000 : ℝ)) (q := (2311834663603 / 100000000000000 : ℝ))
      (E := (cell12248 ⟨43, by decide⟩).energy) (xi := (86681956501657 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12248 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12248]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12248])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12248) (a := (82595032117003 / 100000000000000 : ℝ)) (b := (168252590453 / 100000000000000 : ℝ)) (q := (2311834663603 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12248])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12248])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12248]

theorem cert12248_44 : CellCertificate 12248 (899765504210291 / 10000000000000000 : ℝ) (342989607531441 / 200000000000000000 : ℝ) (86681956501657 / 2500000000000000 : ℝ)
    (cell12248 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · have h := gap_lower (n := 12248) (a := (8256095846753 / 10000000000000 : ℝ)) (b := (168252590453 / 100000000000000 : ℝ)) (q := (1155919326659 / 50000000000000 : ℝ))
      (E := (cell12248 ⟨44, by decide⟩).energy) (xi := (86681956501657 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12248 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12248]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12248])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12248) (a := (8256095846753 / 10000000000000 : ℝ)) (b := (168252590453 / 100000000000000 : ℝ)) (q := (1155919326659 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12248])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12248])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12248]

theorem cert12248_45 : CellCertificate 12248 (899765504210291 / 10000000000000000 : ℝ) (342989607531441 / 200000000000000000 : ℝ) (86681956501657 / 2500000000000000 : ℝ)
    (cell12248 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · have h := gap_lower (n := 12248) (a := (20631727133893 / 25000000000000 : ℝ)) (b := (168252590453 / 100000000000000 : ℝ)) (q := (92473704829 / 4000000000000 : ℝ))
      (E := (cell12248 ⟨45, by decide⟩).energy) (xi := (86681956501657 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12248 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12248]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12248])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12248) (a := (20631727133893 / 25000000000000 : ℝ)) (b := (168252590453 / 100000000000000 : ℝ)) (q := (92473704829 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12248])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12248])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12248]

theorem cert12248_46 : CellCertificate 12248 (899765504210291 / 10000000000000000 : ℝ) (342989607531441 / 200000000000000000 : ℝ) (86681956501657 / 2500000000000000 : ℝ)
    (cell12248 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · have h := gap_lower (n := 12248) (a := (41246441145769 / 50000000000000 : ℝ)) (b := (168252590453 / 100000000000000 : ℝ)) (q := (2311846623897 / 100000000000000 : ℝ))
      (E := (cell12248 ⟨46, by decide⟩).energy) (xi := (86681956501657 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12248 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12248]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12248])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12248) (a := (41246441145769 / 50000000000000 : ℝ)) (b := (168252590453 / 100000000000000 : ℝ)) (q := (2311846623897 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12248])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12248])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12248]

theorem cert12248_47 : CellCertificate 12248 (899765504210291 / 10000000000000000 : ℝ) (342989607531441 / 200000000000000000 : ℝ) (86681956501657 / 2500000000000000 : ℝ)
    (cell12248 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · have h := gap_lower (n := 12248) (a := (82458879705983 / 100000000000000 : ℝ)) (b := (168252590453 / 100000000000000 : ℝ)) (q := (1155925301527 / 50000000000000 : ℝ))
      (E := (cell12248 ⟨47, by decide⟩).energy) (xi := (86681956501657 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12248 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12248]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12248])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12248) (a := (82458879705983 / 100000000000000 : ℝ)) (b := (168252590453 / 100000000000000 : ℝ)) (q := (1155925301527 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12248])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12248])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12248]

theorem cert12248_48 : CellCertificate 12248 (899765504210291 / 10000000000000000 : ℝ) (342989607531441 / 200000000000000000 : ℝ) (86681956501657 / 2500000000000000 : ℝ)
    (cell12248 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · have h := gap_lower (n := 12248) (a := (16484980149923 / 20000000000000 : ℝ)) (b := (168252590453 / 100000000000000 : ℝ)) (q := (1155927307941 / 50000000000000 : ℝ))
      (E := (cell12248 ⟨48, by decide⟩).energy) (xi := (86681956501657 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12248 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12248]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12248])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12248) (a := (16484980149923 / 20000000000000 : ℝ)) (b := (168252590453 / 100000000000000 : ℝ)) (q := (1155927307941 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12248])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12248])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12248]

theorem cert12248_49 : CellCertificate 12248 (899765504210291 / 10000000000000000 : ℝ) (342989607531441 / 200000000000000000 : ℝ) (86681956501657 / 2500000000000000 : ℝ)
    (cell12248 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · have h := gap_lower (n := 12248) (a := (41195472696643 / 50000000000000 : ℝ)) (b := (168252590453 / 100000000000000 : ℝ)) (q := (2311858602119 / 100000000000000 : ℝ))
      (E := (cell12248 ⟨49, by decide⟩).energy) (xi := (86681956501657 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12248 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12248]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12248])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12248) (a := (41195472696643 / 50000000000000 : ℝ)) (b := (168252590453 / 100000000000000 : ℝ)) (q := (2311858602119 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12248])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12248])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12248]

theorem cert12248_50 : CellCertificate 12248 (899765504210291 / 10000000000000000 : ℝ) (342989607531441 / 200000000000000000 : ℝ) (86681956501657 / 2500000000000000 : ℝ)
    (cell12248 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · have h := gap_lower (n := 12248) (a := (20589253401999 / 25000000000000 : ℝ)) (b := (168252590453 / 100000000000000 : ℝ)) (q := (577965654767 / 25000000000000 : ℝ))
      (E := (cell12248 ⟨50, by decide⟩).energy) (xi := (86681956501657 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12248 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12248]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12248])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12248) (a := (20589253401999 / 25000000000000 : ℝ)) (b := (168252590453 / 100000000000000 : ℝ)) (q := (577965654767 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12248])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12248])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12248]

theorem cert12248_51 : CellCertificate 12248 (899765504210291 / 10000000000000000 : ℝ) (342989607531441 / 200000000000000000 : ℝ) (86681956501657 / 2500000000000000 : ℝ)
    (cell12248 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · have h := gap_lower (n := 12248) (a := (82323105364893 / 100000000000000 : ℝ)) (b := (168252590453 / 100000000000000 : ℝ)) (q := (2311866605987 / 100000000000000 : ℝ))
      (E := (cell12248 ⟨51, by decide⟩).energy) (xi := (86681956501657 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12248 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12248]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12248])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12248) (a := (82323105364893 / 100000000000000 : ℝ)) (b := (168252590453 / 100000000000000 : ℝ)) (q := (2311866605987 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12248])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12248])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12248]

theorem cert12248_52 : CellCertificate 12248 (899765504210291 / 10000000000000000 : ℝ) (342989607531441 / 200000000000000000 : ℝ) (86681956501657 / 2500000000000000 : ℝ)
    (cell12248 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · have h := gap_lower (n := 12248) (a := (41144610317633 / 50000000000000 : ℝ)) (b := (168252590453 / 100000000000000 : ℝ)) (q := (2311870619801 / 100000000000000 : ℝ))
      (E := (cell12248 ⟨52, by decide⟩).energy) (xi := (86681956501657 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12248 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12248]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12248])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12248) (a := (41144610317633 / 50000000000000 : ℝ)) (b := (168252590453 / 100000000000000 : ℝ)) (q := (2311870619801 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12248])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12248])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12248]

theorem cert12248_53 : CellCertificate 12248 (899765504210291 / 10000000000000000 : ℝ) (342989607531441 / 200000000000000000 : ℝ) (86681956501657 / 2500000000000000 : ℝ)
    (cell12248 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · have h := gap_lower (n := 12248) (a := (10281919923819 / 12500000000000 : ℝ)) (b := (168252590453 / 100000000000000 : ℝ)) (q := (2311874599293 / 100000000000000 : ℝ))
      (E := (cell12248 ⟨53, by decide⟩).energy) (xi := (86681956501657 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12248 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12248]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12248])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12248) (a := (10281919923819 / 12500000000000 : ℝ)) (b := (168252590453 / 100000000000000 : ℝ)) (q := (2311874599293 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12248])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12248])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12248]

theorem cert12248_54 : CellCertificate 12248 (899765504210291 / 10000000000000000 : ℝ) (342989607531441 / 200000000000000000 : ℝ) (86681956501657 / 2500000000000000 : ℝ)
    (cell12248 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · have h := gap_lower (n := 12248) (a := (82221521602329 / 100000000000000 : ℝ)) (b := (168252590453 / 100000000000000 : ℝ)) (q := (2311878601009 / 100000000000000 : ℝ))
      (E := (cell12248 ⟨54, by decide⟩).energy) (xi := (86681956501657 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12248 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12248]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12248])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12248) (a := (82221521602329 / 100000000000000 : ℝ)) (b := (168252590453 / 100000000000000 : ℝ)) (q := (2311878601009 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12248])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12248])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12248]

theorem cert12248_55 : CellCertificate 12248 (899765504210291 / 10000000000000000 : ℝ) (342989607531441 / 200000000000000000 : ℝ) (86681956501657 / 2500000000000000 : ℝ)
    (cell12248 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · have h := gap_lower (n := 12248) (a := (41093853621159 / 50000000000000 : ℝ)) (b := (168252590453 / 100000000000000 : ℝ)) (q := (462376512653 / 20000000000000 : ℝ))
      (E := (cell12248 ⟨55, by decide⟩).energy) (xi := (86681956501657 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12248 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12248]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12248])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12248) (a := (41093853621159 / 50000000000000 : ℝ)) (b := (168252590453 / 100000000000000 : ℝ)) (q := (462376512653 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12248])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12248])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12248]

theorem cert12248_56 : CellCertificate 12248 (899765504210291 / 10000000000000000 : ℝ) (342989607531441 / 200000000000000000 : ℝ) (86681956501657 / 2500000000000000 : ℝ)
    (cell12248 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · have h := gap_lower (n := 12248) (a := (41076958141191 / 50000000000000 : ℝ)) (b := (168252590453 / 100000000000000 : ℝ)) (q := (1155943300653 / 50000000000000 : ℝ))
      (E := (cell12248 ⟨56, by decide⟩).energy) (xi := (86681956501657 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12248 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12248]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12248])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12248) (a := (41076958141191 / 50000000000000 : ℝ)) (b := (168252590453 / 100000000000000 : ℝ)) (q := (1155943300653 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12248])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12248])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12248]

theorem cert12248_57 : CellCertificate 12248 (899765504210291 / 10000000000000000 : ℝ) (342989607531441 / 200000000000000000 : ℝ) (86681956501657 / 2500000000000000 : ℝ)
    (cell12248 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · have h := gap_lower (n := 12248) (a := (82120148694527 / 100000000000000 : ℝ)) (b := (168252590453 / 100000000000000 : ℝ)) (q := (2311890593949 / 100000000000000 : ℝ))
      (E := (cell12248 ⟨57, by decide⟩).energy) (xi := (86681956501657 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12248 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12248]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12248])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12248) (a := (82120148694527 / 100000000000000 : ℝ)) (b := (168252590453 / 100000000000000 : ℝ)) (q := (2311890593949 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12248])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12248])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12248]

theorem cert12248_58 : CellCertificate 12248 (899765504210291 / 10000000000000000 : ℝ) (342989607531441 / 200000000000000000 : ℝ) (86681956501657 / 2500000000000000 : ℝ)
    (cell12248 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · have h := gap_lower (n := 12248) (a := (41043202225447 / 50000000000000 : ℝ)) (b := (168252590453 / 100000000000000 : ℝ)) (q := (18061676539 / 781250000000 : ℝ))
      (E := (cell12248 ⟨58, by decide⟩).energy) (xi := (86681956501657 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12248 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12248]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12248])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12248) (a := (41043202225447 / 50000000000000 : ℝ)) (b := (168252590453 / 100000000000000 : ℝ)) (q := (18061676539 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12248])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12248])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12248]

theorem cert12248_59 : CellCertificate 12248 (899765504210291 / 10000000000000000 : ℝ) (342989607531441 / 200000000000000000 : ℝ) (86681956501657 / 2500000000000000 : ℝ)
    (cell12248 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · have h := gap_lower (n := 12248) (a := (82052683523769 / 100000000000000 : ℝ)) (b := (168252590453 / 100000000000000 : ℝ)) (q := (2311898547819 / 100000000000000 : ℝ))
      (E := (cell12248 ⟨59, by decide⟩).energy) (xi := (86681956501657 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12248 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12248]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12248])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12248) (a := (82052683523769 / 100000000000000 : ℝ)) (b := (168252590453 / 100000000000000 : ℝ)) (q := (2311898547819 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12248])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12248])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12248]

theorem cert12249_40 : CellCertificate 12249 (899735552680443 / 10000000000000000 : ℝ) (6698468682587 / 3906250000000000 : ℝ) (346698760194027 / 10000000000000000 : ℝ)
    (cell12249 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · have h := gap_lower (n := 12249) (a := (82697392576429 / 100000000000000 : ℝ)) (b := (10514916889 / 6250000000000 : ℝ)) (q := (462335054667 / 20000000000000 : ℝ))
      (E := (cell12249 ⟨40, by decide⟩).energy) (xi := (346698760194027 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12249 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12249]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12249])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12249) (a := (82697392576429 / 100000000000000 : ℝ)) (b := (10514916889 / 6250000000000 : ℝ)) (q := (462335054667 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12249])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12249])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12249]

theorem cert12249_41 : CellCertificate 12249 (899735552680443 / 10000000000000000 : ℝ) (6698468682587 / 3906250000000000 : ℝ) (346698760194027 / 10000000000000000 : ℝ)
    (cell12249 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · have h := gap_lower (n := 12249) (a := (661305983323 / 800000000000 : ℝ)) (b := (10514916889 / 6250000000000 : ℝ)) (q := (231167923527 / 10000000000000 : ℝ))
      (E := (cell12249 ⟨41, by decide⟩).energy) (xi := (346698760194027 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12249 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12249]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12249])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12249) (a := (661305983323 / 800000000000 : ℝ)) (b := (10514916889 / 6250000000000 : ℝ)) (q := (231167923527 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12249])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12249])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12249]

theorem cert12249_42 : CellCertificate 12249 (899735552680443 / 10000000000000000 : ℝ) (6698468682587 / 3906250000000000 : ℝ) (346698760194027 / 10000000000000000 : ℝ)
    (cell12249 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · have h := gap_lower (n := 12249) (a := (41314563530537 / 50000000000000 : ℝ)) (b := (10514916889 / 6250000000000 : ℝ)) (q := (2311683235307 / 100000000000000 : ℝ))
      (E := (cell12249 ⟨42, by decide⟩).energy) (xi := (346698760194027 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12249 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12249]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12249])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12249) (a := (41314563530537 / 50000000000000 : ℝ)) (b := (10514916889 / 6250000000000 : ℝ)) (q := (2311683235307 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12249])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12249])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12249]

theorem cert12249_43 : CellCertificate 12249 (899735552680443 / 10000000000000000 : ℝ) (6698468682587 / 3906250000000000 : ℝ) (346698760194027 / 10000000000000000 : ℝ)
    (cell12249 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · have h := gap_lower (n := 12249) (a := (41297514991741 / 50000000000000 : ℝ)) (b := (10514916889 / 6250000000000 : ℝ)) (q := (462337454681 / 20000000000000 : ℝ))
      (E := (cell12249 ⟨43, by decide⟩).energy) (xi := (346698760194027 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12249 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12249]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12249])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12249) (a := (41297514991741 / 50000000000000 : ℝ)) (b := (10514916889 / 6250000000000 : ℝ)) (q := (462337454681 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12249])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12249])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12249]

theorem cert12249_44 : CellCertificate 12249 (899735552680443 / 10000000000000000 : ℝ) (6698468682587 / 3906250000000000 : ℝ) (346698760194027 / 10000000000000000 : ℝ)
    (cell12249 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · have h := gap_lower (n := 12249) (a := (41280478326353 / 50000000000000 : ℝ)) (b := (10514916889 / 6250000000000 : ℝ)) (q := (1155845615857 / 50000000000000 : ℝ))
      (E := (cell12249 ⟨44, by decide⟩).energy) (xi := (346698760194027 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12249 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12249]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12249])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12249) (a := (41280478326353 / 50000000000000 : ℝ)) (b := (10514916889 / 6250000000000 : ℝ)) (q := (1155845615857 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12249])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12249])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12249]

theorem cert12249_45 : CellCertificate 12249 (899735552680443 / 10000000000000000 : ℝ) (6698468682587 / 3906250000000000 : ℝ) (346698760194027 / 10000000000000000 : ℝ)
    (cell12249 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · have h := gap_lower (n := 12249) (a := (20631726759751 / 25000000000000 : ℝ)) (b := (10514916889 / 6250000000000 : ℝ)) (q := (2311695227251 / 100000000000000 : ℝ))
      (E := (cell12249 ⟨45, by decide⟩).energy) (xi := (346698760194027 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12249 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12249]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12249])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12249) (a := (20631726759751 / 25000000000000 : ℝ)) (b := (10514916889 / 6250000000000 : ℝ)) (q := (2311695227251 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12249])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12249])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12249]

theorem cert12249_46 : CellCertificate 12249 (899735552680443 / 10000000000000000 : ℝ) (6698468682587 / 3906250000000000 : ℝ) (346698760194027 / 10000000000000000 : ℝ)
    (cell12249 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · have h := gap_lower (n := 12249) (a := (16498576222557 / 20000000000000 : ℝ)) (b := (10514916889 / 6250000000000 : ℝ)) (q := (2311699259317 / 100000000000000 : ℝ))
      (E := (cell12249 ⟨46, by decide⟩).energy) (xi := (346698760194027 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12249 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12249]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12249])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12249) (a := (16498576222557 / 20000000000000 : ℝ)) (b := (10514916889 / 6250000000000 : ℝ)) (q := (2311699259317 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12249])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12249])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12249]

theorem cert12249_47 : CellCertificate 12249 (899735552680443 / 10000000000000000 : ℝ) (6698468682587 / 3906250000000000 : ℝ) (346698760194027 / 10000000000000000 : ℝ)
    (cell12249 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · have h := gap_lower (n := 12249) (a := (82458878844607 / 100000000000000 : ℝ)) (b := (10514916889 / 6250000000000 : ℝ)) (q := (144481450579 / 6250000000000 : ℝ))
      (E := (cell12249 ⟨47, by decide⟩).energy) (xi := (346698760194027 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12249 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12249]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12249])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12249) (a := (82458878844607 / 100000000000000 : ℝ)) (b := (10514916889 / 6250000000000 : ℝ)) (q := (144481450579 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12249])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12249])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12249]

theorem cert12249_48 : CellCertificate 12249 (899735552680443 / 10000000000000000 : ℝ) (6698468682587 / 3906250000000000 : ℝ) (346698760194027 / 10000000000000000 : ℝ)
    (cell12249 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · have h := gap_lower (n := 12249) (a := (82424900205177 / 100000000000000 : ℝ)) (b := (10514916889 / 6250000000000 : ℝ)) (q := (462341450497 / 20000000000000 : ℝ))
      (E := (cell12249 ⟨48, by decide⟩).energy) (xi := (346698760194027 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12249 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12249]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12249])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12249) (a := (82424900205177 / 100000000000000 : ℝ)) (b := (10514916889 / 6250000000000 : ℝ)) (q := (462341450497 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12249])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12249])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12249]

theorem cert12249_49 : CellCertificate 12249 (899735552680443 / 10000000000000000 : ℝ) (6698468682587 / 3906250000000000 : ℝ) (346698760194027 / 10000000000000000 : ℝ)
    (cell12249 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · have h := gap_lower (n := 12249) (a := (20597736291337 / 25000000000000 : ℝ)) (b := (10514916889 / 6250000000000 : ℝ)) (q := (2311711210963 / 100000000000000 : ℝ))
      (E := (cell12249 ⟨49, by decide⟩).energy) (xi := (346698760194027 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12249 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12249]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12249])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12249) (a := (20597736291337 / 25000000000000 : ℝ)) (b := (10514916889 / 6250000000000 : ℝ)) (q := (2311711210963 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12249])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12249])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12249]

theorem cert12249_50 : CellCertificate 12249 (899735552680443 / 10000000000000000 : ℝ) (6698468682587 / 3906250000000000 : ℝ) (346698760194027 / 10000000000000000 : ℝ)
    (cell12249 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · have h := gap_lower (n := 12249) (a := (41178506848061 / 50000000000000 : ℝ)) (b := (10514916889 / 6250000000000 : ℝ)) (q := (72241100027 / 3125000000000 : ℝ))
      (E := (cell12249 ⟨50, by decide⟩).energy) (xi := (346698760194027 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12249 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12249]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12249])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12249) (a := (41178506848061 / 50000000000000 : ℝ)) (b := (10514916889 / 6250000000000 : ℝ)) (q := (72241100027 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12249])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12249])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12249]

theorem cert12249_51 : CellCertificate 12249 (899735552680443 / 10000000000000000 : ℝ) (6698468682587 / 3906250000000000 : ℝ) (346698760194027 / 10000000000000000 : ℝ)
    (cell12249 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · have h := gap_lower (n := 12249) (a := (41161552884323 / 50000000000000 : ℝ)) (b := (10514916889 / 6250000000000 : ℝ)) (q := (231171922041 / 10000000000000 : ℝ))
      (E := (cell12249 ⟨51, by decide⟩).energy) (xi := (346698760194027 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12249 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12249]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12249])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12249) (a := (41161552884323 / 50000000000000 : ℝ)) (b := (10514916889 / 6250000000000 : ℝ)) (q := (231171922041 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12249])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12249])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12249]

theorem cert12249_52 : CellCertificate 12249 (899735552680443 / 10000000000000000 : ℝ) (6698468682587 / 3906250000000000 : ℝ) (346698760194027 / 10000000000000000 : ℝ)
    (cell12249 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · have h := gap_lower (n := 12249) (a := (82289221354211 / 100000000000000 : ℝ)) (b := (10514916889 / 6250000000000 : ℝ)) (q := (144482700539 / 6250000000000 : ℝ))
      (E := (cell12249 ⟨52, by decide⟩).energy) (xi := (346698760194027 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12249 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12249]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12249])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12249) (a := (82289221354211 / 100000000000000 : ℝ)) (b := (10514916889 / 6250000000000 : ℝ)) (q := (144482700539 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12249])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12249])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12249]

theorem cert12249_53 : CellCertificate 12249 (899735552680443 / 10000000000000000 : ℝ) (6698468682587 / 3906250000000000 : ℝ) (346698760194027 / 10000000000000000 : ℝ)
    (cell12249 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · have h := gap_lower (n := 12249) (a := (82255360424253 / 100000000000000 : ℝ)) (b := (10514916889 / 6250000000000 : ℝ)) (q := (577931805559 / 25000000000000 : ℝ))
      (E := (cell12249 ⟨53, by decide⟩).energy) (xi := (346698760194027 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12249 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12249]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12249])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12249) (a := (82255360424253 / 100000000000000 : ℝ)) (b := (10514916889 / 6250000000000 : ℝ)) (q := (577931805559 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12249])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12249])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12249]

theorem cert12249_54 : CellCertificate 12249 (899735552680443 / 10000000000000000 : ℝ) (6698468682587 / 3906250000000000 : ℝ) (346698760194027 / 10000000000000000 : ℝ)
    (cell12249 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · have h := gap_lower (n := 12249) (a := (82221522950353 / 100000000000000 : ℝ)) (b := (10514916889 / 6250000000000 : ℝ)) (q := (2311731199797 / 100000000000000 : ℝ))
      (E := (cell12249 ⟨54, by decide⟩).energy) (xi := (346698760194027 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12249 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12249]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12249])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12249) (a := (82221522950353 / 100000000000000 : ℝ)) (b := (10514916889 / 6250000000000 : ℝ)) (q := (2311731199797 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12249])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12249])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12249]

theorem cert12249_55 : CellCertificate 12249 (899735552680443 / 10000000000000000 : ℝ) (6698468682587 / 3906250000000000 : ℝ) (346698760194027 / 10000000000000000 : ℝ)
    (cell12249 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · have h := gap_lower (n := 12249) (a := (10273463613029 / 12500000000000 : ℝ)) (b := (10514916889 / 6250000000000 : ℝ)) (q := (2311735197661 / 100000000000000 : ℝ))
      (E := (cell12249 ⟨55, by decide⟩).energy) (xi := (346698760194027 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12249 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12249]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12249])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12249) (a := (10273463613029 / 12500000000000 : ℝ)) (b := (10514916889 / 6250000000000 : ℝ)) (q := (2311735197661 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12249])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12249])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12249]

theorem cert12249_56 : CellCertificate 12249 (899735552680443 / 10000000000000000 : ℝ) (6698468682587 / 3906250000000000 : ℝ) (346698760194027 / 10000000000000000 : ℝ)
    (cell12249 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · have h := gap_lower (n := 12249) (a := (41076959128877 / 50000000000000 : ℝ)) (b := (10514916889 / 6250000000000 : ℝ)) (q := (2311739212989 / 100000000000000 : ℝ))
      (E := (cell12249 ⟨56, by decide⟩).energy) (xi := (346698760194027 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12249 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12249]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12249])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12249) (a := (41076959128877 / 50000000000000 : ℝ)) (b := (10514916889 / 6250000000000 : ℝ)) (q := (2311739212989 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12249])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12249])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12249]

theorem cert12249_57 : CellCertificate 12249 (899735552680443 / 10000000000000000 : ℝ) (6698468682587 / 3906250000000000 : ℝ) (346698760194027 / 10000000000000000 : ℝ)
    (cell12249 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · have h := gap_lower (n := 12249) (a := (82120150982923 / 100000000000000 : ℝ)) (b := (10514916889 / 6250000000000 : ℝ)) (q := (577935795907 / 25000000000000 : ℝ))
      (E := (cell12249 ⟨57, by decide⟩).energy) (xi := (346698760194027 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12249 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12249]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12249])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12249) (a := (82120150982923 / 100000000000000 : ℝ)) (b := (10514916889 / 6250000000000 : ℝ)) (q := (577935795907 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12249])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12249])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12249]

theorem cert12249_58 : CellCertificate 12249 (899735552680443 / 10000000000000000 : ℝ) (6698468682587 / 3906250000000000 : ℝ) (346698760194027 / 10000000000000000 : ℝ)
    (cell12249 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · have h := gap_lower (n := 12249) (a := (16417281410377 / 20000000000000 : ℝ)) (b := (10514916889 / 6250000000000 : ℝ)) (q := (1155873612249 / 50000000000000 : ℝ))
      (E := (cell12249 ⟨58, by decide⟩).energy) (xi := (346698760194027 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12249 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12249]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12249])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12249) (a := (16417281410377 / 20000000000000 : ℝ)) (b := (10514916889 / 6250000000000 : ℝ)) (q := (1155873612249 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12249])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12249])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12249]

theorem cert12249_59 : CellCertificate 12249 (899735552680443 / 10000000000000000 : ℝ) (6698468682587 / 3906250000000000 : ℝ) (346698760194027 / 10000000000000000 : ℝ)
    (cell12249 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · have h := gap_lower (n := 12249) (a := (20513171609231 / 25000000000000 : ℝ)) (b := (10514916889 / 6250000000000 : ℝ)) (q := (462350242781 / 20000000000000 : ℝ))
      (E := (cell12249 ⟨59, by decide⟩).energy) (xi := (346698760194027 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12249 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12249]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12249])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12249) (a := (20513171609231 / 25000000000000 : ℝ)) (b := (10514916889 / 6250000000000 : ℝ)) (q := (462350242781 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12249])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12249])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12249]

end BstLean.Part263
