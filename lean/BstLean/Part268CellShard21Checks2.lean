import BstLean.Part268CellShard21Checks1

/-! Twenty scalar cells per dimension in a 25-dimension shard. -/
namespace BstLean.Part268
open Real BstLean.Part263

theorem cert12875_40 : CellCertificate 12875 (220466354342377 / 2500000000000000 : ℝ) (1631404647345027 / 1000000000000000000 : ℝ) (329429106657121 / 10000000000000000 : ℝ)
    (cell12875 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · have h := gap_lower (n := 12875) (a := (4134782059153 / 5000000000000 : ℝ)) (b := (19994814457 / 12500000000000 : ℝ)) (q := (89225510663 / 4000000000000 : ℝ))
      (E := (cell12875 ⟨40, by decide⟩).energy) (xi := (329429106657121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12875 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12875]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12875])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12875) (a := (4134782059153 / 5000000000000 : ℝ)) (b := (19994814457 / 12500000000000 : ℝ)) (q := (89225510663 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12875])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12875])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12875]

theorem cert12875_41 : CellCertificate 12875 (220466354342377 / 2500000000000000 : ℝ) (1631404647345027 / 1000000000000000000 : ℝ) (329429106657121 / 10000000000000000 : ℝ)
    (cell12875 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · have h := gap_lower (n := 12875) (a := (41330844644631 / 50000000000000 : ℝ)) (b := (19994814457 / 12500000000000 : ℝ)) (q := (557660448473 / 25000000000000 : ℝ))
      (E := (cell12875 ⟨41, by decide⟩).energy) (xi := (329429106657121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12875 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12875]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12875])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12875) (a := (41330844644631 / 50000000000000 : ℝ)) (b := (19994814457 / 12500000000000 : ℝ)) (q := (557660448473 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12875])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12875])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12875]

theorem cert12875_42 : CellCertificate 12875 (220466354342377 / 2500000000000000 : ℝ) (1631404647345027 / 1000000000000000000 : ℝ) (329429106657121 / 10000000000000000 : ℝ)
    (cell12875 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · have h := gap_lower (n := 12875) (a := (82627760935909 / 100000000000000 : ℝ)) (b := (19994814457 / 12500000000000 : ℝ)) (q := (223064577619 / 10000000000000 : ℝ))
      (E := (cell12875 ⟨42, by decide⟩).energy) (xi := (329429106657121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12875 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12875]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12875])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12875) (a := (82627760935909 / 100000000000000 : ℝ)) (b := (19994814457 / 12500000000000 : ℝ)) (q := (223064577619 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12875])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12875])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12875]

theorem cert12875_43 : CellCertificate 12875 (220466354342377 / 2500000000000000 : ℝ) (1631404647345027 / 1000000000000000000 : ℝ) (329429106657121 / 10000000000000000 : ℝ)
    (cell12875 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · have h := gap_lower (n := 12875) (a := (64526450073 / 78125000000 : ℝ)) (b := (19994814457 / 12500000000000 : ℝ)) (q := (446129954233 / 20000000000000 : ℝ))
      (E := (cell12875 ⟨43, by decide⟩).energy) (xi := (329429106657121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12875 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12875]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12875])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12875) (a := (64526450073 / 78125000000 : ℝ)) (b := (19994814457 / 12500000000000 : ℝ)) (q := (446129954233 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12875])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12875])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12875]

theorem cert12875_44 : CellCertificate 12875 (220466354342377 / 2500000000000000 : ℝ) (1631404647345027 / 1000000000000000000 : ℝ) (329429106657121 / 10000000000000000 : ℝ)
    (cell12875 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · have h := gap_lower (n := 12875) (a := (20639993683111 / 25000000000000 : ℝ)) (b := (19994814457 / 12500000000000 : ℝ)) (q := (446130755507 / 20000000000000 : ℝ))
      (E := (cell12875 ⟨44, by decide⟩).energy) (xi := (329429106657121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12875 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12875]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12875])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12875) (a := (20639993683111 / 25000000000000 : ℝ)) (b := (19994814457 / 12500000000000 : ℝ)) (q := (446130755507 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12875])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12875])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12875]

theorem cert12875_45 : CellCertificate 12875 (220466354342377 / 2500000000000000 : ℝ) (1631404647345027 / 1000000000000000000 : ℝ) (329429106657121 / 10000000000000000 : ℝ)
    (cell12875 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · have h := gap_lower (n := 12875) (a := (82526116823657 / 100000000000000 : ℝ)) (b := (19994814457 / 12500000000000 : ℝ)) (q := (1115328896899 / 50000000000000 : ℝ))
      (E := (cell12875 ⟨45, by decide⟩).energy) (xi := (329429106657121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12875 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12875]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12875])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12875) (a := (82526116823657 / 100000000000000 : ℝ)) (b := (19994814457 / 12500000000000 : ℝ)) (q := (1115328896899 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12875])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12875])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12875]

theorem cert12875_46 : CellCertificate 12875 (220466354342377 / 2500000000000000 : ℝ) (1631404647345027 / 1000000000000000000 : ℝ) (329429106657121 / 10000000000000000 : ℝ)
    (cell12875 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · have h := gap_lower (n := 12875) (a := (20623070584491 / 25000000000000 : ℝ)) (b := (19994814457 / 12500000000000 : ℝ)) (q := (2230661818237 / 100000000000000 : ℝ))
      (E := (cell12875 ⟨46, by decide⟩).energy) (xi := (329429106657121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12875 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12875]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12875])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12875) (a := (20623070584491 / 25000000000000 : ℝ)) (b := (19994814457 / 12500000000000 : ℝ)) (q := (2230661818237 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12875])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12875])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12875]

theorem cert12875_47 : CellCertificate 12875 (220466354342377 / 2500000000000000 : ℝ) (1631404647345027 / 1000000000000000000 : ℝ) (329429106657121 / 10000000000000000 : ℝ)
    (cell12875 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · have h := gap_lower (n := 12875) (a := (41229235623197 / 50000000000000 : ℝ)) (b := (19994814457 / 12500000000000 : ℝ)) (q := (1115332894997 / 50000000000000 : ℝ))
      (E := (cell12875 ⟨47, by decide⟩).energy) (xi := (329429106657121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12875 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12875]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12875])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12875) (a := (41229235623197 / 50000000000000 : ℝ)) (b := (19994814457 / 12500000000000 : ℝ)) (q := (1115332894997 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12875])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12875])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12875]

theorem cert12875_48 : CellCertificate 12875 (220466354342377 / 2500000000000000 : ℝ) (1631404647345027 / 1000000000000000000 : ℝ) (329429106657121 / 10000000000000000 : ℝ)
    (cell12875 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · have h := gap_lower (n := 12875) (a := (82424683520123 / 100000000000000 : ℝ)) (b := (19994814457 / 12500000000000 : ℝ)) (q := (2230669824757 / 100000000000000 : ℝ))
      (E := (cell12875 ⟨48, by decide⟩).energy) (xi := (329429106657121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12875 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12875]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12875])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12875) (a := (82424683520123 / 100000000000000 : ℝ)) (b := (19994814457 / 12500000000000 : ℝ)) (q := (2230669824757 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12875])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12875])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12875]

theorem cert12875_49 : CellCertificate 12875 (220466354342377 / 2500000000000000 : ℝ) (1631404647345027 / 1000000000000000000 : ℝ) (329429106657121 / 10000000000000000 : ℝ)
    (cell12875 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · have h := gap_lower (n := 12875) (a := (8239091913047 / 10000000000000 : ℝ)) (b := (19994814457 / 12500000000000 : ℝ)) (q := (2230673802287 / 100000000000000 : ℝ))
      (E := (cell12875 ⟨49, by decide⟩).energy) (xi := (329429106657121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12875 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12875]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12875])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12875) (a := (8239091913047 / 10000000000000 : ℝ)) (b := (19994814457 / 12500000000000 : ℝ)) (q := (2230673802287 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12875])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12875])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12875]

theorem cert12875_50 : CellCertificate 12875 (220466354342377 / 2500000000000000 : ℝ) (1631404647345027 / 1000000000000000000 : ℝ) (329429106657121 / 10000000000000000 : ℝ)
    (cell12875 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · have h := gap_lower (n := 12875) (a := (82357178048899 / 100000000000000 : ℝ)) (b := (19994814457 / 12500000000000 : ℝ)) (q := (2230677837941 / 100000000000000 : ℝ))
      (E := (cell12875 ⟨50, by decide⟩).energy) (xi := (329429106657121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12875 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12875]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12875])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12875) (a := (82357178048899 / 100000000000000 : ℝ)) (b := (19994814457 / 12500000000000 : ℝ)) (q := (2230677837941 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12875])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12875])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12875]

theorem cert12875_51 : CellCertificate 12875 (220466354342377 / 2500000000000000 : ℝ) (1631404647345027 / 1000000000000000000 : ℝ) (329429106657121 / 10000000000000000 : ℝ)
    (cell12875 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · have h := gap_lower (n := 12875) (a := (16464692049403 / 20000000000000 : ℝ)) (b := (19994814457 / 12500000000000 : ℝ)) (q := (1115340934993 / 50000000000000 : ℝ))
      (E := (cell12875 ⟨51, by decide⟩).energy) (xi := (329429106657121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12875 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12875]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12875])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12875) (a := (16464692049403 / 20000000000000 : ℝ)) (b := (19994814457 / 12500000000000 : ℝ)) (q := (1115340934993 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12875])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12875])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12875]

theorem cert12875_52 : CellCertificate 12875 (220466354342377 / 2500000000000000 : ℝ) (1631404647345027 / 1000000000000000000 : ℝ) (329429106657121 / 10000000000000000 : ℝ)
    (cell12875 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · have h := gap_lower (n := 12875) (a := (10286220712071 / 12500000000000 : ℝ)) (b := (19994814457 / 12500000000000 : ℝ)) (q := (2230685836381 / 100000000000000 : ℝ))
      (E := (cell12875 ⟨52, by decide⟩).energy) (xi := (329429106657121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12875 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12875]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12875])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12875) (a := (10286220712071 / 12500000000000 : ℝ)) (b := (19994814457 / 12500000000000 : ℝ)) (q := (2230685836381 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12875])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12875])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12875]

theorem cert12875_53 : CellCertificate 12875 (220466354342377 / 2500000000000000 : ℝ) (1631404647345027 / 1000000000000000000 : ℝ) (329429106657121 / 10000000000000000 : ℝ)
    (cell12875 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · have h := gap_lower (n := 12875) (a := (16451218873889 / 20000000000000 : ℝ)) (b := (19994814457 / 12500000000000 : ℝ)) (q := (1115344925997 / 50000000000000 : ℝ))
      (E := (cell12875 ⟨53, by decide⟩).energy) (xi := (329429106657121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12875 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12875]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12875])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12875) (a := (16451218873889 / 20000000000000 : ℝ)) (b := (19994814457 / 12500000000000 : ℝ)) (q := (1115344925997 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12875])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12875])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12875]

theorem cert12875_54 : CellCertificate 12875 (220466354342377 / 2500000000000000 : ℝ) (1631404647345027 / 1000000000000000000 : ℝ) (329429106657121 / 10000000000000000 : ℝ)
    (cell12875 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · have h := gap_lower (n := 12875) (a := (82222446237677 / 100000000000000 : ℝ)) (b := (19994814457 / 12500000000000 : ℝ)) (q := (557673463597 / 25000000000000 : ℝ))
      (E := (cell12875 ⟨54, by decide⟩).energy) (xi := (329429106657121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12875 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12875]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12875])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12875) (a := (82222446237677 / 100000000000000 : ℝ)) (b := (19994814457 / 12500000000000 : ℝ)) (q := (557673463597 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12875])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12875])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12875]

theorem cert12875_55 : CellCertificate 12875 (220466354342377 / 2500000000000000 : ℝ) (1631404647345027 / 1000000000000000000 : ℝ) (329429106657121 / 10000000000000000 : ℝ)
    (cell12875 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · have h := gap_lower (n := 12875) (a := (82188821273433 / 100000000000000 : ℝ)) (b := (19994814457 / 12500000000000 : ℝ)) (q := (2230697899059 / 100000000000000 : ℝ))
      (E := (cell12875 ⟨55, by decide⟩).energy) (xi := (329429106657121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12875 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12875]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12875])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12875) (a := (82188821273433 / 100000000000000 : ℝ)) (b := (19994814457 / 12500000000000 : ℝ)) (q := (2230697899059 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12875])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12875])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12875]

theorem cert12875_56 : CellCertificate 12875 (220466354342377 / 2500000000000000 : ℝ) (1631404647345027 / 1000000000000000000 : ℝ) (329429106657121 / 10000000000000000 : ℝ)
    (cell12875 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · have h := gap_lower (n := 12875) (a := (4107760972451 / 5000000000000 : ℝ)) (b := (19994814457 / 12500000000000 : ℝ)) (q := (223070186397 / 10000000000000 : ℝ))
      (E := (cell12875 ⟨56, by decide⟩).energy) (xi := (329429106657121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12875 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12875]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12875])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12875) (a := (4107760972451 / 5000000000000 : ℝ)) (b := (19994814457 / 12500000000000 : ℝ)) (q := (223070186397 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12875])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12875])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12875]

theorem cert12875_57 : CellCertificate 12875 (220466354342377 / 2500000000000000 : ℝ) (1631404647345027 / 1000000000000000000 : ℝ) (329429106657121 / 10000000000000000 : ℝ)
    (cell12875 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · have h := gap_lower (n := 12875) (a := (16424328147377 / 20000000000000 : ℝ)) (b := (19994814457 / 12500000000000 : ℝ)) (q := (278838240313 / 12500000000000 : ℝ))
      (E := (cell12875 ⟨57, by decide⟩).energy) (xi := (329429106657121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12875 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12875]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12875])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12875) (a := (16424328147377 / 20000000000000 : ℝ)) (b := (19994814457 / 12500000000000 : ℝ)) (q := (278838240313 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12875])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12875])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12875]

theorem cert12875_58 : CellCertificate 12875 (220466354342377 / 2500000000000000 : ℝ) (1631404647345027 / 1000000000000000000 : ℝ) (329429106657121 / 10000000000000000 : ℝ)
    (cell12875 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · have h := gap_lower (n := 12875) (a := (8208808510961 / 10000000000000 : ℝ)) (b := (19994814457 / 12500000000000 : ℝ)) (q := (2230709893 / 100000000000 : ℝ))
      (E := (cell12875 ⟨58, by decide⟩).energy) (xi := (329429106657121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12875 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12875]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12875])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12875) (a := (8208808510961 / 10000000000000 : ℝ)) (b := (19994814457 / 12500000000000 : ℝ)) (q := (2230709893 / 100000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12875])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12875])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12875]

theorem cert12875_59 : CellCertificate 12875 (220466354342377 / 2500000000000000 : ℝ) (1631404647345027 / 1000000000000000000 : ℝ) (329429106657121 / 10000000000000000 : ℝ)
    (cell12875 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · have h := gap_lower (n := 12875) (a := (41027276269957 / 50000000000000 : ℝ)) (b := (19994814457 / 12500000000000 : ℝ)) (q := (2230713889361 / 100000000000000 : ℝ))
      (E := (cell12875 ⟨59, by decide⟩).energy) (xi := (329429106657121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12875 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12875]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12875])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12875) (a := (41027276269957 / 50000000000000 : ℝ)) (b := (19994814457 / 12500000000000 : ℝ)) (q := (2230713889361 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12875])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12875])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12875]

theorem cert12876_40 : CellCertificate 12876 (44091910340159 / 500000000000000 : ℝ) (1631277905056399 / 1000000000000000000 : ℝ) (2058768220959 / 62500000000000 : ℝ)
    (cell12876 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · have h := gap_lower (n := 12876) (a := (5168477416369 / 6250000000000 : ℝ)) (b := (39986486349 / 25000000000000 : ℝ)) (q := (446104080807 / 20000000000000 : ℝ))
      (E := (cell12876 ⟨40, by decide⟩).energy) (xi := (2058768220959 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12876 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12876]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12876])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12876) (a := (5168477416369 / 6250000000000 : ℝ)) (b := (39986486349 / 25000000000000 : ℝ)) (q := (446104080807 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12876])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12876])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12876]

theorem cert12876_41 : CellCertificate 12876 (44091910340159 / 500000000000000 : ℝ) (1631277905056399 / 1000000000000000000 : ℝ) (2058768220959 / 62500000000000 : ℝ)
    (cell12876 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · have h := gap_lower (n := 12876) (a := (10332710883057 / 12500000000000 : ℝ)) (b := (39986486349 / 25000000000000 : ℝ)) (q := (278815547009 / 12500000000000 : ℝ))
      (E := (cell12876 ⟨41, by decide⟩).energy) (xi := (2058768220959 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12876 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12876]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12876])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12876) (a := (10332710883057 / 12500000000000 : ℝ)) (b := (39986486349 / 25000000000000 : ℝ)) (q := (278815547009 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12876])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12876])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12876]

theorem cert12876_42 : CellCertificate 12876 (44091910340159 / 500000000000000 : ℝ) (1631277905056399 / 1000000000000000000 : ℝ) (2058768220959 / 62500000000000 : ℝ)
    (cell12876 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · have h := gap_lower (n := 12876) (a := (20656939751761 / 25000000000000 : ℝ)) (b := (39986486349 / 25000000000000 : ℝ)) (q := (2230528362537 / 100000000000000 : ℝ))
      (E := (cell12876 ⟨42, by decide⟩).energy) (xi := (2058768220959 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12876 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12876]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12876])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12876) (a := (20656939751761 / 25000000000000 : ℝ)) (b := (39986486349 / 25000000000000 : ℝ)) (q := (2230528362537 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12876])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12876])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12876]

theorem cert12876_43 : CellCertificate 12876 (44091910340159 / 500000000000000 : ℝ) (1631277905056399 / 1000000000000000000 : ℝ) (2058768220959 / 62500000000000 : ℝ)
    (cell12876 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · have h := gap_lower (n := 12876) (a := (20648463615027 / 25000000000000 : ℝ)) (b := (39986486349 / 25000000000000 : ℝ)) (q := (5576331053 / 250000000000 : ℝ))
      (E := (cell12876 ⟨43, by decide⟩).energy) (xi := (2058768220959 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12876 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12876]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12876])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12876) (a := (20648463615027 / 25000000000000 : ℝ)) (b := (39986486349 / 25000000000000 : ℝ)) (q := (5576331053 / 250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12876])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12876])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12876]

theorem cert12876_44 : CellCertificate 12876 (44091910340159 / 500000000000000 : ℝ) (1631277905056399 / 1000000000000000000 : ℝ) (2058768220959 / 62500000000000 : ℝ)
    (cell12876 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · have h := gap_lower (n := 12876) (a := (82559973394239 / 100000000000000 : ℝ)) (b := (39986486349 / 25000000000000 : ℝ)) (q := (2230536433127 / 100000000000000 : ℝ))
      (E := (cell12876 ⟨44, by decide⟩).energy) (xi := (2058768220959 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12876 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12876]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12876])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12876) (a := (82559973394239 / 100000000000000 : ℝ)) (b := (39986486349 / 25000000000000 : ℝ)) (q := (2230536433127 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12876])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12876])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12876]

theorem cert12876_45 : CellCertificate 12876 (44091910340159 / 500000000000000 : ℝ) (1631277905056399 / 1000000000000000000 : ℝ) (2058768220959 / 62500000000000 : ℝ)
    (cell12876 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · have h := gap_lower (n := 12876) (a := (82526115780173 / 100000000000000 : ℝ)) (b := (39986486349 / 25000000000000 : ℝ)) (q := (557635099187 / 25000000000000 : ℝ))
      (E := (cell12876 ⟨45, by decide⟩).energy) (xi := (2058768220959 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12876 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12876]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12876])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12876) (a := (82526115780173 / 100000000000000 : ℝ)) (b := (39986486349 / 25000000000000 : ℝ)) (q := (557635099187 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12876])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12876])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12876]

theorem cert12876_46 : CellCertificate 12876 (44091910340159 / 500000000000000 : ℝ) (1631277905056399 / 1000000000000000000 : ℝ) (2058768220959 / 62500000000000 : ℝ)
    (cell12876 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · have h := gap_lower (n := 12876) (a := (16498456317759 / 20000000000000 : ℝ)) (b := (39986486349 / 25000000000000 : ℝ)) (q := (1115272214043 / 50000000000000 : ℝ))
      (E := (cell12876 ⟨46, by decide⟩).energy) (xi := (2058768220959 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12876 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12876]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12876])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12876) (a := (16498456317759 / 20000000000000 : ℝ)) (b := (39986486349 / 25000000000000 : ℝ)) (q := (1115272214043 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12876])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12876])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12876]

theorem cert12876_47 : CellCertificate 12876 (44091910340159 / 500000000000000 : ℝ) (1631277905056399 / 1000000000000000000 : ℝ) (2058768220959 / 62500000000000 : ℝ)
    (cell12876 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · have h := gap_lower (n := 12876) (a := (2576827212223 / 3125000000000 : ℝ)) (b := (39986486349 / 25000000000000 : ℝ)) (q := (1115274203711 / 50000000000000 : ℝ))
      (E := (cell12876 ⟨47, by decide⟩).energy) (xi := (2058768220959 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12876 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12876]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12876])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12876) (a := (2576827212223 / 3125000000000 : ℝ)) (b := (39986486349 / 25000000000000 : ℝ)) (q := (1115274203711 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12876])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12876])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12876]

theorem cert12876_48 : CellCertificate 12876 (44091910340159 / 500000000000000 : ℝ) (1631277905056399 / 1000000000000000000 : ℝ) (2058768220959 / 62500000000000 : ℝ)
    (cell12876 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · have h := gap_lower (n := 12876) (a := (82424683358371 / 100000000000000 : ℝ)) (b := (39986486349 / 25000000000000 : ℝ)) (q := (557638112611 / 25000000000000 : ℝ))
      (E := (cell12876 ⟨48, by decide⟩).energy) (xi := (2058768220959 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12876 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12876]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12876])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12876) (a := (82424683358371 / 100000000000000 : ℝ)) (b := (39986486349 / 25000000000000 : ℝ)) (q := (557638112611 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12876])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12876])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12876]

theorem cert12876_49 : CellCertificate 12876 (44091910340159 / 500000000000000 : ℝ) (1631277905056399 / 1000000000000000000 : ℝ) (2058768220959 / 62500000000000 : ℝ)
    (cell12876 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · have h := gap_lower (n := 12876) (a := (41195459630911 / 50000000000000 : ℝ)) (b := (39986486349 / 25000000000000 : ℝ)) (q := (2230556436913 / 100000000000000 : ℝ))
      (E := (cell12876 ⟨49, by decide⟩).energy) (xi := (2058768220959 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12876 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12876]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12876])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12876) (a := (41195459630911 / 50000000000000 : ℝ)) (b := (39986486349 / 25000000000000 : ℝ)) (q := (2230556436913 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12876])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12876])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12876]

theorem cert12876_50 : CellCertificate 12876 (44091910340159 / 500000000000000 : ℝ) (1631277905056399 / 1000000000000000000 : ℝ) (2058768220959 / 62500000000000 : ℝ)
    (cell12876 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · have h := gap_lower (n := 12876) (a := (82357178472951 / 100000000000000 : ℝ)) (b := (39986486349 / 25000000000000 : ℝ)) (q := (2230560423187 / 100000000000000 : ℝ))
      (E := (cell12876 ⟨50, by decide⟩).energy) (xi := (2058768220959 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12876 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12876]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12876])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12876) (a := (82357178472951 / 100000000000000 : ℝ)) (b := (39986486349 / 25000000000000 : ℝ)) (q := (2230560423187 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12876])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12876])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12876]

theorem cert12876_51 : CellCertificate 12876 (44091910340159 / 500000000000000 : ℝ) (1631277905056399 / 1000000000000000000 : ℝ) (2058768220959 / 62500000000000 : ℝ)
    (cell12876 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · have h := gap_lower (n := 12876) (a := (82323460963367 / 100000000000000 : ℝ)) (b := (39986486349 / 25000000000000 : ℝ)) (q := (2230564465503 / 100000000000000 : ℝ))
      (E := (cell12876 ⟨51, by decide⟩).energy) (xi := (2058768220959 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12876 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12876]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12876])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12876) (a := (82323460963367 / 100000000000000 : ℝ)) (b := (39986486349 / 25000000000000 : ℝ)) (q := (2230564465503 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12876])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12876])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12876]

theorem cert12876_52 : CellCertificate 12876 (44091910340159 / 500000000000000 : ℝ) (1631277905056399 / 1000000000000000000 : ℝ) (2058768220959 / 62500000000000 : ℝ)
    (cell12876 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · have h := gap_lower (n := 12876) (a := (82289766704817 / 100000000000000 : ℝ)) (b := (39986486349 / 25000000000000 : ℝ)) (q := (2230568442849 / 100000000000000 : ℝ))
      (E := (cell12876 ⟨52, by decide⟩).energy) (xi := (2058768220959 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12876 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12876]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12876])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12876) (a := (82289766704817 / 100000000000000 : ℝ)) (b := (39986486349 / 25000000000000 : ℝ)) (q := (2230568442849 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12876])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12876])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12876]

theorem cert12876_53 : CellCertificate 12876 (44091910340159 / 500000000000000 : ℝ) (1631277905056399 / 1000000000000000000 : ℝ) (2058768220959 / 62500000000000 : ℝ)
    (cell12876 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · have h := gap_lower (n := 12876) (a := (10282011958649 / 12500000000000 : ℝ)) (b := (39986486349 / 25000000000000 : ℝ)) (q := (2230572470087 / 100000000000000 : ℝ))
      (E := (cell12876 ⟨53, by decide⟩).energy) (xi := (2058768220959 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12876 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12876]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12876])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12876) (a := (10282011958649 / 12500000000000 : ℝ)) (b := (39986486349 / 25000000000000 : ℝ)) (q := (2230572470087 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12876])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12876])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12876]

theorem cert12876_54 : CellCertificate 12876 (44091910340159 / 500000000000000 : ℝ) (1631277905056399 / 1000000000000000000 : ℝ) (2058768220959 / 62500000000000 : ℝ)
    (cell12876 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · have h := gap_lower (n := 12876) (a := (41111223914261 / 50000000000000 : ℝ)) (b := (39986486349 / 25000000000000 : ℝ)) (q := (139411030299 / 6250000000000 : ℝ))
      (E := (cell12876 ⟨54, by decide⟩).energy) (xi := (2058768220959 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12876 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12876]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12876])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12876) (a := (41111223914261 / 50000000000000 : ℝ)) (b := (39986486349 / 25000000000000 : ℝ)) (q := (139411030299 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12876])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12876])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12876]

theorem cert12876_55 : CellCertificate 12876 (44091910340159 / 500000000000000 : ℝ) (1631277905056399 / 1000000000000000000 : ℝ) (2058768220959 / 62500000000000 : ℝ)
    (cell12876 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · have h := gap_lower (n := 12876) (a := (82188823154977 / 100000000000000 : ℝ)) (b := (39986486349 / 25000000000000 : ℝ)) (q := (557645120829 / 25000000000000 : ℝ))
      (E := (cell12876 ⟨55, by decide⟩).energy) (xi := (2058768220959 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12876 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12876]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12876])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12876) (a := (82188823154977 / 100000000000000 : ℝ)) (b := (39986486349 / 25000000000000 : ℝ)) (q := (557645120829 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12876])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12876])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12876]

theorem cert12876_56 : CellCertificate 12876 (44091910340159 / 500000000000000 : ℝ) (1631277905056399 / 1000000000000000000 : ℝ) (2058768220959 / 62500000000000 : ℝ)
    (cell12876 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · have h := gap_lower (n := 12876) (a := (16431044324173 / 20000000000000 : ℝ)) (b := (39986486349 / 25000000000000 : ℝ)) (q := (557646130249 / 25000000000000 : ℝ))
      (E := (cell12876 ⟨56, by decide⟩).energy) (xi := (2058768220959 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12876 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12876]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12876])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12876) (a := (16431044324173 / 20000000000000 : ℝ)) (b := (39986486349 / 25000000000000 : ℝ)) (q := (557646130249 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12876])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12876])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12876]

theorem cert12876_57 : CellCertificate 12876 (44091910340159 / 500000000000000 : ℝ) (1631277905056399 / 1000000000000000000 : ℝ) (2058768220959 / 62500000000000 : ℝ)
    (cell12876 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · have h := gap_lower (n := 12876) (a := (10265205399829 / 12500000000000 : ℝ)) (b := (39986486349 / 25000000000000 : ℝ)) (q := (1115294267347 / 50000000000000 : ℝ))
      (E := (cell12876 ⟨57, by decide⟩).energy) (xi := (2058768220959 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12876 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12876]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12876])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12876) (a := (10265205399829 / 12500000000000 : ℝ)) (b := (39986486349 / 25000000000000 : ℝ)) (q := (1115294267347 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12876])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12876])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12876]

theorem cert12876_58 : CellCertificate 12876 (44091910340159 / 500000000000000 : ℝ) (1631277905056399 / 1000000000000000000 : ℝ) (2058768220959 / 62500000000000 : ℝ)
    (cell12876 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · have h := gap_lower (n := 12876) (a := (82088087860863 / 100000000000000 : ℝ)) (b := (39986486349 / 25000000000000 : ℝ)) (q := (2230592520167 / 100000000000000 : ℝ))
      (E := (cell12876 ⟨58, by decide⟩).energy) (xi := (2058768220959 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12876 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12876]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12876])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12876) (a := (82088087860863 / 100000000000000 : ℝ)) (b := (39986486349 / 25000000000000 : ℝ)) (q := (2230592520167 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12876])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12876])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12876]

theorem cert12876_59 : CellCertificate 12876 (44091910340159 / 500000000000000 : ℝ) (1631277905056399 / 1000000000000000000 : ℝ) (2058768220959 / 62500000000000 : ℝ)
    (cell12876 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · have h := gap_lower (n := 12876) (a := (20513638895069 / 25000000000000 : ℝ)) (b := (39986486349 / 25000000000000 : ℝ)) (q := (1115298266089 / 50000000000000 : ℝ))
      (E := (cell12876 ⟨59, by decide⟩).energy) (xi := (2058768220959 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12876 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12876]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12876])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12876) (a := (20513638895069 / 25000000000000 : ℝ)) (b := (39986486349 / 25000000000000 : ℝ)) (q := (1115298266089 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12876])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12876])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12876]

theorem cert12877_40 : CellCertificate 12877 (88181100028921 / 1000000000000000 : ℝ) (815575591229609 / 500000000000000000 : ℝ) (65875345651643 / 2000000000000000 : ℝ)
    (cell12877 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · have h := gap_lower (n := 12877) (a := (82695636141577 / 100000000000000 : ℝ)) (b := (79966688561 / 50000000000000 : ℝ)) (q := (1115201519237 / 50000000000000 : ℝ))
      (E := (cell12877 ⟨40, by decide⟩).energy) (xi := (65875345651643 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12877 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12877]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12877])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12877) (a := (82695636141577 / 100000000000000 : ℝ)) (b := (79966688561 / 50000000000000 : ℝ)) (q := (1115201519237 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12877])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12877])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12877]

theorem cert12877_41 : CellCertificate 12877 (88181100028921 / 1000000000000000 : ℝ) (815575591229609 / 500000000000000000 : ℝ) (65875345651643 / 2000000000000000 : ℝ)
    (cell12877 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · have h := gap_lower (n := 12877) (a := (82661684840443 / 100000000000000 : ℝ)) (b := (79966688561 / 50000000000000 : ℝ)) (q := (1115203507027 / 50000000000000 : ℝ))
      (E := (cell12877 ⟨41, by decide⟩).energy) (xi := (65875345651643 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12877 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12877]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12877])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12877) (a := (82661684840443 / 100000000000000 : ℝ)) (b := (79966688561 / 50000000000000 : ℝ)) (q := (1115203507027 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12877])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12877])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12877]

theorem cert12877_42 : CellCertificate 12877 (88181100028921 / 1000000000000000 : ℝ) (815575591229609 / 500000000000000000 : ℝ) (65875345651643 / 2000000000000000 : ℝ)
    (cell12877 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · have h := gap_lower (n := 12877) (a := (10328469634867 / 12500000000000 : ℝ)) (b := (79966688561 / 50000000000000 : ℝ)) (q := (557602751187 / 25000000000000 : ℝ))
      (E := (cell12877 ⟨42, by decide⟩).energy) (xi := (65875345651643 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12877 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12877]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12877])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12877) (a := (10328469634867 / 12500000000000 : ℝ)) (b := (79966688561 / 50000000000000 : ℝ)) (q := (557602751187 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12877])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12877])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12877]

theorem cert12877_43 : CellCertificate 12877 (88181100028921 / 1000000000000000 : ℝ) (815575591229609 / 500000000000000000 : ℝ) (65875345651643 / 2000000000000000 : ℝ)
    (cell12877 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · have h := gap_lower (n := 12877) (a := (82593852827499 / 100000000000000 : ℝ)) (b := (79966688561 / 50000000000000 : ℝ)) (q := (2230415068321 / 100000000000000 : ℝ))
      (E := (cell12877 ⟨43, by decide⟩).energy) (xi := (65875345651643 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12877 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12877]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12877])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12877) (a := (82593852827499 / 100000000000000 : ℝ)) (b := (79966688561 / 50000000000000 : ℝ)) (q := (2230415068321 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12877])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12877])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12877]

theorem cert12877_44 : CellCertificate 12877 (88181100028921 / 1000000000000000 : ℝ) (815575591229609 / 500000000000000000 : ℝ) (65875345651643 / 2000000000000000 : ℝ)
    (cell12877 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · have h := gap_lower (n := 12877) (a := (82559972056721 / 100000000000000 : ℝ)) (b := (79966688561 / 50000000000000 : ℝ)) (q := (446083805397 / 20000000000000 : ℝ))
      (E := (cell12877 ⟨44, by decide⟩).energy) (xi := (65875345651643 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12877 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12877]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12877])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12877) (a := (82559972056721 / 100000000000000 : ℝ)) (b := (79966688561 / 50000000000000 : ℝ)) (q := (446083805397 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12877])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12877])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12877]

theorem cert12877_45 : CellCertificate 12877 (88181100028921 / 1000000000000000 : ℝ) (815575591229609 / 500000000000000000 : ℝ) (65875345651643 / 2000000000000000 : ℝ)
    (cell12877 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · have h := gap_lower (n := 12877) (a := (4126305736867 / 5000000000000 : ℝ)) (b := (79966688561 / 50000000000000 : ℝ)) (q := (2230423055741 / 100000000000000 : ℝ))
      (E := (cell12877 ⟨45, by decide⟩).energy) (xi := (65875345651643 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12877 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12877]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12877])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12877) (a := (4126305736867 / 5000000000000 : ℝ)) (b := (79966688561 / 50000000000000 : ℝ)) (q := (2230423055741 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12877])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12877])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12877]

theorem cert12877_46 : CellCertificate 12877 (88181100028921 / 1000000000000000 : ℝ) (815575591229609 / 500000000000000000 : ℝ) (65875345651643 / 2000000000000000 : ℝ)
    (cell12877 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · have h := gap_lower (n := 12877) (a := (82492280840243 / 100000000000000 : ℝ)) (b := (79966688561 / 50000000000000 : ℝ)) (q := (2230427035131 / 100000000000000 : ℝ))
      (E := (cell12877 ⟨46, by decide⟩).energy) (xi := (65875345651643 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12877 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12877]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12877])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12877) (a := (82492280840243 / 100000000000000 : ℝ)) (b := (79966688561 / 50000000000000 : ℝ)) (q := (2230427035131 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12877])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12877])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12877]

theorem cert12877_47 : CellCertificate 12877 (88181100028921 / 1000000000000000 : ℝ) (815575591229609 / 500000000000000000 : ℝ) (65875345651643 / 2000000000000000 : ℝ)
    (cell12877 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · have h := gap_lower (n := 12877) (a := (82458470336459 / 100000000000000 : ℝ)) (b := (79966688561 / 50000000000000 : ℝ)) (q := (2230431081011 / 100000000000000 : ℝ))
      (E := (cell12877 ⟨47, by decide⟩).energy) (xi := (65875345651643 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12877 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12877]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12877])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12877) (a := (82458470336459 / 100000000000000 : ℝ)) (b := (79966688561 / 50000000000000 : ℝ)) (q := (2230431081011 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12877])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12877])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12877]

theorem cert12877_48 : CellCertificate 12877 (88181100028921 / 1000000000000000 : ℝ) (815575591229609 / 500000000000000000 : ℝ) (65875345651643 / 2000000000000000 : ℝ)
    (cell12877 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · have h := gap_lower (n := 12877) (a := (41212341598583 / 50000000000000 : ℝ)) (b := (79966688561 / 50000000000000 : ℝ)) (q := (11152175367 / 500000000000 : ℝ))
      (E := (cell12877 ⟨48, by decide⟩).energy) (xi := (65875345651643 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12877 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12877]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12877])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12877) (a := (41212341598583 / 50000000000000 : ℝ)) (b := (79966688561 / 50000000000000 : ℝ)) (q := (11152175367 / 500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12877])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12877])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12877]

theorem cert12877_49 : CellCertificate 12877 (88181100028921 / 1000000000000000 : ℝ) (815575591229609 / 500000000000000000 : ℝ) (65875345651643 / 2000000000000000 : ℝ)
    (cell12877 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · have h := gap_lower (n := 12877) (a := (16478183878737 / 20000000000000 : ℝ)) (b := (79966688561 / 50000000000000 : ℝ)) (q := (2230439068843 / 100000000000000 : ℝ))
      (E := (cell12877 ⟨49, by decide⟩).energy) (xi := (65875345651643 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12877 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12877]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12877])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12877) (a := (16478183878737 / 20000000000000 : ℝ)) (b := (79966688561 / 50000000000000 : ℝ)) (q := (2230439068843 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12877])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12877])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12877]

theorem cert12877_50 : CellCertificate 12877 (88181100028921 / 1000000000000000 : ℝ) (815575591229609 / 500000000000000000 : ℝ) (65875345651643 / 2000000000000000 : ℝ)
    (cell12877 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · have h := gap_lower (n := 12877) (a := (82357178897481 / 100000000000000 : ℝ)) (b := (79966688561 / 50000000000000 : ℝ)) (q := (278805390471 / 12500000000000 : ℝ))
      (E := (cell12877 ⟨50, by decide⟩).energy) (xi := (65875345651643 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12877 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12877]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12877])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12877) (a := (82357178897481 / 100000000000000 : ℝ)) (b := (79966688561 / 50000000000000 : ℝ)) (q := (278805390471 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12877])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12877])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12877]

theorem cert12877_51 : CellCertificate 12877 (88181100028921 / 1000000000000000 : ℝ) (815575591229609 / 500000000000000000 : ℝ) (65875345651643 / 2000000000000000 : ℝ)
    (cell12877 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · have h := gap_lower (n := 12877) (a := (82323461680161 / 100000000000000 : ℝ)) (b := (79966688561 / 50000000000000 : ℝ)) (q := (2230447117417 / 100000000000000 : ℝ))
      (E := (cell12877 ⟨51, by decide⟩).energy) (xi := (65875345651643 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12877 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12877]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12877])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12877) (a := (82323461680161 / 100000000000000 : ℝ)) (b := (79966688561 / 50000000000000 : ℝ)) (q := (2230447117417 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12877])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12877])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12877]

theorem cert12877_52 : CellCertificate 12877 (88181100028921 / 1000000000000000 : ℝ) (815575591229609 / 500000000000000000 : ℝ) (65875345651643 / 2000000000000000 : ℝ)
    (cell12877 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · have h := gap_lower (n := 12877) (a := (41144883856737 / 50000000000000 : ℝ)) (b := (79966688561 / 50000000000000 : ℝ)) (q := (2230451105771 / 100000000000000 : ℝ))
      (E := (cell12877 ⟨52, by decide⟩).energy) (xi := (65875345651643 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12877 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12877]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12877])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12877) (a := (41144883856737 / 50000000000000 : ℝ)) (b := (79966688561 / 50000000000000 : ℝ)) (q := (2230451105771 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12877])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12877])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12877]

theorem cert12877_53 : CellCertificate 12877 (88181100028921 / 1000000000000000 : ℝ) (815575591229609 / 500000000000000000 : ℝ) (65875345651643 / 2000000000000000 : ℝ)
    (cell12877 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · have h := gap_lower (n := 12877) (a := (2570503030291 / 3125000000000 : ℝ)) (b := (79966688561 / 50000000000000 : ℝ)) (q := (446091028939 / 20000000000000 : ℝ))
      (E := (cell12877 ⟨53, by decide⟩).energy) (xi := (65875345651643 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12877 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12877]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12877])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12877) (a := (2570503030291 / 3125000000000 : ℝ)) (b := (79966688561 / 50000000000000 : ℝ)) (q := (446091028939 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12877])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12877])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12877]

theorem cert12877_54 : CellCertificate 12877 (88181100028921 / 1000000000000000 : ℝ) (815575591229609 / 500000000000000000 : ℝ) (65875345651643 / 2000000000000000 : ℝ)
    (cell12877 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · have h := gap_lower (n := 12877) (a := (16444489883941 / 20000000000000 : ℝ)) (b := (79966688561 / 50000000000000 : ℝ)) (q := (111522955633 / 5000000000000 : ℝ))
      (E := (cell12877 ⟨54, by decide⟩).energy) (xi := (65875345651643 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12877 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12877]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12877])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12877) (a := (16444489883941 / 20000000000000 : ℝ)) (b := (79966688561 / 50000000000000 : ℝ)) (q := (111522955633 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12877])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12877])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12877]

theorem cert12877_55 : CellCertificate 12877 (88181100028921 / 1000000000000000 : ℝ) (815575591229609 / 500000000000000000 : ℝ) (65875345651643 / 2000000000000000 : ℝ)
    (cell12877 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · have h := gap_lower (n := 12877) (a := (82188825036823 / 100000000000000 : ℝ)) (b := (79966688561 / 50000000000000 : ℝ)) (q := (139403945263 / 6250000000000 : ℝ))
      (E := (cell12877 ⟨55, by decide⟩).energy) (xi := (65875345651643 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12877 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12877]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12877])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12877) (a := (82188825036823 / 100000000000000 : ℝ)) (b := (79966688561 / 50000000000000 : ℝ)) (q := (139403945263 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12877])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12877])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12877]

theorem cert12877_56 : CellCertificate 12877 (88181100028921 / 1000000000000000 : ℝ) (815575591229609 / 500000000000000000 : ℝ) (65875345651643 / 2000000000000000 : ℝ)
    (cell12877 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · have h := gap_lower (n := 12877) (a := (82155223792977 / 100000000000000 : ℝ)) (b := (79966688561 / 50000000000000 : ℝ)) (q := (278808396947 / 12500000000000 : ℝ))
      (E := (cell12877 ⟨56, by decide⟩).energy) (xi := (65875345651643 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12877 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12877]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12877])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12877) (a := (82155223792977 / 100000000000000 : ℝ)) (b := (79966688561 / 50000000000000 : ℝ)) (q := (278808396947 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12877])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12877])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12877]

theorem cert12877_57 : CellCertificate 12877 (88181100028921 / 1000000000000000 : ℝ) (815575591229609 / 500000000000000000 : ℝ) (65875345651643 / 2000000000000000 : ℝ)
    (cell12877 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · have h := gap_lower (n := 12877) (a := (20530411415153 / 25000000000000 : ℝ)) (b := (79966688561 / 50000000000000 : ℝ)) (q := (2230471144473 / 100000000000000 : ℝ))
      (E := (cell12877 ⟨57, by decide⟩).energy) (xi := (65875345651643 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12877 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12877]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12877])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12877) (a := (20530411415153 / 25000000000000 : ℝ)) (b := (79966688561 / 50000000000000 : ℝ)) (q := (2230471144473 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12877])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12877])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12877]

theorem cert12877_58 : CellCertificate 12877 (88181100028921 / 1000000000000000 : ℝ) (815575591229609 / 500000000000000000 : ℝ) (65875345651643 / 2000000000000000 : ℝ)
    (cell12877 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · have h := gap_lower (n := 12877) (a := (41044045306157 / 50000000000000 : ℝ)) (b := (79966688561 / 50000000000000 : ℝ)) (q := (2230475144959 / 100000000000000 : ℝ))
      (E := (cell12877 ⟨58, by decide⟩).energy) (xi := (65875345651643 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12877 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12877]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12877])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12877) (a := (41044045306157 / 50000000000000 : ℝ)) (b := (79966688561 / 50000000000000 : ℝ)) (q := (2230475144959 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12877])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12877])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12877]

theorem cert12877_59 : CellCertificate 12877 (88181100028921 / 1000000000000000 : ℝ) (815575591229609 / 500000000000000000 : ℝ) (65875345651643 / 2000000000000000 : ℝ)
    (cell12877 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · have h := gap_lower (n := 12877) (a := (82054558620803 / 100000000000000 : ℝ)) (b := (79966688561 / 50000000000000 : ℝ)) (q := (1115239586327 / 50000000000000 : ℝ))
      (E := (cell12877 ⟨59, by decide⟩).energy) (xi := (65875345651643 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12877 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12877]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12877])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12877) (a := (82054558620803 / 100000000000000 : ℝ)) (b := (79966688561 / 50000000000000 : ℝ)) (q := (1115239586327 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12877])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12877])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12877]

theorem cert12878_40 : CellCertificate 12878 (881783797826647 / 10000000000000000 : ℝ) (326204895909779 / 200000000000000000 : ℝ) (82337636342589 / 2500000000000000 : ℝ)
    (cell12878 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · have h := gap_lower (n := 12878) (a := (41347816811039 / 50000000000000 : ℝ)) (b := (79960405417 / 50000000000000 : ℝ)) (q := (557571417473 / 25000000000000 : ℝ))
      (E := (cell12878 ⟨40, by decide⟩).energy) (xi := (82337636342589 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12878 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12878]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12878])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12878) (a := (41347816811039 / 50000000000000 : ℝ)) (b := (79960405417 / 50000000000000 : ℝ)) (q := (557571417473 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12878])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12878])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12878]

theorem cert12878_41 : CellCertificate 12878 (881783797826647 / 10000000000000000 : ℝ) (326204895909779 / 200000000000000000 : ℝ) (82337636342589 / 2500000000000000 : ℝ)
    (cell12878 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · have h := gap_lower (n := 12878) (a := (41330841308611 / 50000000000000 : ℝ)) (b := (79960405417 / 50000000000000 : ℝ)) (q := (6969655337 / 312500000000 : ℝ))
      (E := (cell12878 ⟨41, by decide⟩).energy) (xi := (82337636342589 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12878 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12878]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12878])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12878) (a := (41330841308611 / 50000000000000 : ℝ)) (b := (79960405417 / 50000000000000 : ℝ)) (q := (6969655337 / 312500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12878])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12878])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12878]

theorem cert12878_42 : CellCertificate 12878 (881783797826647 / 10000000000000000 : ℝ) (326204895909779 / 200000000000000000 : ℝ) (82337636342589 / 2500000000000000 : ℝ)
    (cell12878 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · have h := gap_lower (n := 12878) (a := (41313877575793 / 50000000000000 : ℝ)) (b := (79960405417 / 50000000000000 : ℝ)) (q := (2230293702821 / 100000000000000 : ℝ))
      (E := (cell12878 ⟨42, by decide⟩).energy) (xi := (82337636342589 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12878 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12878]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12878])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12878) (a := (41313877575793 / 50000000000000 : ℝ)) (b := (79960405417 / 50000000000000 : ℝ)) (q := (2230293702821 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12878])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12878])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12878]

theorem cert12878_43 : CellCertificate 12878 (881783797826647 / 10000000000000000 : ℝ) (326204895909779 / 200000000000000000 : ℝ) (82337636342589 / 2500000000000000 : ℝ)
    (cell12878 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · have h := gap_lower (n := 12878) (a := (20648462798903 / 25000000000000 : ℝ)) (b := (79960405417 / 50000000000000 : ℝ)) (q := (2230297712531 / 100000000000000 : ℝ))
      (E := (cell12878 ⟨43, by decide⟩).energy) (xi := (82337636342589 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12878 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12878]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12878])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12878) (a := (20648462798903 / 25000000000000 : ℝ)) (b := (79960405417 / 50000000000000 : ℝ)) (q := (2230297712531 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12878])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12878])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12878]

theorem cert12878_44 : CellCertificate 12878 (881783797826647 / 10000000000000000 : ℝ) (326204895909779 / 200000000000000000 : ℝ) (82337636342589 / 2500000000000000 : ℝ)
    (cell12878 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · have h := gap_lower (n := 12878) (a := (8255997071989 / 10000000000000 : ℝ)) (b := (79960405417 / 50000000000000 : ℝ)) (q := (2230301735683 / 100000000000000 : ℝ))
      (E := (cell12878 ⟨44, by decide⟩).energy) (xi := (82337636342589 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12878 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12878]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12878])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12878) (a := (8255997071989 / 10000000000000 : ℝ)) (b := (79960405417 / 50000000000000 : ℝ)) (q := (2230301735683 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12878])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12878])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12878]

theorem cert12878_45 : CellCertificate 12878 (881783797826647 / 10000000000000000 : ℝ) (326204895909779 / 200000000000000000 : ℝ) (82337636342589 / 2500000000000000 : ℝ)
    (cell12878 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · have h := gap_lower (n := 12878) (a := (82526113695159 / 100000000000000 : ℝ)) (b := (79960405417 / 50000000000000 : ℝ)) (q := (1115152855947 / 50000000000000 : ℝ))
      (E := (cell12878 ⟨45, by decide⟩).energy) (xi := (82337636342589 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12878 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12878]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12878])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12878) (a := (82526113695159 / 100000000000000 : ℝ)) (b := (79960405417 / 50000000000000 : ℝ)) (q := (1115152855947 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12878])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12878])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12878]

theorem cert12878_46 : CellCertificate 12878 (881783797826647 / 10000000000000000 : ℝ) (326204895909779 / 200000000000000000 : ℝ) (82337636342589 / 2500000000000000 : ℝ)
    (cell12878 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · have h := gap_lower (n := 12878) (a := (82492280092307 / 100000000000000 : ℝ)) (b := (79960405417 / 50000000000000 : ℝ)) (q := (1115154878591 / 50000000000000 : ℝ))
      (E := (cell12878 ⟨46, by decide⟩).energy) (xi := (82337636342589 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12878 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12878]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12878])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12878) (a := (82492280092307 / 100000000000000 : ℝ)) (b := (79960405417 / 50000000000000 : ℝ)) (q := (1115154878591 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12878])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12878])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12878]

theorem cert12878_47 : CellCertificate 12878 (881783797826647 / 10000000000000000 : ℝ) (326204895909779 / 200000000000000000 : ℝ) (82337636342589 / 2500000000000000 : ℝ)
    (cell12878 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · have h := gap_lower (n := 12878) (a := (82458469882363 / 100000000000000 : ℝ)) (b := (79960405417 / 50000000000000 : ℝ)) (q := (278789218979 / 12500000000000 : ℝ))
      (E := (cell12878 ⟨47, by decide⟩).energy) (xi := (82337636342589 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12878 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12878]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12878])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12878) (a := (82458469882363 / 100000000000000 : ℝ)) (b := (79960405417 / 50000000000000 : ℝ)) (q := (278789218979 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12878])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12878])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12878]

theorem cert12878_48 : CellCertificate 12878 (881783797826647 / 10000000000000000 : ℝ) (326204895909779 / 200000000000000000 : ℝ) (82337636342589 / 2500000000000000 : ℝ)
    (cell12878 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · have h := gap_lower (n := 12878) (a := (82424683036507 / 100000000000000 : ℝ)) (b := (79960405417 / 50000000000000 : ℝ)) (q := (89212710103 / 4000000000000 : ℝ))
      (E := (cell12878 ⟨48, by decide⟩).energy) (xi := (82337636342589 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12878 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12878]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12878])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12878) (a := (82424683036507 / 100000000000000 : ℝ)) (b := (79960405417 / 50000000000000 : ℝ)) (q := (89212710103 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12878])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12878])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12878]

theorem cert12878_49 : CellCertificate 12878 (881783797826647 / 10000000000000000 : ℝ) (326204895909779 / 200000000000000000 : ℝ) (82337636342589 / 2500000000000000 : ℝ)
    (cell12878 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · have h := gap_lower (n := 12878) (a := (82390919526059 / 100000000000000 : ℝ)) (b := (79960405417 / 50000000000000 : ℝ)) (q := (2230321757053 / 100000000000000 : ℝ))
      (E := (cell12878 ⟨49, by decide⟩).energy) (xi := (82337636342589 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12878 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12878]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12878])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12878) (a := (82390919526059 / 100000000000000 : ℝ)) (b := (79960405417 / 50000000000000 : ℝ)) (q := (2230321757053 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12878])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12878])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12878]

theorem cert12878_50 : CellCertificate 12878 (881783797826647 / 10000000000000000 : ℝ) (326204895909779 / 200000000000000000 : ℝ) (82337636342589 / 2500000000000000 : ℝ)
    (cell12878 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · have h := gap_lower (n := 12878) (a := (41178589661243 / 50000000000000 : ℝ)) (b := (79960405417 / 50000000000000 : ℝ)) (q := (2230325762691 / 100000000000000 : ℝ))
      (E := (cell12878 ⟨50, by decide⟩).energy) (xi := (82337636342589 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12878 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12878]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12878])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12878) (a := (41178589661243 / 50000000000000 : ℝ)) (b := (79960405417 / 50000000000000 : ℝ)) (q := (2230325762691 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12878])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12878])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12878]

theorem cert12878_51 : CellCertificate 12878 (881783797826647 / 10000000000000000 : ℝ) (326204895909779 / 200000000000000000 : ℝ) (82337636342589 / 2500000000000000 : ℝ)
    (cell12878 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · have h := gap_lower (n := 12878) (a := (16464692479479 / 20000000000000 : ℝ)) (b := (79960405417 / 50000000000000 : ℝ)) (q := (2230329766707 / 100000000000000 : ℝ))
      (E := (cell12878 ⟨51, by decide⟩).energy) (xi := (82337636342589 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12878 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12878]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12878])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12878) (a := (16464692479479 / 20000000000000 : ℝ)) (b := (79960405417 / 50000000000000 : ℝ)) (q := (2230329766707 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12878])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12878])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12878]

theorem cert12878_52 : CellCertificate 12878 (881783797826647 / 10000000000000000 : ℝ) (326204895909779 / 200000000000000000 : ℝ) (82337636342589 / 2500000000000000 : ℝ)
    (cell12878 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · have h := gap_lower (n := 12878) (a := (82289768722537 / 100000000000000 : ℝ)) (b := (79960405417 / 50000000000000 : ℝ)) (q := (1115166883053 / 50000000000000 : ℝ))
      (E := (cell12878 ⟨52, by decide⟩).energy) (xi := (82337636342589 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12878 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12878]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12878])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12878) (a := (82289768722537 / 100000000000000 : ℝ)) (b := (79960405417 / 50000000000000 : ℝ)) (q := (1115166883053 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12878])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12878])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12878]

theorem cert12878_53 : CellCertificate 12878 (881783797826647 / 10000000000000000 : ℝ) (326204895909779 / 200000000000000000 : ℝ) (82337636342589 / 2500000000000000 : ℝ)
    (cell12878 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · have h := gap_lower (n := 12878) (a := (82256098269803 / 100000000000000 : ℝ)) (b := (79960405417 / 50000000000000 : ℝ)) (q := (2230337816751 / 100000000000000 : ℝ))
      (E := (cell12878 ⟨53, by decide⟩).energy) (xi := (82337636342589 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12878 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12878]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12878])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12878) (a := (82256098269803 / 100000000000000 : ℝ)) (b := (79960405417 / 50000000000000 : ℝ)) (q := (2230337816751 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12878])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12878])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12878]

theorem cert12878_54 : CellCertificate 12878 (881783797826647 / 10000000000000000 : ℝ) (326204895909779 / 200000000000000000 : ℝ) (82337636342589 / 2500000000000000 : ℝ)
    (cell12878 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · have h := gap_lower (n := 12878) (a := (10277806376403 / 12500000000000 : ℝ)) (b := (79960405417 / 50000000000000 : ℝ)) (q := (2230341797113 / 100000000000000 : ℝ))
      (E := (cell12878 ⟨54, by decide⟩).energy) (xi := (82337636342589 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12878 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12878]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12878])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12878) (a := (10277806376403 / 12500000000000 : ℝ)) (b := (79960405417 / 50000000000000 : ℝ)) (q := (2230341797113 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12878])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12878])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12878]

theorem cert12878_55 : CellCertificate 12878 (881783797826647 / 10000000000000000 : ℝ) (326204895909779 / 200000000000000000 : ℝ) (82337636342589 / 2500000000000000 : ℝ)
    (cell12878 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · have h := gap_lower (n := 12878) (a := (20547206729743 / 25000000000000 : ℝ)) (b := (79960405417 / 50000000000000 : ℝ)) (q := (2230345821733 / 100000000000000 : ℝ))
      (E := (cell12878 ⟨55, by decide⟩).energy) (xi := (82337636342589 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12878 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12878]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12878])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12878) (a := (20547206729743 / 25000000000000 : ℝ)) (b := (79960405417 / 50000000000000 : ℝ)) (q := (2230345821733 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12878])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12878])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12878]

theorem cert12878_56 : CellCertificate 12878 (881783797826647 / 10000000000000000 : ℝ) (326204895909779 / 200000000000000000 : ℝ) (82337636342589 / 2500000000000000 : ℝ)
    (cell12878 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · have h := gap_lower (n := 12878) (a := (82155225965357 / 100000000000000 : ℝ)) (b := (79960405417 / 50000000000000 : ℝ)) (q := (557587456927 / 25000000000000 : ℝ))
      (E := (cell12878 ⟨56, by decide⟩).energy) (xi := (82337636342589 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12878 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12878]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12878])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12878) (a := (82155225965357 / 100000000000000 : ℝ)) (b := (79960405417 / 50000000000000 : ℝ)) (q := (557587456927 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12878])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12878])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12878]

theorem cert12878_57 : CellCertificate 12878 (881783797826647 / 10000000000000000 : ℝ) (326204895909779 / 200000000000000000 : ℝ) (82337636342589 / 2500000000000000 : ℝ)
    (cell12878 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · have h := gap_lower (n := 12878) (a := (41060824061413 / 50000000000000 : ℝ)) (b := (79960405417 / 50000000000000 : ℝ)) (q := (2230353811003 / 100000000000000 : ℝ))
      (E := (cell12878 ⟨57, by decide⟩).energy) (xi := (82337636342589 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12878 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12878]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12878])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12878) (a := (41060824061413 / 50000000000000 : ℝ)) (b := (79960405417 / 50000000000000 : ℝ)) (q := (2230353811003 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12878])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12878])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12878]

theorem cert12878_58 : CellCertificate 12878 (881783797826647 / 10000000000000000 : ℝ) (326204895909779 / 200000000000000000 : ℝ) (82337636342589 / 2500000000000000 : ℝ)
    (cell12878 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · have h := gap_lower (n := 12878) (a := (20522023340991 / 25000000000000 : ℝ)) (b := (79960405417 / 50000000000000 : ℝ)) (q := (2230357826561 / 100000000000000 : ℝ))
      (E := (cell12878 ⟨58, by decide⟩).energy) (xi := (82337636342589 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12878 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12878]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12878])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12878) (a := (20522023340991 / 25000000000000 : ℝ)) (b := (79960405417 / 50000000000000 : ℝ)) (q := (2230357826561 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12878])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12878])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12878]

theorem cert12878_59 : CellCertificate 12878 (881783797826647 / 10000000000000000 : ℝ) (326204895909779 / 200000000000000000 : ℝ) (82337636342589 / 2500000000000000 : ℝ)
    (cell12878 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · have h := gap_lower (n := 12878) (a := (82054561661493 / 100000000000000 : ℝ)) (b := (79960405417 / 50000000000000 : ℝ)) (q := (223036187 / 10000000000 : ℝ))
      (E := (cell12878 ⟨59, by decide⟩).energy) (xi := (82337636342589 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12878 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12878]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12878])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12878) (a := (82054561661493 / 100000000000000 : ℝ)) (b := (79960405417 / 50000000000000 : ℝ)) (q := (223036187 / 10000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12878])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12878])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12878]

theorem cert12879_40 : CellCertificate 12879 (55109787463409 / 625000000000000 : ℝ) (815448898160421 / 500000000000000000 : ℝ) (329324366688777 / 10000000000000000 : ℝ)
    (cell12879 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · have h := gap_lower (n := 12879) (a := (41347815551703 / 50000000000000 : ℝ)) (b := (39977061633 / 25000000000000 : ℝ)) (q := (446033671411 / 20000000000000 : ℝ))
      (E := (cell12879 ⟨40, by decide⟩).energy) (xi := (329324366688777 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12879 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12879]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12879])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12879) (a := (41347815551703 / 50000000000000 : ℝ)) (b := (39977061633 / 25000000000000 : ℝ)) (q := (446033671411 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12879])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12879])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12879]

theorem cert12879_41 : CellCertificate 12879 (55109787463409 / 625000000000000 : ℝ) (815448898160421 / 500000000000000000 : ℝ) (329324366688777 / 10000000000000000 : ℝ)
    (cell12879 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · have h := gap_lower (n := 12879) (a := (41330840197397 / 50000000000000 : ℝ)) (b := (39977061633 / 25000000000000 : ℝ)) (q := (2230172398643 / 100000000000000 : ℝ))
      (E := (cell12879 ⟨41, by decide⟩).energy) (xi := (329324366688777 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12879 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12879]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12879])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12879) (a := (41330840197397 / 50000000000000 : ℝ)) (b := (39977061633 / 25000000000000 : ℝ)) (q := (2230172398643 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12879])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12879])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12879]

theorem cert12879_42 : CellCertificate 12879 (55109787463409 / 625000000000000 : ℝ) (815448898160421 / 500000000000000000 : ℝ) (329324366688777 / 10000000000000000 : ℝ)
    (cell12879 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · have h := gap_lower (n := 12879) (a := (82627753224993 / 100000000000000 : ℝ)) (b := (39977061633 / 25000000000000 : ℝ)) (q := (557544099487 / 25000000000000 : ℝ))
      (E := (cell12879 ⟨42, by decide⟩).energy) (xi := (329324366688777 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12879 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12879]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12879])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12879) (a := (82627753224993 / 100000000000000 : ℝ)) (b := (39977061633 / 25000000000000 : ℝ)) (q := (557544099487 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12879])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12879])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12879]

theorem cert12879_43 : CellCertificate 12879 (55109787463409 / 625000000000000 : ℝ) (815448898160421 / 500000000000000000 : ℝ) (329324366688777 / 10000000000000000 : ℝ)
    (cell12879 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · have h := gap_lower (n := 12879) (a := (41296924782223 / 50000000000000 : ℝ)) (b := (39977061633 / 25000000000000 : ℝ)) (q := (446036082533 / 20000000000000 : ℝ))
      (E := (cell12879 ⟨43, by decide⟩).energy) (xi := (329324366688777 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12879 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12879]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12879])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12879) (a := (41296924782223 / 50000000000000 : ℝ)) (b := (39977061633 / 25000000000000 : ℝ)) (q := (446036082533 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12879])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12879])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12879]

theorem cert12879_44 : CellCertificate 12879 (55109787463409 / 625000000000000 : ℝ) (815448898160421 / 500000000000000000 : ℝ) (329324366688777 / 10000000000000000 : ℝ)
    (cell12879 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · have h := gap_lower (n := 12879) (a := (16511993876749 / 20000000000000 : ℝ)) (b := (39977061633 / 25000000000000 : ℝ)) (q := (2230184441507 / 100000000000000 : ℝ))
      (E := (cell12879 ⟨44, by decide⟩).energy) (xi := (329324366688777 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12879 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12879]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12879])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12879) (a := (16511993876749 / 20000000000000 : ℝ)) (b := (39977061633 / 25000000000000 : ℝ)) (q := (2230184441507 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12879])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12879])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12879]

theorem cert12879_45 : CellCertificate 12879 (55109787463409 / 625000000000000 : ℝ) (815448898160421 / 500000000000000000 : ℝ) (329324366688777 / 10000000000000000 : ℝ)
    (cell12879 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · have h := gap_lower (n := 12879) (a := (8252611265363 / 10000000000000 : ℝ)) (b := (39977061633 / 25000000000000 : ℝ)) (q := (278773553011 / 12500000000000 : ℝ))
      (E := (cell12879 ⟨45, by decide⟩).energy) (xi := (329324366688777 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12879 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12879]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12879])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12879) (a := (8252611265363 / 10000000000000 : ℝ)) (b := (39977061633 / 25000000000000 : ℝ)) (q := (278773553011 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12879])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12879])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12879]

theorem cert12879_46 : CellCertificate 12879 (55109787463409 / 625000000000000 : ℝ) (815448898160421 / 500000000000000000 : ℝ) (329324366688777 / 10000000000000000 : ℝ)
    (cell12879 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · have h := gap_lower (n := 12879) (a := (82492279344987 / 100000000000000 : ℝ)) (b := (39977061633 / 25000000000000 : ℝ)) (q := (1115096208763 / 50000000000000 : ℝ))
      (E := (cell12879 ⟨46, by decide⟩).energy) (xi := (329324366688777 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12879 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12879]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12879])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12879) (a := (82492279344987 / 100000000000000 : ℝ)) (b := (39977061633 / 25000000000000 : ℝ)) (q := (1115096208763 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12879])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12879])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12879]

theorem cert12879_47 : CellCertificate 12879 (55109787463409 / 625000000000000 : ℝ) (815448898160421 / 500000000000000000 : ℝ) (329324366688777 / 10000000000000000 : ℝ)
    (cell12879 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · have h := gap_lower (n := 12879) (a := (82458469428849 / 100000000000000 : ℝ)) (b := (39977061633 / 25000000000000 : ℝ)) (q := (446039283977 / 20000000000000 : ℝ))
      (E := (cell12879 ⟨47, by decide⟩).energy) (xi := (329324366688777 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12879 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12879]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12879])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12879) (a := (82458469428849 / 100000000000000 : ℝ)) (b := (39977061633 / 25000000000000 : ℝ)) (q := (446039283977 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12879])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12879])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12879]

theorem cert12879_48 : CellCertificate 12879 (55109787463409 / 625000000000000 : ℝ) (815448898160421 / 500000000000000000 : ℝ) (329324366688777 / 10000000000000000 : ℝ)
    (cell12879 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · have h := gap_lower (n := 12879) (a := (41212341438197 / 50000000000000 : ℝ)) (b := (39977061633 / 25000000000000 : ℝ)) (q := (2230200429019 / 100000000000000 : ℝ))
      (E := (cell12879 ⟨48, by decide⟩).energy) (xi := (329324366688777 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12879 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12879]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12879])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12879) (a := (41212341438197 / 50000000000000 : ℝ)) (b := (39977061633 / 25000000000000 : ℝ)) (q := (2230200429019 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12879])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12879])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12879]

theorem cert12879_49 : CellCertificate 12879 (55109787463409 / 625000000000000 : ℝ) (815448898160421 / 500000000000000000 : ℝ) (329324366688777 / 10000000000000000 : ℝ)
    (cell12879 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · have h := gap_lower (n := 12879) (a := (16478183931789 / 20000000000000 : ℝ)) (b := (39977061633 / 25000000000000 : ℝ)) (q := (1115102221283 / 50000000000000 : ℝ))
      (E := (cell12879 ⟨49, by decide⟩).energy) (xi := (329324366688777 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12879 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12879]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12879])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12879) (a := (16478183931789 / 20000000000000 : ℝ)) (b := (39977061633 / 25000000000000 : ℝ)) (q := (1115102221283 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12879])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12879])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12879]

theorem cert12879_50 : CellCertificate 12879 (55109787463409 / 625000000000000 : ℝ) (815448898160421 / 500000000000000000 : ℝ) (329324366688777 / 10000000000000000 : ℝ)
    (cell12879 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · have h := gap_lower (n := 12879) (a := (643415466781 / 781250000000 : ℝ)) (b := (39977061633 / 25000000000000 : ℝ)) (q := (2230208457953 / 100000000000000 : ℝ))
      (E := (cell12879 ⟨50, by decide⟩).energy) (xi := (329324366688777 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12879 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12879]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12879])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12879) (a := (643415466781 / 781250000000 : ℝ)) (b := (39977061633 / 25000000000000 : ℝ)) (q := (2230208457953 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12879])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12879])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12879]

theorem cert12879_51 : CellCertificate 12879 (55109787463409 / 625000000000000 : ℝ) (815448898160421 / 500000000000000000 : ℝ) (329324366688777 / 10000000000000000 : ℝ)
    (cell12879 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · have h := gap_lower (n := 12879) (a := (82323463115071 / 100000000000000 : ℝ)) (b := (39977061633 / 25000000000000 : ℝ)) (q := (557553118099 / 25000000000000 : ℝ))
      (E := (cell12879 ⟨51, by decide⟩).energy) (xi := (329324366688777 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12879 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12879]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12879])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12879) (a := (82323463115071 / 100000000000000 : ℝ)) (b := (39977061633 / 25000000000000 : ℝ)) (q := (557553118099 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12879])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12879])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12879]

theorem cert12879_52 : CellCertificate 12879 (55109787463409 / 625000000000000 : ℝ) (815448898160421 / 500000000000000000 : ℝ) (329324366688777 / 10000000000000000 : ℝ)
    (cell12879 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · have h := gap_lower (n := 12879) (a := (82289769732007 / 100000000000000 : ℝ)) (b := (39977061633 / 25000000000000 : ℝ)) (q := (2230216482897 / 100000000000000 : ℝ))
      (E := (cell12879 ⟨52, by decide⟩).energy) (xi := (329324366688777 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12879 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12879]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12879])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12879) (a := (82289769732007 / 100000000000000 : ℝ)) (b := (39977061633 / 25000000000000 : ℝ)) (q := (2230216482897 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12879])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12879])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12879]

theorem cert12879_53 : CellCertificate 12879 (55109787463409 / 625000000000000 : ℝ) (815448898160421 / 500000000000000000 : ℝ) (329324366688777 / 10000000000000000 : ℝ)
    (cell12879 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · have h := gap_lower (n := 12879) (a := (41128049785333 / 50000000000000 : ℝ)) (b := (39977061633 / 25000000000000 : ℝ)) (q := (2230220486253 / 100000000000000 : ℝ))
      (E := (cell12879 ⟨53, by decide⟩).energy) (xi := (329324366688777 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12879 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12879]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12879])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12879) (a := (41128049785333 / 50000000000000 : ℝ)) (b := (39977061633 / 25000000000000 : ℝ)) (q := (2230220486253 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12879])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12879])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12879]

theorem cert12879_54 : CellCertificate 12879 (55109787463409 / 625000000000000 : ℝ) (815448898160421 / 500000000000000000 : ℝ) (329324366688777 / 10000000000000000 : ℝ)
    (cell12879 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · have h := gap_lower (n := 12879) (a := (82222452603081 / 100000000000000 : ℝ)) (b := (39977061633 / 25000000000000 : ℝ)) (q := (278778059881 / 12500000000000 : ℝ))
      (E := (cell12879 ⟨54, by decide⟩).energy) (xi := (329324366688777 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12879 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12879]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12879])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12879) (a := (82222452603081 / 100000000000000 : ℝ)) (b := (39977061633 / 25000000000000 : ℝ)) (q := (278778059881 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12879])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12879])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12879]

theorem cert12879_55 : CellCertificate 12879 (55109787463409 / 625000000000000 : ℝ) (815448898160421 / 500000000000000000 : ℝ) (329324366688777 / 10000000000000000 : ℝ)
    (cell12879 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · have h := gap_lower (n := 12879) (a := (82188828801423 / 100000000000000 : ℝ)) (b := (39977061633 / 25000000000000 : ℝ)) (q := (278778564597 / 12500000000000 : ℝ))
      (E := (cell12879 ⟨55, by decide⟩).energy) (xi := (329324366688777 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12879 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12879]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12879])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12879) (a := (82188828801423 / 100000000000000 : ℝ)) (b := (39977061633 / 25000000000000 : ℝ)) (q := (278778564597 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12879])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12879])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12879]

theorem cert12879_56 : CellCertificate 12879 (55109787463409 / 625000000000000 : ℝ) (815448898160421 / 500000000000000000 : ℝ) (329324366688777 / 10000000000000000 : ℝ)
    (cell12879 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · have h := gap_lower (n := 12879) (a := (16431045627601 / 20000000000000 : ℝ)) (b := (39977061633 / 25000000000000 : ℝ)) (q := (1115116268267 / 50000000000000 : ℝ))
      (E := (cell12879 ⟨56, by decide⟩).energy) (xi := (329324366688777 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12879 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12879]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12879])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12879) (a := (16431045627601 / 20000000000000 : ℝ)) (b := (39977061633 / 25000000000000 : ℝ)) (q := (1115116268267 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12879])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12879])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12879]

theorem cert12879_57 : CellCertificate 12879 (55109787463409 / 625000000000000 : ℝ) (815448898160421 / 500000000000000000 : ℝ) (329324366688777 / 10000000000000000 : ℝ)
    (cell12879 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · have h := gap_lower (n := 12879) (a := (82121650585273 / 100000000000000 : ℝ)) (b := (39977061633 / 25000000000000 : ℝ)) (q := (446047306857 / 20000000000000 : ℝ))
      (E := (cell12879 ⟨57, by decide⟩).energy) (xi := (329324366688777 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12879 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12879]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12879])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12879) (a := (82121650585273 / 100000000000000 : ℝ)) (b := (39977061633 / 25000000000000 : ℝ)) (q := (446047306857 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12879])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12879])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12879]

theorem cert12879_58 : CellCertificate 12879 (55109787463409 / 625000000000000 : ℝ) (815448898160421 / 500000000000000000 : ℝ) (329324366688777 / 10000000000000000 : ℝ)
    (cell12879 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · have h := gap_lower (n := 12879) (a := (82088096115813 / 100000000000000 : ℝ)) (b := (39977061633 / 25000000000000 : ℝ)) (q := (1115120252893 / 50000000000000 : ℝ))
      (E := (cell12879 ⟨58, by decide⟩).energy) (xi := (329324366688777 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12879 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12879]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12879])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12879) (a := (82088096115813 / 100000000000000 : ℝ)) (b := (39977061633 / 25000000000000 : ℝ)) (q := (1115120252893 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12879])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12879])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12879]

theorem cert12879_59 : CellCertificate 12879 (55109787463409 / 625000000000000 : ℝ) (815448898160421 / 500000000000000000 : ℝ) (329324366688777 / 10000000000000000 : ℝ)
    (cell12879 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · have h := gap_lower (n := 12879) (a := (20513641175587 / 25000000000000 : ℝ)) (b := (39977061633 / 25000000000000 : ℝ)) (q := (446048913001 / 20000000000000 : ℝ))
      (E := (cell12879 ⟨59, by decide⟩).energy) (xi := (329324366688777 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12879 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12879]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12879])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12879) (a := (20513641175587 / 25000000000000 : ℝ)) (b := (39977061633 / 25000000000000 : ℝ)) (q := (446048913001 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12879])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12879])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12879]

theorem cert12880_40 : CellCertificate 12880 (17634588101039 / 200000000000000 : ℝ) (1630771132770473 / 1000000000000000000 : ℝ) (41162274026549 / 1250000000000000 : ℝ)
    (cell12880 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · have h := gap_lower (n := 12880) (a := (41347814292781 / 50000000000000 : ℝ)) (b := (79947842107 / 50000000000000 : ℝ)) (q := (446010219993 / 20000000000000 : ℝ))
      (E := (cell12880 ⟨40, by decide⟩).energy) (xi := (41162274026549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12880 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12880]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12880])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12880) (a := (41347814292781 / 50000000000000 : ℝ)) (b := (79947842107 / 50000000000000 : ℝ)) (q := (446010219993 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12880])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12880])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12880]

theorem cert12880_41 : CellCertificate 12880 (17634588101039 / 200000000000000 : ℝ) (1630771132770473 / 1000000000000000000 : ℝ) (41162274026549 / 1250000000000000 : ℝ)
    (cell12880 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · have h := gap_lower (n := 12880) (a := (41330839086579 / 50000000000000 : ℝ)) (b := (79947842107 / 50000000000000 : ℝ)) (q := (17422305363 / 781250000000 : ℝ))
      (E := (cell12880 ⟨41, by decide⟩).energy) (xi := (41162274026549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12880 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12880]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12880])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12880) (a := (41330839086579 / 50000000000000 : ℝ)) (b := (79947842107 / 50000000000000 : ℝ)) (q := (17422305363 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12880])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12880])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12880]

theorem cert12880_42 : CellCertificate 12880 (17634588101039 / 200000000000000 : ℝ) (1630771132770473 / 1000000000000000000 : ℝ) (41162274026549 / 1250000000000000 : ℝ)
    (cell12880 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · have h := gap_lower (n := 12880) (a := (20656937824789 / 25000000000000 : ℝ)) (b := (79947842107 / 50000000000000 : ℝ)) (q := (2230059148941 / 100000000000000 : ℝ))
      (E := (cell12880 ⟨42, by decide⟩).energy) (xi := (41162274026549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12880 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12880]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12880])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12880) (a := (20656937824789 / 25000000000000 : ℝ)) (b := (79947842107 / 50000000000000 : ℝ)) (q := (2230059148941 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12880])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12880])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12880]

theorem cert12880_43 : CellCertificate 12880 (17634588101039 / 200000000000000 : ℝ) (1630771132770473 / 1000000000000000000 : ℝ) (41162274026549 / 1250000000000000 : ℝ)
    (cell12880 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · have h := gap_lower (n := 12880) (a := (41296923967001 / 50000000000000 : ℝ)) (b := (79947842107 / 50000000000000 : ℝ)) (q := (2230063109889 / 100000000000000 : ℝ))
      (E := (cell12880 ⟨43, by decide⟩).energy) (xi := (41162274026549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12880 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12880]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12880])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12880) (a := (41296923967001 / 50000000000000 : ℝ)) (b := (79947842107 / 50000000000000 : ℝ)) (q := (2230063109889 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12880])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12880])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12880]

theorem cert12880_44 : CellCertificate 12880 (17634588101039 / 200000000000000 : ℝ) (1630771132770473 / 1000000000000000000 : ℝ) (41162274026549 / 1250000000000000 : ℝ)
    (cell12880 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · have h := gap_lower (n := 12880) (a := (82559968048287 / 100000000000000 : ℝ)) (b := (79947842107 / 50000000000000 : ℝ)) (q := (2230067144457 / 100000000000000 : ℝ))
      (E := (cell12880 ⟨44, by decide⟩).energy) (xi := (41162274026549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12880 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12880]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12880])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12880) (a := (82559968048287 / 100000000000000 : ℝ)) (b := (79947842107 / 50000000000000 : ℝ)) (q := (2230067144457 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12880])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12880])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12880]

theorem cert12880_45 : CellCertificate 12880 (17634588101039 / 200000000000000 : ℝ) (1630771132770473 / 1000000000000000000 : ℝ) (41162274026549 / 1250000000000000 : ℝ)
    (cell12880 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · have h := gap_lower (n := 12880) (a := (82526111612751 / 100000000000000 : ℝ)) (b := (79947842107 / 50000000000000 : ℝ)) (q := (2230071133447 / 100000000000000 : ℝ))
      (E := (cell12880 ⟨45, by decide⟩).energy) (xi := (41162274026549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12880 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12880]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12880])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12880) (a := (82526111612751 / 100000000000000 : ℝ)) (b := (79947842107 / 50000000000000 : ℝ)) (q := (2230071133447 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12880])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12880])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12880]

theorem cert12880_46 : CellCertificate 12880 (17634588101039 / 200000000000000 : ℝ) (1630771132770473 / 1000000000000000000 : ℝ) (41162274026549 / 1250000000000000 : ℝ)
    (cell12880 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · have h := gap_lower (n := 12880) (a := (82492278598283 / 100000000000000 : ℝ)) (b := (79947842107 / 50000000000000 : ℝ)) (q := (1115037566987 / 50000000000000 : ℝ))
      (E := (cell12880 ⟨46, by decide⟩).energy) (xi := (41162274026549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12880 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12880]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12880])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12880) (a := (82492278598283 / 100000000000000 : ℝ)) (b := (79947842107 / 50000000000000 : ℝ)) (q := (1115037566987 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12880])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12880])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12880]

theorem cert12880_47 : CellCertificate 12880 (17634588101039 / 200000000000000 : ℝ) (1630771132770473 / 1000000000000000000 : ℝ) (41162274026549 / 1250000000000000 : ℝ)
    (cell12880 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · have h := gap_lower (n := 12880) (a := (16491693795183 / 20000000000000 : ℝ)) (b := (79947842107 / 50000000000000 : ℝ)) (q := (2230079144103 / 100000000000000 : ℝ))
      (E := (cell12880 ⟨47, by decide⟩).energy) (xi := (41162274026549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12880 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12880]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12880])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12880) (a := (16491693795183 / 20000000000000 : ℝ)) (b := (79947842107 / 50000000000000 : ℝ)) (q := (2230079144103 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12880])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12880])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12880]

theorem cert12880_48 : CellCertificate 12880 (17634588101039 / 200000000000000 : ℝ) (1630771132770473 / 1000000000000000000 : ℝ) (41162274026549 / 1250000000000000 : ℝ)
    (cell12880 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · have h := gap_lower (n := 12880) (a := (82424682716827 / 100000000000000 : ℝ)) (b := (79947842107 / 50000000000000 : ℝ)) (q := (1115041580843 / 50000000000000 : ℝ))
      (E := (cell12880 ⟨48, by decide⟩).energy) (xi := (41162274026549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12880 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12880]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12880])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12880) (a := (82424682716827 / 100000000000000 : ℝ)) (b := (79947842107 / 50000000000000 : ℝ)) (q := (1115041580843 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12880])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12880])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12880]

theorem cert12880_49 : CellCertificate 12880 (17634588101039 / 200000000000000 : ℝ) (1630771132770473 / 1000000000000000000 : ℝ) (41162274026549 / 1250000000000000 : ℝ)
    (cell12880 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · have h := gap_lower (n := 12880) (a := (82390919792341 / 100000000000000 : ℝ)) (b := (79947842107 / 50000000000000 : ℝ)) (q := (1115043592181 / 50000000000000 : ℝ))
      (E := (cell12880 ⟨49, by decide⟩).energy) (xi := (41162274026549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12880 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12880]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12880])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12880) (a := (82390919792341 / 100000000000000 : ℝ)) (b := (79947842107 / 50000000000000 : ℝ)) (q := (1115043592181 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12880])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12880])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12880]

theorem cert12880_50 : CellCertificate 12880 (17634588101039 / 200000000000000 : ℝ) (1630771132770473 / 1000000000000000000 : ℝ) (41162274026549 / 1250000000000000 : ℝ)
    (cell12880 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · have h := gap_lower (n := 12880) (a := (3294287206957 / 4000000000000 : ℝ)) (b := (79947842107 / 50000000000000 : ℝ)) (q := (2230091209557 / 100000000000000 : ℝ))
      (E := (cell12880 ⟨50, by decide⟩).energy) (xi := (41162274026549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12880 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12880]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12880])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12880) (a := (3294287206957 / 4000000000000 : ℝ)) (b := (79947842107 / 50000000000000 : ℝ)) (q := (2230091209557 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12880])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12880])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12880]

theorem cert12880_51 : CellCertificate 12880 (17634588101039 / 200000000000000 : ℝ) (1630771132770473 / 1000000000000000000 : ℝ) (41162274026549 / 1250000000000000 : ℝ)
    (cell12880 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · have h := gap_lower (n := 12880) (a := (20580865958297 / 25000000000000 : ℝ)) (b := (79947842107 / 50000000000000 : ℝ)) (q := (1115047587731 / 50000000000000 : ℝ))
      (E := (cell12880 ⟨51, by decide⟩).energy) (xi := (41162274026549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12880 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12880]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12880])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12880) (a := (20580865958297 / 25000000000000 : ℝ)) (b := (79947842107 / 50000000000000 : ℝ)) (q := (1115047587731 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12880])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12880])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12880]

theorem cert12880_52 : CellCertificate 12880 (17634588101039 / 200000000000000 : ℝ) (1630771132770473 / 1000000000000000000 : ℝ) (41162274026549 / 1250000000000000 : ℝ)
    (cell12880 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · have h := gap_lower (n := 12880) (a := (41144885370941 / 50000000000000 : ℝ)) (b := (79947842107 / 50000000000000 : ℝ)) (q := (2230099197103 / 100000000000000 : ℝ))
      (E := (cell12880 ⟨52, by decide⟩).energy) (xi := (41162274026549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12880 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12880]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12880])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12880) (a := (41144885370941 / 50000000000000 : ℝ)) (b := (79947842107 / 50000000000000 : ℝ)) (q := (2230099197103 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12880])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12880])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12880]

theorem cert12880_53 : CellCertificate 12880 (17634588101039 / 200000000000000 : ℝ) (1630771132770473 / 1000000000000000000 : ℝ) (41162274026549 / 1250000000000000 : ℝ)
    (cell12880 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · have h := gap_lower (n := 12880) (a := (822561008719 / 1000000000000 : ℝ)) (b := (79947842107 / 50000000000000 : ℝ)) (q := (1115051606137 / 50000000000000 : ℝ))
      (E := (cell12880 ⟨53, by decide⟩).energy) (xi := (41162274026549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12880 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12880]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12880])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12880) (a := (822561008719 / 1000000000000 : ℝ)) (b := (79947842107 / 50000000000000 : ℝ)) (q := (1115051606137 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12880])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12880])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12880]

theorem cert12880_54 : CellCertificate 12880 (17634588101039 / 200000000000000 : ℝ) (1630771132770473 / 1000000000000000000 : ℝ) (41162274026549 / 1250000000000000 : ℝ)
    (cell12880 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · have h := gap_lower (n := 12880) (a := (41111227097637 / 50000000000000 : ℝ)) (b := (79947842107 / 50000000000000 : ℝ)) (q := (2230107217561 / 100000000000000 : ℝ))
      (E := (cell12880 ⟨54, by decide⟩).energy) (xi := (41162274026549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12880 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12880]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12880])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12880) (a := (41111227097637 / 50000000000000 : ℝ)) (b := (79947842107 / 50000000000000 : ℝ)) (q := (2230107217561 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12880])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12880])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12880]

theorem cert12880_55 : CellCertificate 12880 (17634588101039 / 200000000000000 : ℝ) (1630771132770473 / 1000000000000000000 : ℝ) (41162274026549 / 1250000000000000 : ℝ)
    (cell12880 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · have h := gap_lower (n := 12880) (a := (5136801917761 / 6250000000000 : ℝ)) (b := (79947842107 / 50000000000000 : ℝ)) (q := (2230111209339 / 100000000000000 : ℝ))
      (E := (cell12880 ⟨55, by decide⟩).energy) (xi := (41162274026549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12880 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12880]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12880])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12880) (a := (5136801917761 / 6250000000000 : ℝ)) (b := (79947842107 / 50000000000000 : ℝ)) (q := (2230111209339 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12880])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12880])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12880]

theorem cert12880_56 : CellCertificate 12880 (17634588101039 / 200000000000000 : ℝ) (1630771132770473 / 1000000000000000000 : ℝ) (41162274026549 / 1250000000000000 : ℝ)
    (cell12880 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · have h := gap_lower (n := 12880) (a := (82155230310919 / 100000000000000 : ℝ)) (b := (79947842107 / 50000000000000 : ℝ)) (q := (557528810729 / 25000000000000 : ℝ))
      (E := (cell12880 ⟨56, by decide⟩).energy) (xi := (41162274026549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12880 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12880]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12880])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12880) (a := (82155230310919 / 100000000000000 : ℝ)) (b := (79947842107 / 50000000000000 : ℝ)) (q := (557528810729 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12880])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12880])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12880]

theorem cert12880_57 : CellCertificate 12880 (17634588101039 / 200000000000000 : ℝ) (1630771132770473 / 1000000000000000000 : ℝ) (41162274026549 / 1250000000000000 : ℝ)
    (cell12880 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · have h := gap_lower (n := 12880) (a := (5132603315497 / 6250000000000 : ℝ)) (b := (79947842107 / 50000000000000 : ℝ)) (q := (2230119255159 / 100000000000000 : ℝ))
      (E := (cell12880 ⟨57, by decide⟩).energy) (xi := (41162274026549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12880 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12880]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12880])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12880) (a := (5132603315497 / 6250000000000 : ℝ)) (b := (79947842107 / 50000000000000 : ℝ)) (q := (2230119255159 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12880])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12880])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12880]

theorem cert12880_58 : CellCertificate 12880 (17634588101039 / 200000000000000 : ℝ) (1630771132770473 / 1000000000000000000 : ℝ) (41162274026549 / 1250000000000000 : ℝ)
    (cell12880 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · have h := gap_lower (n := 12880) (a := (4104404943393 / 5000000000000 : ℝ)) (b := (79947842107 / 50000000000000 : ℝ)) (q := (89204929673 / 4000000000000 : ℝ))
      (E := (cell12880 ⟨58, by decide⟩).energy) (xi := (41162274026549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12880 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12880]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12880])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12880) (a := (4104404943393 / 5000000000000 : ℝ)) (b := (79947842107 / 50000000000000 : ℝ)) (q := (89204929673 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12880])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12880])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12880]

theorem cert12880_59 : CellCertificate 12880 (17634588101039 / 200000000000000 : ℝ) (1630771132770473 / 1000000000000000000 : ℝ) (41162274026549 / 1250000000000000 : ℝ)
    (cell12880 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · have h := gap_lower (n := 12880) (a := (41027283871683 / 50000000000000 : ℝ)) (b := (79947842107 / 50000000000000 : ℝ)) (q := (2230127257673 / 100000000000000 : ℝ))
      (E := (cell12880 ⟨59, by decide⟩).energy) (xi := (41162274026549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12880 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12880]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12880])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12880) (a := (41027283871683 / 50000000000000 : ℝ)) (b := (79947842107 / 50000000000000 : ℝ)) (q := (2230127257673 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12880])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12880])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12880]

theorem cert12881_40 : CellCertificate 12881 (881702214737919 / 10000000000000000 : ℝ) (407661122223301 / 250000000000000000 : ℝ) (65854404388023 / 2000000000000000 : ℝ)
    (cell12881 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · have h := gap_lower (n := 12881) (a := (16539125213709 / 20000000000000 : ℝ)) (b := (159883123881 / 100000000000000 : ℝ)) (q := (2229933839857 / 100000000000000 : ℝ))
      (E := (cell12881 ⟨40, by decide⟩).energy) (xi := (65854404388023 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12881 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12881]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12881])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12881) (a := (16539125213709 / 20000000000000 : ℝ)) (b := (159883123881 / 100000000000000 : ℝ)) (q := (2229933839857 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12881])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12881])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12881]

theorem cert12881_41 : CellCertificate 12881 (881702214737919 / 10000000000000000 : ℝ) (407661122223301 / 250000000000000000 : ℝ) (65854404388023 / 2000000000000000 : ℝ)
    (cell12881 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · have h := gap_lower (n := 12881) (a := (41330837976157 / 50000000000000 : ℝ)) (b := (159883123881 / 100000000000000 : ℝ)) (q := (2229937888879 / 100000000000000 : ℝ))
      (E := (cell12881 ⟨41, by decide⟩).energy) (xi := (65854404388023 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12881 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12881]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12881])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12881) (a := (41330837976157 / 50000000000000 : ℝ)) (b := (159883123881 / 100000000000000 : ℝ)) (q := (2229937888879 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12881])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12881])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12881]

theorem cert12881_42 : CellCertificate 12881 (881702214737919 / 10000000000000000 : ℝ) (407661122223301 / 250000000000000000 : ℝ) (65854404388023 / 2000000000000000 : ℝ)
    (cell12881 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · have h := gap_lower (n := 12881) (a := (82627749374077 / 100000000000000 : ℝ)) (b := (159883123881 / 100000000000000 : ℝ)) (q := (1114970948493 / 50000000000000 : ℝ))
      (E := (cell12881 ⟨42, by decide⟩).energy) (xi := (65854404388023 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12881 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12881]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12881])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12881) (a := (82627749374077 / 100000000000000 : ℝ)) (b := (159883123881 / 100000000000000 : ℝ)) (q := (1114970948493 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12881])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12881])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12881]

theorem cert12881_43 : CellCertificate 12881 (881702214737919 / 10000000000000000 : ℝ) (407661122223301 / 250000000000000000 : ℝ) (65854404388023 / 2000000000000000 : ℝ)
    (cell12881 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · have h := gap_lower (n := 12881) (a := (82593846304279 / 100000000000000 : ℝ)) (b := (159883123881 / 100000000000000 : ℝ)) (q := (2229945863039 / 100000000000000 : ℝ))
      (E := (cell12881 ⟨43, by decide⟩).energy) (xi := (65854404388023 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12881 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12881]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12881])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12881) (a := (82593846304279 / 100000000000000 : ℝ)) (b := (159883123881 / 100000000000000 : ℝ)) (q := (2229945863039 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12881])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12881])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12881]

theorem cert12881_44 : CellCertificate 12881 (881702214737919 / 10000000000000000 : ℝ) (407661122223301 / 250000000000000000 : ℝ) (65854404388023 / 2000000000000000 : ℝ)
    (cell12881 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · have h := gap_lower (n := 12881) (a := (16511993342703 / 20000000000000 : ℝ)) (b := (159883123881 / 100000000000000 : ℝ)) (q := (69685934481 / 3125000000000 : ℝ))
      (E := (cell12881 ⟨44, by decide⟩).energy) (xi := (65854404388023 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12881 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12881]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12881])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12881) (a := (16511993342703 / 20000000000000 : ℝ)) (b := (159883123881 / 100000000000000 : ℝ)) (q := (69685934481 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12881])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12881])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12881]

theorem cert12881_45 : CellCertificate 12881 (881702214737919 / 10000000000000000 : ℝ) (407661122223301 / 250000000000000000 : ℝ) (65854404388023 / 2000000000000000 : ℝ)
    (cell12881 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · have h := gap_lower (n := 12881) (a := (20631527643131 / 25000000000000 : ℝ)) (b := (159883123881 / 100000000000000 : ℝ)) (q := (2229953898849 / 100000000000000 : ℝ))
      (E := (cell12881 ⟨45, by decide⟩).energy) (xi := (65854404388023 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12881 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12881]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12881])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12881) (a := (20631527643131 / 25000000000000 : ℝ)) (b := (159883123881 / 100000000000000 : ℝ)) (q := (2229953898849 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12881])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12881])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12881]

theorem cert12881_46 : CellCertificate 12881 (881702214737919 / 10000000000000000 : ℝ) (407661122223301 / 250000000000000000 : ℝ) (65854404388023 / 2000000000000000 : ℝ)
    (cell12881 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · have h := gap_lower (n := 12881) (a := (16498455570439 / 20000000000000 : ℝ)) (b := (159883123881 / 100000000000000 : ℝ)) (q := (557489476631 / 25000000000000 : ℝ))
      (E := (cell12881 ⟨46, by decide⟩).energy) (xi := (65854404388023 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12881 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12881]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12881])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12881) (a := (16498455570439 / 20000000000000 : ℝ)) (b := (159883123881 / 100000000000000 : ℝ)) (q := (557489476631 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12881])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12881])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12881]

theorem cert12881_47 : CellCertificate 12881 (881702214737919 / 10000000000000000 : ℝ) (407661122223301 / 250000000000000000 : ℝ) (65854404388023 / 2000000000000000 : ℝ)
    (cell12881 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · have h := gap_lower (n := 12881) (a := (41229234261781 / 50000000000000 : ℝ)) (b := (159883123881 / 100000000000000 : ℝ)) (q := (2229961924483 / 100000000000000 : ℝ))
      (E := (cell12881 ⟨47, by decide⟩).energy) (xi := (65854404388023 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12881 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12881]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12881])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12881) (a := (41229234261781 / 50000000000000 : ℝ)) (b := (159883123881 / 100000000000000 : ℝ)) (q := (2229961924483 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12881])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12881])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12881]

theorem cert12881_48 : CellCertificate 12881 (881702214737919 / 10000000000000000 : ℝ) (407661122223301 / 250000000000000000 : ℝ) (65854404388023 / 2000000000000000 : ℝ)
    (cell12881 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · have h := gap_lower (n := 12881) (a := (16484936511561 / 20000000000000 : ℝ)) (b := (159883123881 / 100000000000000 : ℝ)) (q := (278745736453 / 12500000000000 : ℝ))
      (E := (cell12881 ⟨48, by decide⟩).energy) (xi := (65854404388023 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12881 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12881]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12881])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12881) (a := (16484936511561 / 20000000000000 : ℝ)) (b := (159883123881 / 100000000000000 : ℝ)) (q := (278745736453 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12881])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12881])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12881]

theorem cert12881_49 : CellCertificate 12881 (881702214737919 / 10000000000000000 : ℝ) (407661122223301 / 250000000000000000 : ℝ) (65854404388023 / 2000000000000000 : ℝ)
    (cell12881 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · have h := gap_lower (n := 12881) (a := (10298864990781 / 12500000000000 : ℝ)) (b := (159883123881 / 100000000000000 : ℝ)) (q := (278746240433 / 12500000000000 : ℝ))
      (E := (cell12881 ⟨49, by decide⟩).energy) (xi := (65854404388023 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12881 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12881]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12881])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12881) (a := (10298864990781 / 12500000000000 : ℝ)) (b := (159883123881 / 100000000000000 : ℝ)) (q := (278746240433 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12881])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12881])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12881]

theorem cert12881_50 : CellCertificate 12881 (881702214737919 / 10000000000000000 : ℝ) (407661122223301 / 250000000000000000 : ℝ) (65854404388023 / 2000000000000000 : ℝ)
    (cell12881 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · have h := gap_lower (n := 12881) (a := (41178590300179 / 50000000000000 : ℝ)) (b := (159883123881 / 100000000000000 : ℝ)) (q := (1114986979251 / 50000000000000 : ℝ))
      (E := (cell12881 ⟨50, by decide⟩).energy) (xi := (65854404388023 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12881 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12881]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12881])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12881) (a := (41178590300179 / 50000000000000 : ℝ)) (b := (159883123881 / 100000000000000 : ℝ)) (q := (1114986979251 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12881])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12881])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12881]

theorem cert12881_51 : CellCertificate 12881 (881702214737919 / 10000000000000000 : ℝ) (407661122223301 / 250000000000000000 : ℝ) (65854404388023 / 2000000000000000 : ℝ)
    (cell12881 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · have h := gap_lower (n := 12881) (a := (41161732275873 / 50000000000000 : ℝ)) (b := (159883123881 / 100000000000000 : ℝ)) (q := (139373620933 / 6250000000000 : ℝ))
      (E := (cell12881 ⟨51, by decide⟩).energy) (xi := (65854404388023 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12881 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12881]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12881])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12881) (a := (41161732275873 / 50000000000000 : ℝ)) (b := (159883123881 / 100000000000000 : ℝ)) (q := (139373620933 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12881])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12881])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12881]

theorem cert12881_52 : CellCertificate 12881 (881702214737919 / 10000000000000000 : ℝ) (407661122223301 / 250000000000000000 : ℝ) (65854404388023 / 2000000000000000 : ℝ)
    (cell12881 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · have h := gap_lower (n := 12881) (a := (20572442938041 / 25000000000000 : ℝ)) (b := (159883123881 / 100000000000000 : ℝ)) (q := (2229981967767 / 100000000000000 : ℝ))
      (E := (cell12881 ⟨52, by decide⟩).energy) (xi := (65854404388023 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12881 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12881]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12881])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12881) (a := (20572442938041 / 25000000000000 : ℝ)) (b := (159883123881 / 100000000000000 : ℝ)) (q := (2229981967767 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12881])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12881])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12881]

theorem cert12881_53 : CellCertificate 12881 (881702214737919 / 10000000000000000 : ℝ) (407661122223301 / 250000000000000000 : ℝ) (65854404388023 / 2000000000000000 : ℝ)
    (cell12881 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · have h := gap_lower (n := 12881) (a := (16451220434701 / 20000000000000 : ℝ)) (b := (159883123881 / 100000000000000 : ℝ)) (q := (17421765123 / 781250000000 : ℝ))
      (E := (cell12881 ⟨53, by decide⟩).energy) (xi := (65854404388023 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12881 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12881]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12881])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12881) (a := (16451220434701 / 20000000000000 : ℝ)) (b := (159883123881 / 100000000000000 : ℝ)) (q := (17421765123 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12881])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12881])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12881]

theorem cert12881_54 : CellCertificate 12881 (881702214737919 / 10000000000000000 : ℝ) (407661122223301 / 250000000000000000 : ℝ) (65854404388023 / 2000000000000000 : ℝ)
    (cell12881 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · have h := gap_lower (n := 12881) (a := (82222455787803 / 100000000000000 : ℝ)) (b := (159883123881 / 100000000000000 : ℝ)) (q := (1114994976779 / 50000000000000 : ℝ))
      (E := (cell12881 ⟨54, by decide⟩).energy) (xi := (65854404388023 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12881 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12881]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12881])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12881) (a := (82222455787803 / 100000000000000 : ℝ)) (b := (159883123881 / 100000000000000 : ℝ)) (q := (1114994976779 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12881])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12881])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12881]

theorem cert12881_55 : CellCertificate 12881 (881702214737919 / 10000000000000000 : ℝ) (407661122223301 / 250000000000000000 : ℝ) (65854404388023 / 2000000000000000 : ℝ)
    (cell12881 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · have h := gap_lower (n := 12881) (a := (82188832567231 / 100000000000000 : ℝ)) (b := (159883123881 / 100000000000000 : ℝ)) (q := (2229993958539 / 100000000000000 : ℝ))
      (E := (cell12881 ⟨55, by decide⟩).energy) (xi := (65854404388023 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12881 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12881]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12881])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12881) (a := (82188832567231 / 100000000000000 : ℝ)) (b := (159883123881 / 100000000000000 : ℝ)) (q := (2229993958539 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12881])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12881])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12881]

theorem cert12881_56 : CellCertificate 12881 (881702214737919 / 10000000000000000 : ℝ) (407661122223301 / 250000000000000000 : ℝ) (65854404388023 / 2000000000000000 : ℝ)
    (cell12881 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · have h := gap_lower (n := 12881) (a := (41077616242051 / 50000000000000 : ℝ)) (b := (159883123881 / 100000000000000 : ℝ)) (q := (278749750749 / 12500000000000 : ℝ))
      (E := (cell12881 ⟨56, by decide⟩).energy) (xi := (65854404388023 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12881 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12881]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12881])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12881) (a := (41077616242051 / 50000000000000 : ℝ)) (b := (159883123881 / 100000000000000 : ℝ)) (q := (278749750749 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12881])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12881])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12881]

theorem cert12881_57 : CellCertificate 12881 (881702214737919 / 10000000000000000 : ℝ) (407661122223301 / 250000000000000000 : ℝ) (65854404388023 / 2000000000000000 : ℝ)
    (cell12881 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · have h := gap_lower (n := 12881) (a := (5132603469429 / 6250000000000 : ℝ)) (b := (159883123881 / 100000000000000 : ℝ)) (q := (2230001973623 / 100000000000000 : ℝ))
      (E := (cell12881 ⟨57, by decide⟩).energy) (xi := (65854404388023 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12881 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12881]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12881])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12881) (a := (5132603469429 / 6250000000000 : ℝ)) (b := (159883123881 / 100000000000000 : ℝ)) (q := (2230001973623 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12881])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12881])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12881]

theorem cert12881_58 : CellCertificate 12881 (881702214737919 / 10000000000000000 : ℝ) (407661122223301 / 250000000000000000 : ℝ) (65854404388023 / 2000000000000000 : ℝ)
    (cell12881 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · have h := gap_lower (n := 12881) (a := (16417620324021 / 20000000000000 : ℝ)) (b := (159883123881 / 100000000000000 : ℝ)) (q := (2230006034677 / 100000000000000 : ℝ))
      (E := (cell12881 ⟨58, by decide⟩).energy) (xi := (65854404388023 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12881 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12881]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12881])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12881) (a := (16417620324021 / 20000000000000 : ℝ)) (b := (159883123881 / 100000000000000 : ℝ)) (q := (2230006034677 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12881])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12881])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12881]

theorem cert12881_59 : CellCertificate 12881 (881702214737919 / 10000000000000000 : ℝ) (407661122223301 / 250000000000000000 : ℝ) (65854404388023 / 2000000000000000 : ℝ)
    (cell12881 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · have h := gap_lower (n := 12881) (a := (20513642696137 / 25000000000000 : ℝ)) (b := (159883123881 / 100000000000000 : ℝ)) (q := (557502501803 / 25000000000000 : ℝ))
      (E := (cell12881 ⟨59, by decide⟩).energy) (xi := (65854404388023 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12881 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12881]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12881])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12881) (a := (20513642696137 / 25000000000000 : ℝ)) (b := (159883123881 / 100000000000000 : ℝ)) (q := (557502501803 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12881])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12881])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12881]

theorem cert12882_40 : CellCertificate 12882 (440837514235751 / 5000000000000000 : ℝ) (1630517864684451 / 1000000000000000000 : ℝ) (329245855870859 / 10000000000000000 : ℝ)
    (cell12882 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · have h := gap_lower (n := 12882) (a := (20673905888089 / 25000000000000 : ℝ)) (b := (39967641383 / 25000000000000 : ℝ)) (q := (278727079437 / 12500000000000 : ℝ))
      (E := (cell12882 ⟨40, by decide⟩).energy) (xi := (329245855870859 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12882 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12882]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12882])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12882) (a := (20673905888089 / 25000000000000 : ℝ)) (b := (39967641383 / 25000000000000 : ℝ)) (q := (278727079437 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12882])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12882])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12882]

theorem cert12882_41 : CellCertificate 12882 (440837514235751 / 5000000000000000 : ℝ) (1630517864684451 / 1000000000000000000 : ℝ) (329245855870859 / 10000000000000000 : ℝ)
    (cell12882 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · have h := gap_lower (n := 12882) (a := (82661673732261 / 100000000000000 : ℝ)) (b := (39967641383 / 25000000000000 : ℝ)) (q := (1114910314763 / 50000000000000 : ℝ))
      (E := (cell12882 ⟨41, by decide⟩).energy) (xi := (329245855870859 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12882 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12882]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12882])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12882) (a := (82661673732261 / 100000000000000 : ℝ)) (b := (39967641383 / 25000000000000 : ℝ)) (q := (1114910314763 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12882])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12882])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12882]

theorem cert12882_42 : CellCertificate 12882 (440837514235751 / 5000000000000000 : ℝ) (1630517864684451 / 1000000000000000000 : ℝ) (329245855870859 / 10000000000000000 : ℝ)
    (cell12882 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · have h := gap_lower (n := 12882) (a := (82627747449753 / 100000000000000 : ℝ)) (b := (39967641383 / 25000000000000 : ℝ)) (q := (2229824642089 / 100000000000000 : ℝ))
      (E := (cell12882 ⟨42, by decide⟩).energy) (xi := (329245855870859 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12882 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12882]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12882])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12882) (a := (82627747449753 / 100000000000000 : ℝ)) (b := (39967641383 / 25000000000000 : ℝ)) (q := (2229824642089 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12882])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12882])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12882]

theorem cert12882_43 : CellCertificate 12882 (440837514235751 / 5000000000000000 : ℝ) (1630517864684451 / 1000000000000000000 : ℝ) (329245855870859 / 10000000000000000 : ℝ)
    (cell12882 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · have h := gap_lower (n := 12882) (a := (41296922337639 / 50000000000000 : ℝ)) (b := (39967641383 / 25000000000000 : ℝ)) (q := (1114914336057 / 50000000000000 : ℝ))
      (E := (cell12882 ⟨43, by decide⟩).energy) (xi := (329245855870859 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12882 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12882]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12882])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12882) (a := (41296922337639 / 50000000000000 : ℝ)) (b := (39967641383 / 25000000000000 : ℝ)) (q := (1114914336057 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12882])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12882])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12882]

theorem cert12882_44 : CellCertificate 12882 (440837514235751 / 5000000000000000 : ℝ) (1630517864684451 / 1000000000000000000 : ℝ) (329245855870859 / 10000000000000000 : ℝ)
    (cell12882 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · have h := gap_lower (n := 12882) (a := (20639991344857 / 25000000000000 : ℝ)) (b := (39967641383 / 25000000000000 : ℝ)) (q := (445966531891 / 20000000000000 : ℝ))
      (E := (cell12882 ⟨44, by decide⟩).energy) (xi := (329245855870859 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12882 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12882]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12882])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12882) (a := (20639991344857 / 25000000000000 : ℝ)) (b := (39967641383 / 25000000000000 : ℝ)) (q := (445966531891 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12882])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12882])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12882]

theorem cert12882_45 : CellCertificate 12882 (440837514235751 / 5000000000000000 : ℝ) (1630517864684451 / 1000000000000000000 : ℝ) (329245855870859 / 10000000000000000 : ℝ)
    (cell12882 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · have h := gap_lower (n := 12882) (a := (82526109532947 / 100000000000000 : ℝ)) (b := (39967641383 / 25000000000000 : ℝ)) (q := (445967332283 / 20000000000000 : ℝ))
      (E := (cell12882 ⟨45, by decide⟩).energy) (xi := (329245855870859 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12882 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12882]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12882])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12882) (a := (82526109532947 / 100000000000000 : ℝ)) (b := (39967641383 / 25000000000000 : ℝ)) (q := (445967332283 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12882])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12882])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12882]

theorem cert12882_46 : CellCertificate 12882 (440837514235751 / 5000000000000000 : ℝ) (1630517864684451 / 1000000000000000000 : ℝ) (329245855870859 / 10000000000000000 : ℝ)
    (cell12882 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · have h := gap_lower (n := 12882) (a := (41246138553361 / 50000000000000 : ℝ)) (b := (39967641383 / 25000000000000 : ℝ)) (q := (557460169069 / 25000000000000 : ℝ))
      (E := (cell12882 ⟨46, by decide⟩).energy) (xi := (329245855870859 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12882 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12882]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12882])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12882) (a := (41246138553361 / 50000000000000 : ℝ)) (b := (39967641383 / 25000000000000 : ℝ)) (q := (557460169069 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12882])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12882])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12882]

theorem cert12882_47 : CellCertificate 12882 (440837514235751 / 5000000000000000 : ℝ) (1630517864684451 / 1000000000000000000 : ℝ) (329245855870859 / 10000000000000000 : ℝ)
    (cell12882 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · have h := gap_lower (n := 12882) (a := (8245846807179 / 10000000000000 : ℝ)) (b := (39967641383 / 25000000000000 : ℝ)) (q := (2229844702099 / 100000000000000 : ℝ))
      (E := (cell12882 ⟨47, by decide⟩).energy) (xi := (329245855870859 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12882 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12882]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12882])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12882) (a := (8245846807179 / 10000000000000 : ℝ)) (b := (39967641383 / 25000000000000 : ℝ)) (q := (2229844702099 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12882])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12882])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12882]

theorem cert12882_48 : CellCertificate 12882 (440837514235751 / 5000000000000000 : ℝ) (1630517864684451 / 1000000000000000000 : ℝ) (329245855870859 / 10000000000000000 : ℝ)
    (cell12882 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · have h := gap_lower (n := 12882) (a := (82424682399329 / 100000000000000 : ℝ)) (b := (39967641383 / 25000000000000 : ℝ)) (q := (278731084723 / 12500000000000 : ℝ))
      (E := (cell12882 ⟨48, by decide⟩).energy) (xi := (329245855870859 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12882 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12882]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12882])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12882) (a := (82424682399329 / 100000000000000 : ℝ)) (b := (39967641383 / 25000000000000 : ℝ)) (q := (278731084723 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12882])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12882])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12882]

theorem cert12882_49 : CellCertificate 12882 (440837514235751 / 5000000000000000 : ℝ) (1630517864684451 / 1000000000000000000 : ℝ) (329245855870859 / 10000000000000000 : ℝ)
    (cell12882 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · have h := gap_lower (n := 12882) (a := (41195460030333 / 50000000000000 : ℝ)) (b := (39967641383 / 25000000000000 : ℝ)) (q := (8710362183 / 390625000000 : ℝ))
      (E := (cell12882 ⟨49, by decide⟩).energy) (xi := (329245855870859 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12882 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12882]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12882])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12882) (a := (41195460030333 / 50000000000000 : ℝ)) (b := (39967641383 / 25000000000000 : ℝ)) (q := (8710362183 / 390625000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12882])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12882])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12882]

theorem cert12882_50 : CellCertificate 12882 (440837514235751 / 5000000000000000 : ℝ) (1630517864684451 / 1000000000000000000 : ℝ) (329245855870859 / 10000000000000000 : ℝ)
    (cell12882 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · have h := gap_lower (n := 12882) (a := (82357181027267 / 100000000000000 : ℝ)) (b := (39967641383 / 25000000000000 : ℝ)) (q := (222985670479 / 10000000000000 : ℝ))
      (E := (cell12882 ⟨50, by decide⟩).energy) (xi := (329245855870859 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12882 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12882]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12882])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12882) (a := (82357181027267 / 100000000000000 : ℝ)) (b := (39967641383 / 25000000000000 : ℝ)) (q := (222985670479 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12882])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12882])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12882]

theorem cert12882_51 : CellCertificate 12882 (440837514235751 / 5000000000000000 : ℝ) (1630517864684451 / 1000000000000000000 : ℝ) (329245855870859 / 10000000000000000 : ℝ)
    (cell12882 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · have h := gap_lower (n := 12882) (a := (16464693054149 / 20000000000000 : ℝ)) (b := (39967641383 / 25000000000000 : ℝ)) (q := (557465172943 / 25000000000000 : ℝ))
      (E := (cell12882 ⟨51, by decide⟩).energy) (xi := (329245855870859 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12882 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12882]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12882])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12882) (a := (16464693054149 / 20000000000000 : ℝ)) (b := (39967641383 / 25000000000000 : ℝ)) (q := (557465172943 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12882])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12882])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12882]

theorem cert12882_52 : CellCertificate 12882 (440837514235751 / 5000000000000000 : ℝ) (1630517864684451 / 1000000000000000000 : ℝ) (329245855870859 / 10000000000000000 : ℝ)
    (cell12882 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · have h := gap_lower (n := 12882) (a := (20572443190713 / 25000000000000 : ℝ)) (b := (39967641383 / 25000000000000 : ℝ)) (q := (1114932367923 / 50000000000000 : ℝ))
      (E := (cell12882 ⟨52, by decide⟩).energy) (xi := (329245855870859 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12882 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12882]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12882])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12882) (a := (20572443190713 / 25000000000000 : ℝ)) (b := (39967641383 / 25000000000000 : ℝ)) (q := (1114932367923 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12882])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12882])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12882]

theorem cert12882_53 : CellCertificate 12882 (440837514235751 / 5000000000000000 : ℝ) (1630517864684451 / 1000000000000000000 : ℝ) (329245855870859 / 10000000000000000 : ℝ)
    (cell12882 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · have h := gap_lower (n := 12882) (a := (41128051737741 / 50000000000000 : ℝ)) (b := (39967641383 / 25000000000000 : ℝ)) (q := (2229868715733 / 100000000000000 : ℝ))
      (E := (cell12882 ⟨53, by decide⟩).energy) (xi := (329245855870859 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12882 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12882]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12882])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12882) (a := (41128051737741 / 50000000000000 : ℝ)) (b := (39967641383 / 25000000000000 : ℝ)) (q := (2229868715733 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12882])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12882])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12882]

theorem cert12882_54 : CellCertificate 12882 (440837514235751 / 5000000000000000 : ℝ) (1630517864684451 / 1000000000000000000 : ℝ) (329245855870859 / 10000000000000000 : ℝ)
    (cell12882 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · have h := gap_lower (n := 12882) (a := (82222457380669 / 100000000000000 : ℝ)) (b := (39967641383 / 25000000000000 : ℝ)) (q := (1114936373067 / 50000000000000 : ℝ))
      (E := (cell12882 ⟨54, by decide⟩).energy) (xi := (329245855870859 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12882 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12882]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12882])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12882) (a := (82222457380669 / 100000000000000 : ℝ)) (b := (39967641383 / 25000000000000 : ℝ)) (q := (1114936373067 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12882])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12882])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12882]

theorem cert12882_55 : CellCertificate 12882 (440837514235751 / 5000000000000000 : ℝ) (1630517864684451 / 1000000000000000000 : ℝ) (329245855870859 / 10000000000000000 : ℝ)
    (cell12882 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · have h := gap_lower (n := 12882) (a := (20547208612647 / 25000000000000 : ℝ)) (b := (39967641383 / 25000000000000 : ℝ)) (q := (3567802823 / 160000000000 : ℝ))
      (E := (cell12882 ⟨55, by decide⟩).energy) (xi := (329245855870859 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12882 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12882]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12882])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12882) (a := (20547208612647 / 25000000000000 : ℝ)) (b := (39967641383 / 25000000000000 : ℝ)) (q := (3567802823 / 160000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12882])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12882])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12882]

theorem cert12882_56 : CellCertificate 12882 (440837514235751 / 5000000000000000 : ℝ) (1630517864684451 / 1000000000000000000 : ℝ) (329245855870859 / 10000000000000000 : ℝ)
    (cell12882 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · have h := gap_lower (n := 12882) (a := (82155234657551 / 100000000000000 : ℝ)) (b := (39967641383 / 25000000000000 : ℝ)) (q := (17839046133 / 800000000000 : ℝ))
      (E := (cell12882 ⟨56, by decide⟩).energy) (xi := (329245855870859 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12882 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12882]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12882])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12882) (a := (82155234657551 / 100000000000000 : ℝ)) (b := (39967641383 / 25000000000000 : ℝ)) (q := (17839046133 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12882])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12882])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12882]

theorem cert12882_57 : CellCertificate 12882 (440837514235751 / 5000000000000000 : ℝ) (1630517864684451 / 1000000000000000000 : ℝ) (329245855870859 / 10000000000000000 : ℝ)
    (cell12882 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · have h := gap_lower (n := 12882) (a := (10265207246751 / 12500000000000 : ℝ)) (b := (39967641383 / 25000000000000 : ℝ)) (q := (2229884748843 / 100000000000000 : ℝ))
      (E := (cell12882 ⟨57, by decide⟩).energy) (xi := (329245855870859 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12882 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12882]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12882])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12882) (a := (10265207246751 / 12500000000000 : ℝ)) (b := (39967641383 / 25000000000000 : ℝ)) (q := (2229884748843 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12882])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12882])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12882]

theorem cert12882_58 : CellCertificate 12882 (440837514235751 / 5000000000000000 : ℝ) (1630517864684451 / 1000000000000000000 : ℝ) (329245855870859 / 10000000000000000 : ℝ)
    (cell12882 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · have h := gap_lower (n := 12882) (a := (20522026093137 / 25000000000000 : ℝ)) (b := (39967641383 / 25000000000000 : ℝ)) (q := (2229888765969 / 100000000000000 : ℝ))
      (E := (cell12882 ⟨58, by decide⟩).energy) (xi := (329245855870859 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12882 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12882]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12882])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12882) (a := (20522026093137 / 25000000000000 : ℝ)) (b := (39967641383 / 25000000000000 : ℝ)) (q := (2229888765969 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12882])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12882])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12882]

theorem cert12882_59 : CellCertificate 12882 (440837514235751 / 5000000000000000 : ℝ) (1630517864684451 / 1000000000000000000 : ℝ) (329245855870859 / 10000000000000000 : ℝ)
    (cell12882 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · have h := gap_lower (n := 12882) (a := (41027286912947 / 50000000000000 : ℝ)) (b := (39967641383 / 25000000000000 : ℝ)) (q := (1114946406811 / 50000000000000 : ℝ))
      (E := (cell12882 ⟨59, by decide⟩).energy) (xi := (329245855870859 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12882 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12882]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12882])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12882) (a := (41027286912947 / 50000000000000 : ℝ)) (b := (39967641383 / 25000000000000 : ℝ)) (q := (1114946406811 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12882])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12882])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12882]

theorem cert12883_40 : CellCertificate 12883 (110205980781469 / 1250000000000000 : ℝ) (815195630069817 / 500000000000000000 : ℝ) (16460984700177 / 500000000000000 : ℝ)
    (cell12883 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · have h := gap_lower (n := 12883) (a := (82695621036993 / 100000000000000 : ℝ)) (b := (79929004583 / 50000000000000 : ℝ)) (q := (55742485703 / 2500000000000 : ℝ))
      (E := (cell12883 ⟨40, by decide⟩).energy) (xi := (16460984700177 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12883 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12883]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12883])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12883) (a := (82695621036993 / 100000000000000 : ℝ)) (b := (79929004583 / 50000000000000 : ℝ)) (q := (55742485703 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12883])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12883])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12883]

theorem cert12883_41 : CellCertificate 12883 (110205980781469 / 1250000000000000 : ℝ) (815195630069817 / 500000000000000000 : ℝ) (16460984700177 / 500000000000000 : ℝ)
    (cell12883 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · have h := gap_lower (n := 12883) (a := (82661671513 / 100000000000 : ℝ)) (b := (79929004583 / 50000000000000 : ℝ)) (q := (2229703425981 / 100000000000000 : ℝ))
      (E := (cell12883 ⟨41, by decide⟩).energy) (xi := (16460984700177 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12883 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12883]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12883])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12883) (a := (82661671513 / 100000000000 : ℝ)) (b := (79929004583 / 50000000000000 : ℝ)) (q := (2229703425981 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12883])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12883])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12883]

theorem cert12883_42 : CellCertificate 12883 (110205980781469 / 1250000000000000 : ℝ) (815195630069817 / 500000000000000000 : ℝ) (16460984700177 / 500000000000000 : ℝ)
    (cell12883 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · have h := gap_lower (n := 12883) (a := (41313872763093 / 50000000000000 : ℝ)) (b := (79929004583 / 50000000000000 : ℝ)) (q := (2229707443059 / 100000000000000 : ℝ))
      (E := (cell12883 ⟨42, by decide⟩).energy) (xi := (16460984700177 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12883 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12883]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12883])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12883) (a := (41313872763093 / 50000000000000 : ℝ)) (b := (79929004583 / 50000000000000 : ℝ)) (q := (2229707443059 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12883])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12883])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12883]

theorem cert12883_43 : CellCertificate 12883 (110205980781469 / 1250000000000000 : ℝ) (815195630069817 / 500000000000000000 : ℝ) (16460984700177 / 500000000000000 : ℝ)
    (cell12883 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · have h := gap_lower (n := 12883) (a := (82593843046997 / 100000000000000 : ℝ)) (b := (79929004583 / 50000000000000 : ℝ)) (q := (2229711478283 / 100000000000000 : ℝ))
      (E := (cell12883 ⟨43, by decide⟩).energy) (xi := (16460984700177 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12883 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12883]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12883])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12883) (a := (82593843046997 / 100000000000000 : ℝ)) (b := (79929004583 / 50000000000000 : ℝ)) (q := (2229711478283 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12883])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12883])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12883]

theorem cert12883_44 : CellCertificate 12883 (110205980781469 / 1250000000000000 : ℝ) (815195630069817 / 500000000000000000 : ℝ) (16460984700177 / 500000000000000 : ℝ)
    (cell12883 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · have h := gap_lower (n := 12883) (a := (82559964046027 / 100000000000000 : ℝ)) (b := (79929004583 / 50000000000000 : ℝ)) (q := (445943094301 / 20000000000000 : ℝ))
      (E := (cell12883 ⟨44, by decide⟩).energy) (xi := (16460984700177 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12883 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12883]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12883])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12883) (a := (82559964046027 / 100000000000000 : ℝ)) (b := (79929004583 / 50000000000000 : ℝ)) (q := (445943094301 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12883])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12883])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12883]

theorem cert12883_45 : CellCertificate 12883 (110205980781469 / 1250000000000000 : ℝ) (815195630069817 / 500000000000000000 : ℝ) (16460984700177 / 500000000000000 : ℝ)
    (cell12883 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · have h := gap_lower (n := 12883) (a := (4126305424701 / 5000000000000 : ℝ)) (b := (79929004583 / 50000000000000 : ℝ)) (q := (2229719480029 / 100000000000000 : ℝ))
      (E := (cell12883 ⟨45, by decide⟩).energy) (xi := (16460984700177 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12883 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12883]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12883])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12883) (a := (4126305424701 / 5000000000000 : ℝ)) (b := (79929004583 / 50000000000000 : ℝ)) (q := (2229719480029 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12883])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12883])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12883]

theorem cert12883_46 : CellCertificate 12883 (110205980781469 / 1250000000000000 : ℝ) (815195630069817 / 500000000000000000 : ℝ) (16460984700177 / 500000000000000 : ℝ)
    (cell12883 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · have h := gap_lower (n := 12883) (a := (16498455272373 / 20000000000000 : ℝ)) (b := (79929004583 / 50000000000000 : ℝ)) (q := (557430875533 / 25000000000000 : ℝ))
      (E := (cell12883 ⟨46, by decide⟩).energy) (xi := (16460984700177 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12883 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12883]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12883])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12883) (a := (16498455272373 / 20000000000000 : ℝ)) (b := (79929004583 / 50000000000000 : ℝ)) (q := (557430875533 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12883])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12883])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12883]

theorem cert12883_47 : CellCertificate 12883 (110205980781469 / 1250000000000000 : ℝ) (815195630069817 / 500000000000000000 : ℝ) (16460984700177 / 500000000000000 : ℝ)
    (cell12883 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · have h := gap_lower (n := 12883) (a := (41229233810299 / 50000000000000 : ℝ)) (b := (79929004583 / 50000000000000 : ℝ)) (q := (2229727476951 / 100000000000000 : ℝ))
      (E := (cell12883 ⟨47, by decide⟩).energy) (xi := (16460984700177 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12883 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12883]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12883])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12883) (a := (41229233810299 / 50000000000000 : ℝ)) (b := (79929004583 / 50000000000000 : ℝ)) (q := (2229727476951 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12883])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12883])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12883]

theorem cert12883_48 : CellCertificate 12883 (110205980781469 / 1250000000000000 : ℝ) (815195630069817 / 500000000000000000 : ℝ) (16460984700177 / 500000000000000 : ℝ)
    (cell12883 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · have h := gap_lower (n := 12883) (a := (82424682241399 / 100000000000000 : ℝ)) (b := (79929004583 / 50000000000000 : ℝ)) (q := (2229731520169 / 100000000000000 : ℝ))
      (E := (cell12883 ⟨48, by decide⟩).energy) (xi := (16460984700177 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12883 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12883]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12883])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12883) (a := (82424682241399 / 100000000000000 : ℝ)) (b := (79929004583 / 50000000000000 : ℝ)) (q := (2229731520169 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12883])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12883])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12883]

theorem cert12883_49 : CellCertificate 12883 (110205980781469 / 1250000000000000 : ℝ) (815195630069817 / 500000000000000000 : ℝ) (16460984700177 / 500000000000000 : ℝ)
    (cell12883 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · have h := gap_lower (n := 12883) (a := (41195460097797 / 50000000000000 : ℝ)) (b := (79929004583 / 50000000000000 : ℝ)) (q := (2229735511541 / 100000000000000 : ℝ))
      (E := (cell12883 ⟨49, by decide⟩).energy) (xi := (16460984700177 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12883 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12883]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12883])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12883) (a := (41195460097797 / 50000000000000 : ℝ)) (b := (79929004583 / 50000000000000 : ℝ)) (q := (2229735511541 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12883])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12883])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12883]

theorem cert12883_50 : CellCertificate 12883 (110205980781469 / 1250000000000000 : ℝ) (815195630069817 / 500000000000000000 : ℝ) (16460984700177 / 500000000000000 : ℝ)
    (cell12883 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · have h := gap_lower (n := 12883) (a := (20589295363663 / 25000000000000 : ℝ)) (b := (79929004583 / 50000000000000 : ℝ)) (q := (111486975371 / 5000000000000 : ℝ))
      (E := (cell12883 ⟨50, by decide⟩).energy) (xi := (16460984700177 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12883 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12883]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12883])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12883) (a := (20589295363663 / 25000000000000 : ℝ)) (b := (79929004583 / 50000000000000 : ℝ)) (q := (111486975371 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12883])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12883])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12883]

theorem cert12883_51 : CellCertificate 12883 (110205980781469 / 1250000000000000 : ℝ) (815195630069817 / 500000000000000000 : ℝ) (16460984700177 / 500000000000000 : ℝ)
    (cell12883 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · have h := gap_lower (n := 12883) (a := (10290433248773 / 12500000000000 : ℝ)) (b := (79929004583 / 50000000000000 : ℝ)) (q := (111487175251 / 5000000000000 : ℝ))
      (E := (cell12883 ⟨51, by decide⟩).energy) (xi := (16460984700177 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12883 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12883]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12883])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12883) (a := (10290433248773 / 12500000000000 : ℝ)) (b := (79929004583 / 50000000000000 : ℝ)) (q := (111487175251 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12883])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12883])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12883]

theorem cert12883_52 : CellCertificate 12883 (110205980781469 / 1250000000000000 : ℝ) (815195630069817 / 500000000000000000 : ℝ) (16460984700177 / 500000000000000 : ℝ)
    (cell12883 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · have h := gap_lower (n := 12883) (a := (16457954754789 / 20000000000000 : ℝ)) (b := (79929004583 / 50000000000000 : ℝ)) (q := (1114873780193 / 50000000000000 : ℝ))
      (E := (cell12883 ⟨52, by decide⟩).energy) (xi := (16460984700177 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12883 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12883]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12883])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12883) (a := (16457954754789 / 20000000000000 : ℝ)) (b := (79929004583 / 50000000000000 : ℝ)) (q := (1114873780193 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12883])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12883])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12883]

theorem cert12883_53 : CellCertificate 12883 (110205980781469 / 1250000000000000 : ℝ) (815195630069817 / 500000000000000000 : ℝ) (16460984700177 / 500000000000000 : ℝ)
    (cell12883 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · have h := gap_lower (n := 12883) (a := (82256104777829 / 100000000000000 : ℝ)) (b := (79929004583 / 50000000000000 : ℝ)) (q := (2229751552243 / 100000000000000 : ℝ))
      (E := (cell12883 ⟨53, by decide⟩).energy) (xi := (16460984700177 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12883 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12883]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12883])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12883) (a := (82256104777829 / 100000000000000 : ℝ)) (b := (79929004583 / 50000000000000 : ℝ)) (q := (2229751552243 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12883])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12883])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12883]

theorem cert12883_54 : CellCertificate 12883 (110205980781469 / 1250000000000000 : ℝ) (815195630069817 / 500000000000000000 : ℝ) (16460984700177 / 500000000000000 : ℝ)
    (cell12883 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · have h := gap_lower (n := 12883) (a := (82222458973871 / 100000000000000 : ℝ)) (b := (79929004583 / 50000000000000 : ℝ)) (q := (557438884049 / 25000000000000 : ℝ))
      (E := (cell12883 ⟨54, by decide⟩).energy) (xi := (16460984700177 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12883 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12883]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12883])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12883) (a := (82222458973871 / 100000000000000 : ℝ)) (b := (79929004583 / 50000000000000 : ℝ)) (q := (557438884049 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12883])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12883])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12883]

theorem cert12883_55 : CellCertificate 12883 (110205980781469 / 1250000000000000 : ℝ) (815195630069817 / 500000000000000000 : ℝ) (16460984700177 / 500000000000000 : ℝ)
    (cell12883 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · have h := gap_lower (n := 12883) (a := (41094418167123 / 50000000000000 : ℝ)) (b := (79929004583 / 50000000000000 : ℝ)) (q := (1114879783867 / 50000000000000 : ℝ))
      (E := (cell12883 ⟨55, by decide⟩).energy) (xi := (16460984700177 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12883 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12883]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12883])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12883) (a := (41094418167123 / 50000000000000 : ℝ)) (b := (79929004583 / 50000000000000 : ℝ)) (q := (1114879783867 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12883])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12883])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12883]

theorem cert12883_56 : CellCertificate 12883 (110205980781469 / 1250000000000000 : ℝ) (815195630069817 / 500000000000000000 : ℝ) (16460984700177 / 500000000000000 : ℝ)
    (cell12883 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · have h := gap_lower (n := 12883) (a := (82155236831267 / 100000000000000 : ℝ)) (b := (79929004583 / 50000000000000 : ℝ)) (q := (557440895989 / 25000000000000 : ℝ))
      (E := (cell12883 ⟨56, by decide⟩).energy) (xi := (16460984700177 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12883 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12883]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12883])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12883) (a := (82155236831267 / 100000000000000 : ℝ)) (b := (79929004583 / 50000000000000 : ℝ)) (q := (557440895989 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12883])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12883])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12883]

theorem cert12883_57 : CellCertificate 12883 (110205980781469 / 1250000000000000 : ℝ) (815195630069817 / 500000000000000000 : ℝ) (16460984700177 / 500000000000000 : ℝ)
    (cell12883 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · have h := gap_lower (n := 12883) (a := (41060830218693 / 50000000000000 : ℝ)) (b := (79929004583 / 50000000000000 : ℝ)) (q := (1114883790409 / 50000000000000 : ℝ))
      (E := (cell12883 ⟨57, by decide⟩).energy) (xi := (16460984700177 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12883 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12883]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12883])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12883) (a := (41060830218693 / 50000000000000 : ℝ)) (b := (79929004583 / 50000000000000 : ℝ)) (q := (1114883790409 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12883])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12883])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12883]

theorem cert12883_58 : CellCertificate 12883 (110205980781469 / 1250000000000000 : ℝ) (815195630069817 / 500000000000000000 : ℝ) (16460984700177 / 500000000000000 : ℝ)
    (cell12883 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · have h := gap_lower (n := 12883) (a := (82088107125189 / 100000000000000 : ℝ)) (b := (79929004583 / 50000000000000 : ℝ)) (q := (2229771613263 / 100000000000000 : ℝ))
      (E := (cell12883 ⟨58, by decide⟩).energy) (xi := (16460984700177 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12883 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12883]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12883])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12883) (a := (82088107125189 / 100000000000000 : ℝ)) (b := (79929004583 / 50000000000000 : ℝ)) (q := (2229771613263 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12883])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12883])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12883]

theorem cert12883_59 : CellCertificate 12883 (110205980781469 / 1250000000000000 : ℝ) (815195630069817 / 500000000000000000 : ℝ) (16460984700177 / 500000000000000 : ℝ)
    (cell12883 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · have h := gap_lower (n := 12883) (a := (82054576867403 / 100000000000000 : ℝ)) (b := (79929004583 / 50000000000000 : ℝ)) (q := (2229775617697 / 100000000000000 : ℝ))
      (E := (cell12883 ⟨59, by decide⟩).energy) (xi := (16460984700177 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12883 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12883]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12883])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12883) (a := (82054576867403 / 100000000000000 : ℝ)) (b := (79929004583 / 50000000000000 : ℝ)) (q := (2229775617697 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12883])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12883])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12883]

theorem cert12884_40 : CellCertificate 12884 (881620668077721 / 10000000000000000 : ℝ) (407566168813543 / 250000000000000000 : ℝ) (164596768168537 / 5000000000000000 : ℝ)
    (cell12884 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · have h := gap_lower (n := 12884) (a := (82695618522457 / 100000000000000 : ℝ)) (b := (159845454783 / 100000000000000 : ℝ)) (q := (2229582276493 / 100000000000000 : ℝ))
      (E := (cell12884 ⟨40, by decide⟩).energy) (xi := (164596768168537 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12884 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12884]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12884])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12884) (a := (82695618522457 / 100000000000000 : ℝ)) (b := (159845454783 / 100000000000000 : ℝ)) (q := (2229582276493 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12884])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12884])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12884]

theorem cert12884_41 : CellCertificate 12884 (881620668077721 / 10000000000000000 : ℝ) (407566168813543 / 250000000000000000 : ℝ) (164596768168537 / 5000000000000000 : ℝ)
    (cell12884 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · have h := gap_lower (n := 12884) (a := (8266166929453 / 10000000000000 : ℝ)) (b := (159845454783 / 100000000000000 : ℝ)) (q := (445917255649 / 20000000000000 : ℝ))
      (E := (cell12884 ⟨41, by decide⟩).energy) (xi := (164596768168537 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12884 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12884]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12884])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12884) (a := (8266166929453 / 10000000000000 : ℝ)) (b := (159845454783 / 100000000000000 : ℝ)) (q := (445917255649 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12884])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12884])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12884]

theorem cert12884_42 : CellCertificate 12884 (881620668077721 / 10000000000000000 : ℝ) (407566168813543 / 250000000000000000 : ℝ) (164596768168537 / 5000000000000000 : ℝ)
    (cell12884 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · have h := gap_lower (n := 12884) (a := (41313871801687 / 50000000000000 : ℝ)) (b := (159845454783 / 100000000000000 : ℝ)) (q := (2229590299899 / 100000000000000 : ℝ))
      (E := (cell12884 ⟨42, by decide⟩).energy) (xi := (164596768168537 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12884 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12884]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12884])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12884) (a := (41313871801687 / 50000000000000 : ℝ)) (b := (159845454783 / 100000000000000 : ℝ)) (q := (2229590299899 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12884])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12884])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12884]

theorem cert12884_43 : CellCertificate 12884 (881620668077721 / 10000000000000000 : ℝ) (407566168813543 / 250000000000000000 : ℝ) (164596768168537 / 5000000000000000 : ℝ)
    (cell12884 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · have h := gap_lower (n := 12884) (a := (20648460354859 / 25000000000000 : ℝ)) (b := (159845454783 / 100000000000000 : ℝ)) (q := (2229594281547 / 100000000000000 : ℝ))
      (E := (cell12884 ⟨43, by decide⟩).energy) (xi := (164596768168537 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12884 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12884]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12884])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12884) (a := (20648460354859 / 25000000000000 : ℝ)) (b := (159845454783 / 100000000000000 : ℝ)) (q := (2229594281547 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12884])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12884])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12884]

theorem cert12884_44 : CellCertificate 12884 (881620668077721 / 10000000000000000 : ℝ) (407566168813543 / 250000000000000000 : ℝ) (164596768168537 / 5000000000000000 : ℝ)
    (cell12884 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · have h := gap_lower (n := 12884) (a := (2579998834791 / 3125000000000 : ℝ)) (b := (159845454783 / 100000000000000 : ℝ)) (q := (557399570171 / 25000000000000 : ℝ))
      (E := (cell12884 ⟨44, by decide⟩).energy) (xi := (164596768168537 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12884 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12884]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12884])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12884) (a := (2579998834791 / 3125000000000 : ℝ)) (b := (159845454783 / 100000000000000 : ℝ)) (q := (557399570171 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12884])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12884])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12884]

theorem cert12884_45 : CellCertificate 12884 (881620668077721 / 10000000000000000 : ℝ) (407566168813543 / 250000000000000000 : ℝ) (164596768168537 / 5000000000000000 : ℝ)
    (cell12884 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · have h := gap_lower (n := 12884) (a := (322367607249 / 390625000000 : ℝ)) (b := (159845454783 / 100000000000000 : ℝ)) (q := (2229602295807 / 100000000000000 : ℝ))
      (E := (cell12884 ⟨45, by decide⟩).energy) (xi := (164596768168537 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12884 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12884]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12884])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12884) (a := (322367607249 / 390625000000 : ℝ)) (b := (159845454783 / 100000000000000 : ℝ)) (q := (2229602295807 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12884])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12884])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12884]

theorem cert12884_46 : CellCertificate 12884 (881620668077721 / 10000000000000000 : ℝ) (407566168813543 / 250000000000000000 : ℝ) (164596768168537 / 5000000000000000 : ℝ)
    (cell12884 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · have h := gap_lower (n := 12884) (a := (82492275617623 / 100000000000000 : ℝ)) (b := (159845454783 / 100000000000000 : ℝ)) (q := (2229606325191 / 100000000000000 : ℝ))
      (E := (cell12884 ⟨46, by decide⟩).energy) (xi := (164596768168537 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12884 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12884]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12884])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12884) (a := (82492275617623 / 100000000000000 : ℝ)) (b := (159845454783 / 100000000000000 : ℝ)) (q := (2229606325191 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12884])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12884])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12884]

theorem cert12884_47 : CellCertificate 12884 (881620668077721 / 10000000000000000 : ℝ) (407566168813543 / 250000000000000000 : ℝ) (164596768168537 / 5000000000000000 : ℝ)
    (cell12884 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · have h := gap_lower (n := 12884) (a := (16491693433997 / 20000000000000 : ℝ)) (b := (159845454783 / 100000000000000 : ℝ)) (q := (222961030797 / 10000000000000 : ℝ))
      (E := (cell12884 ⟨47, by decide⟩).energy) (xi := (164596768168537 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12884 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12884]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12884])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12884) (a := (16491693433997 / 20000000000000 : ℝ)) (b := (159845454783 / 100000000000000 : ℝ)) (q := (222961030797 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12884])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12884])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12884]

theorem cert12884_48 : CellCertificate 12884 (881620668077721 / 10000000000000000 : ℝ) (407566168813543 / 250000000000000000 : ℝ) (164596768168537 / 5000000000000000 : ℝ)
    (cell12884 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · have h := gap_lower (n := 12884) (a := (82424682084013 / 100000000000000 : ℝ)) (b := (159845454783 / 100000000000000 : ℝ)) (q := (17836914407 / 800000000000 : ℝ))
      (E := (cell12884 ⟨48, by decide⟩).energy) (xi := (164596768168537 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12884 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12884]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12884])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12884) (a := (82424682084013 / 100000000000000 : ℝ)) (b := (159845454783 / 100000000000000 : ℝ)) (q := (17836914407 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12884])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12884])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12884]

theorem cert12884_49 : CellCertificate 12884 (881620668077721 / 10000000000000000 : ℝ) (407566168813543 / 250000000000000000 : ℝ) (164596768168537 / 5000000000000000 : ℝ)
    (cell12884 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · have h := gap_lower (n := 12884) (a := (10298865041379 / 12500000000000 : ℝ)) (b := (159845454783 / 100000000000000 : ℝ)) (q := (2229618360519 / 100000000000000 : ℝ))
      (E := (cell12884 ⟨49, by decide⟩).energy) (xi := (164596768168537 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12884 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12884]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12884])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12884) (a := (10298865041379 / 12500000000000 : ℝ)) (b := (159845454783 / 100000000000000 : ℝ)) (q := (2229618360519 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12884])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12884])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12884]

theorem cert12884_50 : CellCertificate 12884 (881620668077721 / 10000000000000000 : ℝ) (407566168813543 / 250000000000000000 : ℝ) (164596768168537 / 5000000000000000 : ℝ)
    (cell12884 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · have h := gap_lower (n := 12884) (a := (82357181882511 / 100000000000000 : ℝ)) (b := (159845454783 / 100000000000000 : ℝ)) (q := (557405591599 / 25000000000000 : ℝ))
      (E := (cell12884 ⟨50, by decide⟩).energy) (xi := (164596768168537 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12884 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12884]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12884])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12884) (a := (82357181882511 / 100000000000000 : ℝ)) (b := (159845454783 / 100000000000000 : ℝ)) (q := (557405591599 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12884])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12884])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12884]

theorem cert12884_51 : CellCertificate 12884 (881620668077721 / 10000000000000000 : ℝ) (407566168813543 / 250000000000000000 : ℝ) (164596768168537 / 5000000000000000 : ℝ)
    (cell12884 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · have h := gap_lower (n := 12884) (a := (5145216669379 / 6250000000000 : ℝ)) (b := (159845454783 / 100000000000000 : ℝ)) (q := (222962637467 / 10000000000000 : ℝ))
      (E := (cell12884 ⟨51, by decide⟩).energy) (xi := (164596768168537 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12884 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12884]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12884])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12884) (a := (5145216669379 / 6250000000000 : ℝ)) (b := (159845454783 / 100000000000000 : ℝ)) (q := (222962637467 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12884])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12884])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12884]

theorem cert12884_52 : CellCertificate 12884 (881620668077721 / 10000000000000000 : ℝ) (407566168813543 / 250000000000000000 : ℝ) (164596768168537 / 5000000000000000 : ℝ)
    (cell12884 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · have h := gap_lower (n := 12884) (a := (20572443696361 / 25000000000000 : ℝ)) (b := (159845454783 / 100000000000000 : ℝ)) (q := (1114815191171 / 50000000000000 : ℝ))
      (E := (cell12884 ⟨52, by decide⟩).energy) (xi := (164596768168537 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12884 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12884]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12884])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12884) (a := (20572443696361 / 25000000000000 : ℝ)) (b := (159845454783 / 100000000000000 : ℝ)) (q := (1114815191171 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12884])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12884])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12884]

theorem cert12884_53 : CellCertificate 12884 (881620668077721 / 10000000000000000 : ℝ) (407566168813543 / 250000000000000000 : ℝ) (164596768168537 / 5000000000000000 : ℝ)
    (cell12884 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · have h := gap_lower (n := 12884) (a := (82256106080547 / 100000000000000 : ℝ)) (b := (159845454783 / 100000000000000 : ℝ)) (q := (445926877241 / 20000000000000 : ℝ))
      (E := (cell12884 ⟨53, by decide⟩).energy) (xi := (164596768168537 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12884 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12884]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12884])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12884) (a := (82256106080547 / 100000000000000 : ℝ)) (b := (159845454783 / 100000000000000 : ℝ)) (q := (445926877241 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12884])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12884])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12884]

theorem cert12884_54 : CellCertificate 12884 (881620668077721 / 10000000000000000 : ℝ) (407566168813543 / 250000000000000000 : ℝ) (164596768168537 / 5000000000000000 : ℝ)
    (cell12884 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · have h := gap_lower (n := 12884) (a := (8222246056741 / 10000000000000 : ℝ)) (b := (159845454783 / 100000000000000 : ℝ)) (q := (2229638382837 / 100000000000000 : ℝ))
      (E := (cell12884 ⟨54, by decide⟩).energy) (xi := (164596768168537 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12884 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12884]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12884])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12884) (a := (8222246056741 / 10000000000000 : ℝ)) (b := (159845454783 / 100000000000000 : ℝ)) (q := (2229638382837 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12884])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12884])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12884]

theorem cert12884_55 : CellCertificate 12884 (881620668077721 / 10000000000000000 : ℝ) (407566168813543 / 250000000000000000 : ℝ) (164596768168537 / 5000000000000000 : ℝ)
    (cell12884 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · have h := gap_lower (n := 12884) (a := (41094419109103 / 50000000000000 : ℝ)) (b := (159845454783 / 100000000000000 : ℝ)) (q := (445928473723 / 20000000000000 : ℝ))
      (E := (cell12884 ⟨55, by decide⟩).energy) (xi := (164596768168537 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12884 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12884]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12884])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12884) (a := (41094419109103 / 50000000000000 : ℝ)) (b := (159845454783 / 100000000000000 : ℝ)) (q := (445928473723 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12884])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12884])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12884]

theorem cert12884_56 : CellCertificate 12884 (881620668077721 / 10000000000000000 : ℝ) (407566168813543 / 250000000000000000 : ℝ) (164596768168537 / 5000000000000000 : ℝ)
    (cell12884 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · have h := gap_lower (n := 12884) (a := (82155239005251 / 100000000000000 : ℝ)) (b := (159845454783 / 100000000000000 : ℝ)) (q := (2229646398843 / 100000000000000 : ℝ))
      (E := (cell12884 ⟨56, by decide⟩).energy) (xi := (164596768168537 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12884 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12884]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12884])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12884) (a := (82155239005251 / 100000000000000 : ℝ)) (b := (159845454783 / 100000000000000 : ℝ)) (q := (2229646398843 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12884])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12884])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12884]

theorem cert12884_57 : CellCertificate 12884 (881620668077721 / 10000000000000000 : ℝ) (407566168813543 / 250000000000000000 : ℝ) (164596768168537 / 5000000000000000 : ℝ)
    (cell12884 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · have h := gap_lower (n := 12884) (a := (16424332580199 / 20000000000000 : ℝ)) (b := (159845454783 / 100000000000000 : ℝ)) (q := (2229650410387 / 100000000000000 : ℝ))
      (E := (cell12884 ⟨57, by decide⟩).energy) (xi := (164596768168537 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12884 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12884]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12884])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12884) (a := (16424332580199 / 20000000000000 : ℝ)) (b := (159845454783 / 100000000000000 : ℝ)) (q := (2229650410387 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12884])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12884])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12884]

theorem cert12884_58 : CellCertificate 12884 (881620668077721 / 10000000000000000 : ℝ) (407566168813543 / 250000000000000000 : ℝ) (164596768168537 / 5000000000000000 : ℝ)
    (cell12884 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · have h := gap_lower (n := 12884) (a := (20522027469507 / 25000000000000 : ℝ)) (b := (159845454783 / 100000000000000 : ℝ)) (q := (2229654398999 / 100000000000000 : ℝ))
      (E := (cell12884 ⟨58, by decide⟩).energy) (xi := (164596768168537 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12884 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12884]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12884])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12884) (a := (20522027469507 / 25000000000000 : ℝ)) (b := (159845454783 / 100000000000000 : ℝ)) (q := (2229654398999 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12884])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12884])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12884]

theorem cert12884_59 : CellCertificate 12884 (881620668077721 / 10000000000000000 : ℝ) (407566168813543 / 250000000000000000 : ℝ) (164596768168537 / 5000000000000000 : ℝ)
    (cell12884 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · have h := gap_lower (n := 12884) (a := (3282183196363 / 4000000000000 : ℝ)) (b := (159845454783 / 100000000000000 : ℝ)) (q := (557414604859 / 25000000000000 : ℝ))
      (E := (cell12884 ⟨59, by decide⟩).energy) (xi := (164596768168537 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12884 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12884]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12884])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12884) (a := (3282183196363 / 4000000000000 : ℝ)) (b := (159845454783 / 100000000000000 : ℝ)) (q := (557414604859 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12884])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12884])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12884]

theorem cert12885_40 : CellCertificate 12885 (440796746974231 / 5000000000000000 : ℝ) (1630138110023487 / 1000000000000000000 : ℝ) (41145922858797 / 1250000000000000 : ℝ)
    (cell12885 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · have h := gap_lower (n := 12885) (a := (82695616008747 / 100000000000000 : ℝ)) (b := (79916451191 / 50000000000000 : ℝ)) (q := (2229465121853 / 100000000000000 : ℝ))
      (E := (cell12885 ⟨40, by decide⟩).energy) (xi := (41145922858797 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12885 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12885]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12885])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12885) (a := (82695616008747 / 100000000000000 : ℝ)) (b := (79916451191 / 50000000000000 : ℝ)) (q := (2229465121853 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12885])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12885])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12885]

theorem cert12885_41 : CellCertificate 12885 (440796746974231 / 5000000000000000 : ℝ) (1630138110023487 / 1000000000000000000 : ℝ) (41145922858797 / 1250000000000000 : ℝ)
    (cell12885 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · have h := gap_lower (n := 12885) (a := (82661667076851 / 100000000000000 : ℝ)) (b := (79916451191 / 50000000000000 : ℝ)) (q := (557367281883 / 25000000000000 : ℝ))
      (E := (cell12885 ⟨41, by decide⟩).energy) (xi := (41145922858797 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12885 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12885]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12885])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12885) (a := (82661667076851 / 100000000000000 : ℝ)) (b := (79916451191 / 50000000000000 : ℝ)) (q := (557367281883 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12885])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12885])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12885]

theorem cert12885_42 : CellCertificate 12885 (440796746974231 / 5000000000000000 : ℝ) (1630138110023487 / 1000000000000000000 : ℝ) (41145922858797 / 1250000000000000 : ℝ)
    (cell12885 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · have h := gap_lower (n := 12885) (a := (41313870840659 / 50000000000000 : ℝ)) (b := (79916451191 / 50000000000000 : ℝ)) (q := (2229473153797 / 100000000000000 : ℝ))
      (E := (cell12885 ⟨42, by decide⟩).energy) (xi := (41145922858797 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12885 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12885]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12885])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12885) (a := (41313870840659 / 50000000000000 : ℝ)) (b := (79916451191 / 50000000000000 : ℝ)) (q := (2229473153797 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12885])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12885])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12885]

theorem cert12885_43 : CellCertificate 12885 (440796746974231 / 5000000000000000 : ℝ) (1630138110023487 / 1000000000000000000 : ℝ) (41145922858797 / 1250000000000000 : ℝ)
    (cell12885 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · have h := gap_lower (n := 12885) (a := (82593839792597 / 100000000000000 : ℝ)) (b := (79916451191 / 50000000000000 : ℝ)) (q := (1114738570369 / 50000000000000 : ℝ))
      (E := (cell12885 ⟨43, by decide⟩).energy) (xi := (41145922858797 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12885 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12885]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12885])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12885) (a := (82593839792597 / 100000000000000 : ℝ)) (b := (79916451191 / 50000000000000 : ℝ)) (q := (1114738570369 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12885])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12885])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12885]

theorem cert12885_44 : CellCertificate 12885 (440796746974231 / 5000000000000000 : ℝ) (1630138110023487 / 1000000000000000000 : ℝ) (41145922858797 / 1250000000000000 : ℝ)
    (cell12885 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · have h := gap_lower (n := 12885) (a := (41279980690641 / 50000000000000 : ℝ)) (b := (79916451191 / 50000000000000 : ℝ)) (q := (2229481145853 / 100000000000000 : ℝ))
      (E := (cell12885 ⟨44, by decide⟩).energy) (xi := (41145922858797 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12885 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12885]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12885])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12885) (a := (41279980690641 / 50000000000000 : ℝ)) (b := (79916451191 / 50000000000000 : ℝ)) (q := (2229481145853 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12885])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12885])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12885]

theorem cert12885_45 : CellCertificate 12885 (440796746974231 / 5000000000000000 : ℝ) (1630138110023487 / 1000000000000000000 : ℝ) (41145922858797 / 1250000000000000 : ℝ)
    (cell12885 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · have h := gap_lower (n := 12885) (a := (41263053209059 / 50000000000000 : ℝ)) (b := (79916451191 / 50000000000000 : ℝ)) (q := (1114742583817 / 50000000000000 : ℝ))
      (E := (cell12885 ⟨45, by decide⟩).energy) (xi := (41145922858797 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12885 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12885]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12885])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12885) (a := (41263053209059 / 50000000000000 : ℝ)) (b := (79916451191 / 50000000000000 : ℝ)) (q := (1114742583817 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12885])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12885])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12885]

theorem cert12885_46 : CellCertificate 12885 (440796746974231 / 5000000000000000 : ℝ) (1630138110023487 / 1000000000000000000 : ℝ) (41145922858797 / 1250000000000000 : ℝ)
    (cell12885 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · have h := gap_lower (n := 12885) (a := (20623068718499 / 25000000000000 : ℝ)) (b := (79916451191 / 50000000000000 : ℝ)) (q := (2229489145451 / 100000000000000 : ℝ))
      (E := (cell12885 ⟨46, by decide⟩).energy) (xi := (41145922858797 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12885 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12885]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12885])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12885) (a := (20623068718499 / 25000000000000 : ℝ)) (b := (79916451191 / 50000000000000 : ℝ)) (q := (2229489145451 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12885])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12885])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12885]

theorem cert12885_47 : CellCertificate 12885 (440796746974231 / 5000000000000000 : ℝ) (1630138110023487 / 1000000000000000000 : ℝ) (41145922858797 / 1250000000000000 : ℝ)
    (cell12885 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · have h := gap_lower (n := 12885) (a := (82458466719953 / 100000000000000 : ℝ)) (b := (79916451191 / 50000000000000 : ℝ)) (q := (557373298789 / 25000000000000 : ℝ))
      (E := (cell12885 ⟨47, by decide⟩).energy) (xi := (41145922858797 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12885 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12885]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12885])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12885) (a := (82458466719953 / 100000000000000 : ℝ)) (b := (79916451191 / 50000000000000 : ℝ)) (q := (557373298789 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12885])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12885])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12885]

theorem cert12885_48 : CellCertificate 12885 (440796746974231 / 5000000000000000 : ℝ) (1630138110023487 / 1000000000000000000 : ℝ) (41145922858797 / 1250000000000000 : ℝ)
    (cell12885 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · have h := gap_lower (n := 12885) (a := (20606170481793 / 25000000000000 : ℝ)) (b := (79916451191 / 50000000000000 : ℝ)) (q := (2229497196761 / 100000000000000 : ℝ))
      (E := (cell12885 ⟨48, by decide⟩).energy) (xi := (41145922858797 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12885 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12885]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12885])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12885) (a := (20606170481793 / 25000000000000 : ℝ)) (b := (79916451191 / 50000000000000 : ℝ)) (q := (2229497196761 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12885])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12885])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12885]

theorem cert12885_49 : CellCertificate 12885 (440796746974231 / 5000000000000000 : ℝ) (1630138110023487 / 1000000000000000000 : ℝ) (41145922858797 / 1250000000000000 : ℝ)
    (cell12885 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · have h := gap_lower (n := 12885) (a := (82390920466979 / 100000000000000 : ℝ)) (b := (79916451191 / 50000000000000 : ℝ)) (q := (2229501206807 / 100000000000000 : ℝ))
      (E := (cell12885 ⟨49, by decide⟩).energy) (xi := (41145922858797 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12885 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12885]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12885])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12885) (a := (82390920466979 / 100000000000000 : ℝ)) (b := (79916451191 / 50000000000000 : ℝ)) (q := (2229501206807 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12885])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12885])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12885]

theorem cert12885_50 : CellCertificate 12885 (440796746974231 / 5000000000000000 : ℝ) (1630138110023487 / 1000000000000000000 : ℝ) (41145922858797 / 1250000000000000 : ℝ)
    (cell12885 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · have h := gap_lower (n := 12885) (a := (16471436462169 / 20000000000000 : ℝ)) (b := (79916451191 / 50000000000000 : ℝ)) (q := (2229505222717 / 100000000000000 : ℝ))
      (E := (cell12885 ⟨50, by decide⟩).energy) (xi := (41145922858797 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12885 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12885]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12885])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12885) (a := (16471436462169 / 20000000000000 : ℝ)) (b := (79916451191 / 50000000000000 : ℝ)) (q := (2229505222717 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12885])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12885])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12885]

theorem cert12885_51 : CellCertificate 12885 (440796746974231 / 5000000000000000 : ℝ) (1630138110023487 / 1000000000000000000 : ℝ) (41145922858797 / 1250000000000000 : ℝ)
    (cell12885 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · have h := gap_lower (n := 12885) (a := (82323467430383 / 100000000000000 : ℝ)) (b := (79916451191 / 50000000000000 : ℝ)) (q := (2229509182679 / 100000000000000 : ℝ))
      (E := (cell12885 ⟨51, by decide⟩).energy) (xi := (41145922858797 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12885 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12885]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12885])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12885) (a := (82323467430383 / 100000000000000 : ℝ)) (b := (79916451191 / 50000000000000 : ℝ)) (q := (2229509182679 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12885])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12885])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12885]

theorem cert12885_52 : CellCertificate 12885 (440796746974231 / 5000000000000000 : ℝ) (1630138110023487 / 1000000000000000000 : ℝ) (41145922858797 / 1250000000000000 : ℝ)
    (cell12885 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · have h := gap_lower (n := 12885) (a := (20572443949337 / 25000000000000 : ℝ)) (b := (79916451191 / 50000000000000 : ℝ)) (q := (557378300429 / 25000000000000 : ℝ))
      (E := (cell12885 ⟨52, by decide⟩).energy) (xi := (41145922858797 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12885 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12885]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12885])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12885) (a := (20572443949337 / 25000000000000 : ℝ)) (b := (79916451191 / 50000000000000 : ℝ)) (q := (557378300429 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12885])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12885])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12885]

theorem cert12885_53 : CellCertificate 12885 (440796746974231 / 5000000000000000 : ℝ) (1630138110023487 / 1000000000000000000 : ℝ) (41145922858797 / 1250000000000000 : ℝ)
    (cell12885 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · have h := gap_lower (n := 12885) (a := (20564026845909 / 25000000000000 : ℝ)) (b := (79916451191 / 50000000000000 : ℝ)) (q := (1114758608809 / 50000000000000 : ℝ))
      (E := (cell12885 ⟨53, by decide⟩).energy) (xi := (41145922858797 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12885 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12885]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12885])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12885) (a := (20564026845909 / 25000000000000 : ℝ)) (b := (79916451191 / 50000000000000 : ℝ)) (q := (1114758608809 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12885])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12885])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12885]

theorem cert12885_54 : CellCertificate 12885 (440796746974231 / 5000000000000000 : ℝ) (1630138110023487 / 1000000000000000000 : ℝ) (41145922858797 / 1250000000000000 : ℝ)
    (cell12885 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · have h := gap_lower (n := 12885) (a := (20555615540321 / 25000000000000 : ℝ)) (b := (79916451191 / 50000000000000 : ℝ)) (q := (278690153371 / 12500000000000 : ℝ))
      (E := (cell12885 ⟨54, by decide⟩).energy) (xi := (41145922858797 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12885 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12885]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12885])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12885) (a := (20555615540321 / 25000000000000 : ℝ)) (b := (79916451191 / 50000000000000 : ℝ)) (q := (278690153371 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12885])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12885])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12885]

theorem cert12885_55 : CellCertificate 12885 (440796746974231 / 5000000000000000 : ℝ) (1630138110023487 / 1000000000000000000 : ℝ) (41145922858797 / 1250000000000000 : ℝ)
    (cell12885 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · have h := gap_lower (n := 12885) (a := (82188840102467 / 100000000000000 : ℝ)) (b := (79916451191 / 50000000000000 : ℝ)) (q := (2229525226137 / 100000000000000 : ℝ))
      (E := (cell12885 ⟨55, by decide⟩).energy) (xi := (41145922858797 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12885 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12885]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12885])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12885) (a := (82188840102467 / 100000000000000 : ℝ)) (b := (79916451191 / 50000000000000 : ℝ)) (q := (2229525226137 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12885])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12885])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12885]

theorem cert12885_56 : CellCertificate 12885 (440796746974231 / 5000000000000000 : ℝ) (1630138110023487 / 1000000000000000000 : ℝ) (41145922858797 / 1250000000000000 : ℝ)
    (cell12885 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · have h := gap_lower (n := 12885) (a := (82155241179501 / 100000000000000 : ℝ)) (b := (79916451191 / 50000000000000 : ℝ)) (q := (222952927043 / 10000000000000 : ℝ))
      (E := (cell12885 ⟨56, by decide⟩).energy) (xi := (41145922858797 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12885 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12885]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12885])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12885) (a := (82155241179501 / 100000000000000 : ℝ)) (b := (79916451191 / 50000000000000 : ℝ)) (q := (222952927043 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12885])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12885])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12885]

theorem cert12885_57 : CellCertificate 12885 (440796746974231 / 5000000000000000 : ℝ) (1630138110023487 / 1000000000000000000 : ℝ) (41145922858797 / 1250000000000000 : ℝ)
    (cell12885 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · have h := gap_lower (n := 12885) (a := (82121665364837 / 100000000000000 : ℝ)) (b := (79916451191 / 50000000000000 : ℝ)) (q := (2229533237549 / 100000000000000 : ℝ))
      (E := (cell12885 ⟨57, by decide⟩).energy) (xi := (41145922858797 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12885 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12885]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12885])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12885) (a := (82121665364837 / 100000000000000 : ℝ)) (b := (79916451191 / 50000000000000 : ℝ)) (q := (2229533237549 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12885])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12885])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12885]

theorem cert12885_58 : CellCertificate 12885 (440796746974231 / 5000000000000000 : ℝ) (1630138110023487 / 1000000000000000000 : ℝ) (41145922858797 / 1250000000000000 : ℝ)
    (cell12885 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · have h := gap_lower (n := 12885) (a := (16417622526213 / 20000000000000 : ℝ)) (b := (79916451191 / 50000000000000 : ℝ)) (q := (2229537300737 / 100000000000000 : ℝ))
      (E := (cell12885 ⟨58, by decide⟩).energy) (xi := (41145922858797 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12885 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12885]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12885])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12885) (a := (16417622526213 / 20000000000000 : ℝ)) (b := (79916451191 / 50000000000000 : ℝ)) (q := (2229537300737 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12885])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12885])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12885]

theorem cert12885_59 : CellCertificate 12885 (440796746974231 / 5000000000000000 : ℝ) (1630138110023487 / 1000000000000000000 : ℝ) (41145922858797 / 1250000000000000 : ℝ)
    (cell12885 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · have h := gap_lower (n := 12885) (a := (82054582950911 / 100000000000000 : ℝ)) (b := (79916451191 / 50000000000000 : ℝ)) (q := (2229541278049 / 100000000000000 : ℝ))
      (E := (cell12885 ⟨59, by decide⟩).energy) (xi := (41145922858797 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12885 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12885]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12885])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12885) (a := (82054582950911 / 100000000000000 : ℝ)) (b := (79916451191 / 50000000000000 : ℝ)) (q := (2229541278049 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12885])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12885])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12885]

theorem cert12886_40 : CellCertificate 12886 (881566323863029 / 10000000000000000 : ℝ) (1630011564443 / 1000000000000000 : ℝ) (164570616801181 / 5000000000000000 : ℝ)
    (cell12886 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · have h := gap_lower (n := 12886) (a := (82695613495863 / 100000000000000 : ℝ)) (b := (39955087991 / 25000000000000 : ℝ)) (q := (2229348022963 / 100000000000000 : ℝ))
      (E := (cell12886 ⟨40, by decide⟩).energy) (xi := (164570616801181 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12886 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12886]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12886])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12886) (a := (82695613495863 / 100000000000000 : ℝ)) (b := (39955087991 / 25000000000000 : ℝ)) (q := (2229348022963 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12886])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12886])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12886]

theorem cert12886_41 : CellCertificate 12886 (881566323863029 / 10000000000000000 : ℝ) (1630011564443 / 1000000000000000 : ℝ) (164570616801181 / 5000000000000000 : ℝ)
    (cell12886 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · have h := gap_lower (n := 12886) (a := (82661664859963 / 100000000000000 : ℝ)) (b := (39955087991 / 25000000000000 : ℝ)) (q := (2229352032629 / 100000000000000 : ℝ))
      (E := (cell12886 ⟨41, by decide⟩).energy) (xi := (164570616801181 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12886 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12886]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12886])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12886) (a := (82661664859963 / 100000000000000 : ℝ)) (b := (39955087991 / 25000000000000 : ℝ)) (q := (2229352032629 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12886])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12886])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12886]

theorem cert12886_42 : CellCertificate 12886 (881566323863029 / 10000000000000000 : ℝ) (1630011564443 / 1000000000000000 : ℝ) (164570616801181 / 5000000000000000 : ℝ)
    (cell12886 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · have h := gap_lower (n := 12886) (a := (41313869880009 / 50000000000000 : ℝ)) (b := (39955087991 / 25000000000000 : ℝ)) (q := (2229356004753 / 100000000000000 : ℝ))
      (E := (cell12886 ⟨42, by decide⟩).energy) (xi := (164570616801181 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12886 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12886]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12886])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12886) (a := (41313869880009 / 50000000000000 : ℝ)) (b := (39955087991 / 25000000000000 : ℝ)) (q := (2229356004753 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12886])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12886])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12886]

theorem cert12886_43 : CellCertificate 12886 (881566323863029 / 10000000000000000 : ℝ) (1630011564443 / 1000000000000000 : ℝ) (164570616801181 / 5000000000000000 : ℝ)
    (cell12886 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · have h := gap_lower (n := 12886) (a := (82593838166477 / 100000000000000 : ℝ)) (b := (39955087991 / 25000000000000 : ℝ)) (q := (111468002793 / 5000000000000 : ℝ))
      (E := (cell12886 ⟨43, by decide⟩).energy) (xi := (164570616801181 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12886 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12886]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12886])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12886) (a := (82593838166477 / 100000000000000 : ℝ)) (b := (39955087991 / 25000000000000 : ℝ)) (q := (111468002793 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12886])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12886])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12886]

theorem cert12886_44 : CellCertificate 12886 (881566323863029 / 10000000000000000 : ℝ) (1630011564443 / 1000000000000000 : ℝ) (164570616801181 / 5000000000000000 : ℝ)
    (cell12886 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · have h := gap_lower (n := 12886) (a := (82559960049937 / 100000000000000 : ℝ)) (b := (39955087991 / 25000000000000 : ℝ)) (q := (222936406701 / 10000000000000 : ℝ))
      (E := (cell12886 ⟨44, by decide⟩).energy) (xi := (164570616801181 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12886 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12886]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12886])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12886) (a := (82559960049937 / 100000000000000 : ℝ)) (b := (39955087991 / 25000000000000 : ℝ)) (q := (222936406701 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12886])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12886])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12886]

theorem cert12886_45 : CellCertificate 12886 (881566323863029 / 10000000000000000 : ℝ) (1630011564443 / 1000000000000000 : ℝ) (164570616801181 / 5000000000000000 : ℝ)
    (cell12886 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · have h := gap_lower (n := 12886) (a := (82526105381141 / 100000000000000 : ℝ)) (b := (39955087991 / 25000000000000 : ℝ)) (q := (2229368036627 / 100000000000000 : ℝ))
      (E := (cell12886 ⟨45, by decide⟩).energy) (xi := (164570616801181 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12886 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12886]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12886])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12886) (a := (82526105381141 / 100000000000000 : ℝ)) (b := (39955087991 / 25000000000000 : ℝ)) (q := (2229368036627 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12886])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12886])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12886]

theorem cert12886_46 : CellCertificate 12886 (881566323863029 / 10000000000000000 : ℝ) (1630011564443 / 1000000000000000 : ℝ) (164570616801181 / 5000000000000000 : ℝ)
    (cell12886 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · have h := gap_lower (n := 12886) (a := (10311534266373 / 12500000000000 : ℝ)) (b := (39955087991 / 25000000000000 : ℝ)) (q := (89174883229 / 4000000000000 : ℝ))
      (E := (cell12886 ⟨46, by decide⟩).energy) (xi := (164570616801181 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12886 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12886]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12886])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12886) (a := (10311534266373 / 12500000000000 : ℝ)) (b := (39955087991 / 25000000000000 : ℝ)) (q := (89174883229 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12886])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12886])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12886]

theorem cert12886_47 : CellCertificate 12886 (881566323863029 / 10000000000000000 : ℝ) (1630011564443 / 1000000000000000 : ℝ) (164570616801181 / 5000000000000000 : ℝ)
    (cell12886 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · have h := gap_lower (n := 12886) (a := (82458466270501 / 100000000000000 : ℝ)) (b := (39955087991 / 25000000000000 : ℝ)) (q := (111468803979 / 5000000000000 : ℝ))
      (E := (cell12886 ⟨47, by decide⟩).energy) (xi := (164570616801181 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12886 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12886]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12886])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12886) (a := (82458466270501 / 100000000000000 : ℝ)) (b := (39955087991 / 25000000000000 : ℝ)) (q := (111468803979 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12886])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12886])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12886]

theorem cert12886_48 : CellCertificate 12886 (881566323863029 / 10000000000000000 : ℝ) (1630011564443 / 1000000000000000 : ℝ) (164570616801181 / 5000000000000000 : ℝ)
    (cell12886 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · have h := gap_lower (n := 12886) (a := (20606170442719 / 25000000000000 : ℝ)) (b := (39955087991 / 25000000000000 : ℝ)) (q := (6966812781 / 312500000000 : ℝ))
      (E := (cell12886 ⟨48, by decide⟩).energy) (xi := (164570616801181 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12886 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12886]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12886])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12886) (a := (20606170442719 / 25000000000000 : ℝ)) (b := (39955087991 / 25000000000000 : ℝ)) (q := (6966812781 / 312500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12886])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12886])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12886]

theorem cert12886_49 : CellCertificate 12886 (881566323863029 / 10000000000000000 : ℝ) (1630011564443 / 1000000000000000 : ℝ) (164570616801181 / 5000000000000000 : ℝ)
    (cell12886 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · have h := gap_lower (n := 12886) (a := (82390920603437 / 100000000000000 : ℝ)) (b := (39955087991 / 25000000000000 : ℝ)) (q := (557346012601 / 25000000000000 : ℝ))
      (E := (cell12886 ⟨49, by decide⟩).energy) (xi := (164570616801181 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12886 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12886]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12886])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12886) (a := (82390920603437 / 100000000000000 : ℝ)) (b := (39955087991 / 25000000000000 : ℝ)) (q := (557346012601 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12886])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12886])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12886]

theorem cert12886_50 : CellCertificate 12886 (881566323863029 / 10000000000000000 : ℝ) (1630011564443 / 1000000000000000 : ℝ) (164570616801181 / 5000000000000000 : ℝ)
    (cell12886 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · have h := gap_lower (n := 12886) (a := (16471436547931 / 20000000000000 : ℝ)) (b := (39955087991 / 25000000000000 : ℝ)) (q := (1114694038191 / 50000000000000 : ℝ))
      (E := (cell12886 ⟨50, by decide⟩).energy) (xi := (164570616801181 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12886 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12886]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12886])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12886) (a := (16471436547931 / 20000000000000 : ℝ)) (b := (39955087991 / 25000000000000 : ℝ)) (q := (1114694038191 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12886])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12886])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12886]

theorem cert12886_51 : CellCertificate 12886 (881566323863029 / 10000000000000000 : ℝ) (1630011564443 / 1000000000000000 : ℝ) (164570616801181 / 5000000000000000 : ℝ)
    (cell12886 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · have h := gap_lower (n := 12886) (a := (82323468151143 / 100000000000000 : ℝ)) (b := (39955087991 / 25000000000000 : ℝ)) (q := (1114696053057 / 50000000000000 : ℝ))
      (E := (cell12886 ⟨51, by decide⟩).energy) (xi := (164570616801181 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12886 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12886]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12886])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12886) (a := (82323468151143 / 100000000000000 : ℝ)) (b := (39955087991 / 25000000000000 : ℝ)) (q := (1114696053057 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12886])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12886])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12886]

theorem cert12886_52 : CellCertificate 12886 (881566323863029 / 10000000000000000 : ℝ) (1630011564443 / 1000000000000000 : ℝ) (164570616801181 / 5000000000000000 : ℝ)
    (cell12886 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · have h := gap_lower (n := 12886) (a := (41144888404829 / 50000000000000 : ℝ)) (b := (39955087991 / 25000000000000 : ℝ)) (q := (2229396077551 / 100000000000000 : ℝ))
      (E := (cell12886 ⟨52, by decide⟩).energy) (xi := (164570616801181 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12886 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12886]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12886])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12886) (a := (41144888404829 / 50000000000000 : ℝ)) (b := (39955087991 / 25000000000000 : ℝ)) (q := (2229396077551 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12886])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12886])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12886]

theorem cert12886_53 : CellCertificate 12886 (881566323863029 / 10000000000000000 : ℝ) (1630011564443 / 1000000000000000 : ℝ) (164570616801181 / 5000000000000000 : ℝ)
    (cell12886 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · have h := gap_lower (n := 12886) (a := (10282013585887 / 12500000000000 : ℝ)) (b := (39955087991 / 25000000000000 : ℝ)) (q := (2229400105553 / 100000000000000 : ℝ))
      (E := (cell12886 ⟨53, by decide⟩).energy) (xi := (164570616801181 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12886 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12886]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12886])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12886) (a := (10282013585887 / 12500000000000 : ℝ)) (b := (39955087991 / 25000000000000 : ℝ)) (q := (2229400105553 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12886])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12886])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12886]

theorem cert12886_54 : CellCertificate 12886 (881566323863029 / 10000000000000000 : ℝ) (1630011564443 / 1000000000000000 : ℝ) (164570616801181 / 5000000000000000 : ℝ)
    (cell12886 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · have h := gap_lower (n := 12886) (a := (41111231877747 / 50000000000000 : ℝ)) (b := (39955087991 / 25000000000000 : ℝ)) (q := (1114702063839 / 50000000000000 : ℝ))
      (E := (cell12886 ⟨54, by decide⟩).energy) (xi := (164570616801181 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12886 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12886]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12886])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12886) (a := (41111231877747 / 50000000000000 : ℝ)) (b := (39955087991 / 25000000000000 : ℝ)) (q := (1114702063839 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12886])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12886])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12886]

theorem cert12886_55 : CellCertificate 12886 (881566323863029 / 10000000000000000 : ℝ) (1630011564443 / 1000000000000000 : ℝ) (164570616801181 / 5000000000000000 : ℝ)
    (cell12886 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · have h := gap_lower (n := 12886) (a := (8218884198703 / 10000000000000 : ℝ)) (b := (39955087991 / 25000000000000 : ℝ)) (q := (2229408140297 / 100000000000000 : ℝ))
      (E := (cell12886 ⟨55, by decide⟩).energy) (xi := (164570616801181 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12886 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12886]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12886])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12886) (a := (8218884198703 / 10000000000000 : ℝ)) (b := (39955087991 / 25000000000000 : ℝ)) (q := (2229408140297 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12886])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12886])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12886]

theorem cert12886_56 : CellCertificate 12886 (881566323863029 / 10000000000000000 : ℝ) (1630011564443 / 1000000000000000 : ℝ) (164570616801181 / 5000000000000000 : ℝ)
    (cell12886 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · have h := gap_lower (n := 12886) (a := (82155243354017 / 100000000000000 : ℝ)) (b := (39955087991 / 25000000000000 : ℝ)) (q := (278676517447 / 12500000000000 : ℝ))
      (E := (cell12886 ⟨56, by decide⟩).energy) (xi := (164570616801181 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12886 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12886]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12886])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12886) (a := (82155243354017 / 100000000000000 : ℝ)) (b := (39955087991 / 25000000000000 : ℝ)) (q := (278676517447 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12886])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12886])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12886]

theorem cert12886_57 : CellCertificate 12886 (881566323863029 / 10000000000000000 : ℝ) (1630011564443 / 1000000000000000 : ℝ) (164570616801181 / 5000000000000000 : ℝ)
    (cell12886 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · have h := gap_lower (n := 12886) (a := (8212166782891 / 10000000000000 : ℝ)) (b := (39955087991 / 25000000000000 : ℝ)) (q := (222941612147 / 10000000000000 : ℝ))
      (E := (cell12886 ⟨57, by decide⟩).energy) (xi := (164570616801181 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12886 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12886]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12886])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12886) (a := (8212166782891 / 10000000000000 : ℝ)) (b := (39955087991 / 25000000000000 : ℝ)) (q := (222941612147 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12886])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12886])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12886]

theorem cert12886_58 : CellCertificate 12886 (881566323863029 / 10000000000000000 : ℝ) (1630011564443 / 1000000000000000 : ℝ) (164570616801181 / 5000000000000000 : ℝ)
    (cell12886 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · have h := gap_lower (n := 12886) (a := (82088115384299 / 100000000000000 : ℝ)) (b := (39955087991 / 25000000000000 : ℝ)) (q := (1114710070459 / 50000000000000 : ℝ))
      (E := (cell12886 ⟨58, by decide⟩).energy) (xi := (164570616801181 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12886 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12886]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12886])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12886) (a := (82088115384299 / 100000000000000 : ℝ)) (b := (39955087991 / 25000000000000 : ℝ)) (q := (1114710070459 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12886])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12886])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12886]

theorem cert12886_59 : CellCertificate 12886 (881566323863029 / 10000000000000000 : ℝ) (1630011564443 / 1000000000000000 : ℝ) (164570616801181 / 5000000000000000 : ℝ)
    (cell12886 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · have h := gap_lower (n := 12886) (a := (8205458599291 / 10000000000000 : ℝ)) (b := (39955087991 / 25000000000000 : ℝ)) (q := (2229424193537 / 100000000000000 : ℝ))
      (E := (cell12886 ⟨59, by decide⟩).energy) (xi := (164570616801181 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12886 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12886]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12886])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12886) (a := (8205458599291 / 10000000000000 : ℝ)) (b := (39955087991 / 25000000000000 : ℝ)) (q := (2229424193537 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12886])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12886])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12886]

theorem cert12887_40 : CellCertificate 12887 (35261566312819 / 400000000000000 : ℝ) (1629885038508137 / 1000000000000000000 : ℝ) (329115088531949 / 10000000000000000 : ℝ)
    (cell12887 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · have h := gap_lower (n := 12887) (a := (16539122196761 / 20000000000000 : ℝ)) (b := (159807803527 / 100000000000000 : ℝ)) (q := (2229230921061 / 100000000000000 : ℝ))
      (E := (cell12887 ⟨40, by decide⟩).energy) (xi := (329115088531949 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12887 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12887]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12887])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12887) (a := (16539122196761 / 20000000000000 : ℝ)) (b := (159807803527 / 100000000000000 : ℝ)) (q := (2229230921061 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12887])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12887])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12887]

theorem cert12887_41 : CellCertificate 12887 (35261566312819 / 400000000000000 : ℝ) (1629885038508137 / 1000000000000000000 : ℝ) (329115088531949 / 10000000000000000 : ℝ)
    (cell12887 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · have h := gap_lower (n := 12887) (a := (16532332528773 / 20000000000000 : ℝ)) (b := (159807803527 / 100000000000000 : ℝ)) (q := (8916939739 / 400000000000 : ℝ))
      (E := (cell12887 ⟨41, by decide⟩).energy) (xi := (329115088531949 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12887 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12887]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12887])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12887) (a := (16532332528773 / 20000000000000 : ℝ)) (b := (159807803527 / 100000000000000 : ℝ)) (q := (8916939739 / 400000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12887])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12887])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12887]

theorem cert12887_42 : CellCertificate 12887 (35261566312819 / 400000000000000 : ℝ) (1629885038508137 / 1000000000000000000 : ℝ) (329115088531949 / 10000000000000000 : ℝ)
    (cell12887 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · have h := gap_lower (n := 12887) (a := (82627737839473 / 100000000000000 : ℝ)) (b := (159807803527 / 100000000000000 : ℝ)) (q := (111461945579 / 5000000000000 : ℝ))
      (E := (cell12887 ⟨42, by decide⟩).energy) (xi := (329115088531949 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12887 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12887]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12887])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12887) (a := (82627737839473 / 100000000000000 : ℝ)) (b := (159807803527 / 100000000000000 : ℝ)) (q := (111461945579 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12887])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12887])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12887]

theorem cert12887_43 : CellCertificate 12887 (35261566312819 / 400000000000000 : ℝ) (1629885038508137 / 1000000000000000000 : ℝ) (329115088531949 / 10000000000000000 : ℝ)
    (cell12887 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · have h := gap_lower (n := 12887) (a := (82593836541077 / 100000000000000 : ℝ)) (b := (159807803527 / 100000000000000 : ℝ)) (q := (2229242968077 / 100000000000000 : ℝ))
      (E := (cell12887 ⟨43, by decide⟩).energy) (xi := (329115088531949 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12887 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12887]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12887])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12887) (a := (82593836541077 / 100000000000000 : ℝ)) (b := (159807803527 / 100000000000000 : ℝ)) (q := (2229242968077 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12887])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12887])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12887]

theorem cert12887_44 : CellCertificate 12887 (35261566312819 / 400000000000000 : ℝ) (1629885038508137 / 1000000000000000000 : ℝ) (329115088531949 / 10000000000000000 : ℝ)
    (cell12887 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · have h := gap_lower (n := 12887) (a := (20639989679819 / 25000000000000 : ℝ)) (b := (159807803527 / 100000000000000 : ℝ)) (q := (2229246926441 / 100000000000000 : ℝ))
      (E := (cell12887 ⟨44, by decide⟩).energy) (xi := (329115088531949 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12887 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12887]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12887])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12887) (a := (20639989679819 / 25000000000000 : ℝ)) (b := (159807803527 / 100000000000000 : ℝ)) (q := (2229246926441 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12887])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12887])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12887]

theorem cert12887_45 : CellCertificate 12887 (35261566312819 / 400000000000000 : ℝ) (1629885038508137 / 1000000000000000000 : ℝ) (329115088531949 / 10000000000000000 : ℝ)
    (cell12887 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · have h := gap_lower (n := 12887) (a := (16505220868963 / 20000000000000 : ℝ)) (b := (159807803527 / 100000000000000 : ℝ)) (q := (222925096167 / 10000000000000 : ℝ))
      (E := (cell12887 ⟨45, by decide⟩).energy) (xi := (329115088531949 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12887 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12887]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12887])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12887) (a := (16505220868963 / 20000000000000 : ℝ)) (b := (159807803527 / 100000000000000 : ℝ)) (q := (222925096167 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12887])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12887])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12887]

theorem cert12887_46 : CellCertificate 12887 (35261566312819 / 400000000000000 : ℝ) (1629885038508137 / 1000000000000000000 : ℝ) (329115088531949 / 10000000000000000 : ℝ)
    (cell12887 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · have h := gap_lower (n := 12887) (a := (41246136694293 / 50000000000000 : ℝ)) (b := (159807803527 / 100000000000000 : ℝ)) (q := (2229254954297 / 100000000000000 : ℝ))
      (E := (cell12887 ⟨46, by decide⟩).energy) (xi := (329115088531949 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12887 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12887]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12887])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12887) (a := (41246136694293 / 50000000000000 : ℝ)) (b := (159807803527 / 100000000000000 : ℝ)) (q := (2229254954297 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12887])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12887])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12887]

theorem cert12887_47 : CellCertificate 12887 (35261566312819 / 400000000000000 : ℝ) (1629885038508137 / 1000000000000000000 : ℝ) (329115088531949 / 10000000000000000 : ℝ)
    (cell12887 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · have h := gap_lower (n := 12887) (a := (20614616455407 / 25000000000000 : ℝ)) (b := (159807803527 / 100000000000000 : ℝ)) (q := (2229258961243 / 100000000000000 : ℝ))
      (E := (cell12887 ⟨47, by decide⟩).energy) (xi := (329115088531949 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12887 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12887]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12887])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12887) (a := (20614616455407 / 25000000000000 : ℝ)) (b := (159807803527 / 100000000000000 : ℝ)) (q := (2229258961243 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12887])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12887])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12887]

theorem cert12887_48 : CellCertificate 12887 (35261566312819 / 400000000000000 : ℝ) (1629885038508137 / 1000000000000000000 : ℝ) (329115088531949 / 10000000000000000 : ℝ)
    (cell12887 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · have h := gap_lower (n := 12887) (a := (20606170403781 / 25000000000000 : ℝ)) (b := (159807803527 / 100000000000000 : ℝ)) (q := (445852596071 / 20000000000000 : ℝ))
      (E := (cell12887 ⟨48, by decide⟩).energy) (xi := (329115088531949 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12887 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12887]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12887])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12887) (a := (20606170403781 / 25000000000000 : ℝ)) (b := (159807803527 / 100000000000000 : ℝ)) (q := (445852596071 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12887])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12887])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12887]

theorem cert12887_49 : CellCertificate 12887 (35261566312819 / 400000000000000 : ℝ) (1629885038508137 / 1000000000000000000 : ℝ) (329115088531949 / 10000000000000000 : ℝ)
    (cell12887 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · have h := gap_lower (n := 12887) (a := (20597730185101 / 25000000000000 : ℝ)) (b := (159807803527 / 100000000000000 : ℝ)) (q := (445853401853 / 20000000000000 : ℝ))
      (E := (cell12887 ⟨49, by decide⟩).energy) (xi := (329115088531949 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12887 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12887]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12887])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12887) (a := (20597730185101 / 25000000000000 : ℝ)) (b := (159807803527 / 100000000000000 : ℝ)) (q := (445853401853 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12887])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12887])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12887]

theorem cert12887_50 : CellCertificate 12887 (35261566312819 / 400000000000000 : ℝ) (1629885038508137 / 1000000000000000000 : ℝ) (329115088531949 / 10000000000000000 : ℝ)
    (cell12887 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · have h := gap_lower (n := 12887) (a := (82357183168939 / 100000000000000 : ℝ)) (b := (159807803527 / 100000000000000 : ℝ)) (q := (445854197279 / 20000000000000 : ℝ))
      (E := (cell12887 ⟨50, by decide⟩).energy) (xi := (329115088531949 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12887 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12887]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12887])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12887) (a := (82357183168939 / 100000000000000 : ℝ)) (b := (159807803527 / 100000000000000 : ℝ)) (q := (445854197279 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12887])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12887])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12887]

theorem cert12887_51 : CellCertificate 12887 (35261566312819 / 400000000000000 : ℝ) (1629885038508137 / 1000000000000000000 : ℝ) (329115088531949 / 10000000000000000 : ℝ)
    (cell12887 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · have h := gap_lower (n := 12887) (a := (82323468872343 / 100000000000000 : ℝ)) (b := (159807803527 / 100000000000000 : ℝ)) (q := (557318756733 / 25000000000000 : ℝ))
      (E := (cell12887 ⟨51, by decide⟩).energy) (xi := (329115088531949 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12887 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12887]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12887])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12887) (a := (82323468872343 / 100000000000000 : ℝ)) (b := (159807803527 / 100000000000000 : ℝ)) (q := (557318756733 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12887])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12887])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12887]

theorem cert12887_52 : CellCertificate 12887 (35261566312819 / 400000000000000 : ℝ) (1629885038508137 / 1000000000000000000 : ℝ) (329115088531949 / 10000000000000000 : ℝ)
    (cell12887 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · have h := gap_lower (n := 12887) (a := (82289777822373 / 100000000000000 : ℝ)) (b := (159807803527 / 100000000000000 : ℝ)) (q := (2229279009851 / 100000000000000 : ℝ))
      (E := (cell12887 ⟨52, by decide⟩).energy) (xi := (329115088531949 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12887 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12887]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12887])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12887) (a := (82289777822373 / 100000000000000 : ℝ)) (b := (159807803527 / 100000000000000 : ℝ)) (q := (2229279009851 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12887])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12887])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12887]

theorem cert12887_53 : CellCertificate 12887 (35261566312819 / 400000000000000 : ℝ) (1629885038508137 / 1000000000000000000 : ℝ) (329115088531949 / 10000000000000000 : ℝ)
    (cell12887 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · have h := gap_lower (n := 12887) (a := (41128054995463 / 50000000000000 : ℝ)) (b := (159807803527 / 100000000000000 : ℝ)) (q := (2229283050013 / 100000000000000 : ℝ))
      (E := (cell12887 ⟨53, by decide⟩).energy) (xi := (329115088531949 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12887 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12887]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12887])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12887) (a := (41128054995463 / 50000000000000 : ℝ)) (b := (159807803527 / 100000000000000 : ℝ)) (q := (2229283050013 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12887])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12887])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12887]

theorem cert12887_54 : CellCertificate 12887 (35261566312819 / 400000000000000 : ℝ) (1629885038508137 / 1000000000000000000 : ℝ) (329115088531949 / 10000000000000000 : ℝ)
    (cell12887 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · have h := gap_lower (n := 12887) (a := (2055561633751 / 2500000000000 : ℝ)) (b := (159807803527 / 100000000000000 : ℝ)) (q := (1114643512939 / 50000000000000 : ℝ))
      (E := (cell12887 ⟨54, by decide⟩).energy) (xi := (329115088531949 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12887 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12887]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12887])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12887) (a := (2055561633751 / 2500000000000 : ℝ)) (b := (159807803527 / 100000000000000 : ℝ)) (q := (1114643512939 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12887])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12887])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12887]

theorem cert12887_55 : CellCertificate 12887 (35261566312819 / 400000000000000 : ℝ) (1629885038508137 / 1000000000000000000 : ℝ) (329115088531949 / 10000000000000000 : ℝ)
    (cell12887 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · have h := gap_lower (n := 12887) (a := (82188843871893 / 100000000000000 : ℝ)) (b := (159807803527 / 100000000000000 : ℝ)) (q := (2229291051983 / 100000000000000 : ℝ))
      (E := (cell12887 ⟨55, by decide⟩).energy) (xi := (329115088531949 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12887 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12887]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12887])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12887) (a := (82188843871893 / 100000000000000 : ℝ)) (b := (159807803527 / 100000000000000 : ℝ)) (q := (2229291051983 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12887])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12887])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12887]

theorem cert12887_56 : CellCertificate 12887 (35261566312819 / 400000000000000 : ℝ) (1629885038508137 / 1000000000000000000 : ℝ) (329115088531949 / 10000000000000000 : ℝ)
    (cell12887 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · have h := gap_lower (n := 12887) (a := (102694056911 / 125000000000 : ℝ)) (b := (159807803527 / 100000000000000 : ℝ)) (q := (1114647532711 / 50000000000000 : ℝ))
      (E := (cell12887 ⟨56, by decide⟩).energy) (xi := (329115088531949 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12887 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12887]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12887])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12887) (a := (102694056911 / 125000000000 : ℝ)) (b := (159807803527 / 100000000000000 : ℝ)) (q := (1114647532711 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12887])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12887])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12887]

theorem cert12887_57 : CellCertificate 12887 (35261566312819 / 400000000000000 : ℝ) (1629885038508137 / 1000000000000000000 : ℝ) (329115088531949 / 10000000000000000 : ℝ)
    (cell12887 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · have h := gap_lower (n := 12887) (a := (2566302196663 / 3125000000000 : ℝ)) (b := (159807803527 / 100000000000000 : ℝ)) (q := (2229299062149 / 100000000000000 : ℝ))
      (E := (cell12887 ⟨57, by decide⟩).energy) (xi := (329115088531949 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12887 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12887]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12887])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12887) (a := (2566302196663 / 3125000000000 : ℝ)) (b := (159807803527 / 100000000000000 : ℝ)) (q := (2229299062149 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12887])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12887])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12887]

theorem cert12887_58 : CellCertificate 12887 (35261566312819 / 400000000000000 : ℝ) (1629885038508137 / 1000000000000000000 : ℝ) (329115088531949 / 10000000000000000 : ℝ)
    (cell12887 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · have h := gap_lower (n := 12887) (a := (82088118137731 / 100000000000000 : ℝ)) (b := (159807803527 / 100000000000000 : ℝ)) (q := (139331443569 / 6250000000000 : ℝ))
      (E := (cell12887 ⟨58, by decide⟩).energy) (xi := (329115088531949 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12887 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12887]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12887])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12887) (a := (82088118137731 / 100000000000000 : ℝ)) (b := (159807803527 / 100000000000000 : ℝ)) (q := (139331443569 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12887])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12887])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12887]

theorem cert12887_59 : CellCertificate 12887 (35261566312819 / 400000000000000 : ℝ) (1629885038508137 / 1000000000000000000 : ℝ) (329115088531949 / 10000000000000000 : ℝ)
    (cell12887 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · have h := gap_lower (n := 12887) (a := (1282102953673 / 1562500000000 : ℝ)) (b := (159807803527 / 100000000000000 : ℝ)) (q := (557326776673 / 25000000000000 : ℝ))
      (E := (cell12887 ⟨59, by decide⟩).energy) (xi := (329115088531949 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12887 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12887]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12887])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12887) (a := (1282102953673 / 1562500000000 : ℝ)) (b := (159807803527 / 100000000000000 : ℝ)) (q := (557326776673 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12887])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12887])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12887]

theorem cert12888_40 : CellCertificate 12888 (176302399163971 / 2000000000000000 : ℝ) (814879266107161 / 500000000000000000 : ℝ) (164544473829027 / 5000000000000000 : ℝ)
    (cell12888 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · have h := gap_lower (n := 12888) (a := (82695608472573 / 100000000000000 : ℝ)) (b := (15979525707 / 10000000000000 : ℝ)) (q := (2229113874913 / 100000000000000 : ℝ))
      (E := (cell12888 ⟨40, by decide⟩).energy) (xi := (164544473829027 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12888 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12888]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12888])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12888) (a := (82695608472573 / 100000000000000 : ℝ)) (b := (15979525707 / 10000000000000 : ℝ)) (q := (2229113874913 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12888])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12888])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12888]

theorem cert12888_41 : CellCertificate 12888 (176302399163971 / 2000000000000000 : ℝ) (814879266107161 / 500000000000000000 : ℝ) (164544473829027 / 5000000000000000 : ℝ)
    (cell12888 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · have h := gap_lower (n := 12888) (a := (41330830214279 / 50000000000000 : ℝ)) (b := (15979525707 / 10000000000000 : ℝ)) (q := (557279473171 / 25000000000000 : ℝ))
      (E := (cell12888 ⟨41, by decide⟩).energy) (xi := (164544473829027 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12888 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12888]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12888])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12888) (a := (41330830214279 / 50000000000000 : ℝ)) (b := (15979525707 / 10000000000000 : ℝ)) (q := (557279473171 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12888])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12888])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12888]

theorem cert12888_42 : CellCertificate 12888 (176302399163971 / 2000000000000000 : ℝ) (814879266107161 / 500000000000000000 : ℝ) (164544473829027 / 5000000000000000 : ℝ)
    (cell12888 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · have h := gap_lower (n := 12888) (a := (82627735919683 / 100000000000000 : ℝ)) (b := (15979525707 / 10000000000000 : ℝ)) (q := (2229121874281 / 100000000000000 : ℝ))
      (E := (cell12888 ⟨42, by decide⟩).energy) (xi := (164544473829027 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12888 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12888]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12888])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12888) (a := (82627735919683 / 100000000000000 : ℝ)) (b := (15979525707 / 10000000000000 : ℝ)) (q := (2229121874281 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12888])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12888])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12888]

theorem cert12888_43 : CellCertificate 12888 (176302399163971 / 2000000000000000 : ℝ) (814879266107161 / 500000000000000000 : ℝ) (164544473829027 / 5000000000000000 : ℝ)
    (cell12888 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · have h := gap_lower (n := 12888) (a := (82593834916397 / 100000000000000 : ℝ)) (b := (15979525707 / 10000000000000 : ℝ)) (q := (2229125877393 / 100000000000000 : ℝ))
      (E := (cell12888 ⟨43, by decide⟩).energy) (xi := (164544473829027 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12888 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12888]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12888])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12888) (a := (82593834916397 / 100000000000000 : ℝ)) (b := (15979525707 / 10000000000000 : ℝ)) (q := (2229125877393 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12888])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12888])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12888]

theorem cert12888_44 : CellCertificate 12888 (176302399163971 / 2000000000000000 : ℝ) (814879266107161 / 500000000000000000 : ℝ) (164544473829027 / 5000000000000000 : ℝ)
    (cell12888 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · have h := gap_lower (n := 12888) (a := (825599573893 / 1000000000000 : ℝ)) (b := (15979525707 / 10000000000000 : ℝ)) (q := (557282475181 / 25000000000000 : ℝ))
      (E := (cell12888 ⟨44, by decide⟩).energy) (xi := (164544473829027 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12888 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12888]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12888])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12888) (a := (825599573893 / 1000000000000 : ℝ)) (b := (15979525707 / 10000000000000 : ℝ)) (q := (557282475181 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12888])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12888])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12888]

theorem cert12888_45 : CellCertificate 12888 (176302399163971 / 2000000000000000 : ℝ) (814879266107161 / 500000000000000000 : ℝ) (164544473829027 / 5000000000000000 : ℝ)
    (cell12888 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · have h := gap_lower (n := 12888) (a := (82526103309137 / 100000000000000 : ℝ)) (b := (15979525707 / 10000000000000 : ℝ)) (q := (2229133883883 / 100000000000000 : ℝ))
      (E := (cell12888 ⟨45, by decide⟩).energy) (xi := (164544473829027 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12888 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12888]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12888])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12888) (a := (82526103309137 / 100000000000000 : ℝ)) (b := (15979525707 / 10000000000000 : ℝ)) (q := (2229133883883 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12888])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12888])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12888]

theorem cert12888_46 : CellCertificate 12888 (176302399163971 / 2000000000000000 : ℝ) (814879266107161 / 500000000000000000 : ℝ) (164544473829027 / 5000000000000000 : ℝ)
    (cell12888 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · have h := gap_lower (n := 12888) (a := (41246136323401 / 50000000000000 : ℝ)) (b := (15979525707 / 10000000000000 : ℝ)) (q := (2229137883981 / 100000000000000 : ℝ))
      (E := (cell12888 ⟨46, by decide⟩).energy) (xi := (164544473829027 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12888 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12888]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12888])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12888) (a := (41246136323401 / 50000000000000 : ℝ)) (b := (15979525707 / 10000000000000 : ℝ)) (q := (2229137883981 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12888])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12888])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12888]

theorem cert12888_47 : CellCertificate 12888 (176302399163971 / 2000000000000000 : ℝ) (814879266107161 / 500000000000000000 : ℝ) (164544473829027 / 5000000000000000 : ℝ)
    (cell12888 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · have h := gap_lower (n := 12888) (a := (41229232686667 / 50000000000000 : ℝ)) (b := (15979525707 / 10000000000000 : ℝ)) (q := (1114570949539 / 50000000000000 : ℝ))
      (E := (cell12888 ⟨47, by decide⟩).energy) (xi := (164544473829027 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12888 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12888]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12888])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12888) (a := (41229232686667 / 50000000000000 : ℝ)) (b := (15979525707 / 10000000000000 : ℝ)) (q := (1114570949539 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12888])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12888])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12888]

theorem cert12888_48 : CellCertificate 12888 (176302399163971 / 2000000000000000 : ℝ) (814879266107161 / 500000000000000000 : ℝ) (164544473829027 / 5000000000000000 : ℝ)
    (cell12888 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · have h := gap_lower (n := 12888) (a := (82424681459917 / 100000000000000 : ℝ)) (b := (15979525707 / 10000000000000 : ℝ)) (q := (2229145927019 / 100000000000000 : ℝ))
      (E := (cell12888 ⟨48, by decide⟩).energy) (xi := (164544473829027 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12888 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12888]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12888])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12888) (a := (82424681459917 / 100000000000000 : ℝ)) (b := (15979525707 / 10000000000000 : ℝ)) (q := (2229145927019 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12888])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12888])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12888]

theorem cert12888_49 : CellCertificate 12888 (176302399163971 / 2000000000000000 : ℝ) (814879266107161 / 500000000000000000 : ℝ) (164544473829027 / 5000000000000000 : ℝ)
    (cell12888 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · have h := gap_lower (n := 12888) (a := (82390920877881 / 100000000000000 : ℝ)) (b := (15979525707 / 10000000000000 : ℝ)) (q := (1114574953231 / 50000000000000 : ℝ))
      (E := (cell12888 ⟨49, by decide⟩).energy) (xi := (164544473829027 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12888 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12888]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12888])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12888) (a := (82390920877881 / 100000000000000 : ℝ)) (b := (15979525707 / 10000000000000 : ℝ)) (q := (1114574953231 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12888])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12888])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12888]

theorem cert12888_50 : CellCertificate 12888 (176302399163971 / 2000000000000000 : ℝ) (814879266107161 / 500000000000000000 : ℝ) (164544473829027 / 5000000000000000 : ℝ)
    (cell12888 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · have h := gap_lower (n := 12888) (a := (82357183598697 / 100000000000000 : ℝ)) (b := (15979525707 / 10000000000000 : ℝ)) (q := (2229153952757 / 100000000000000 : ℝ))
      (E := (cell12888 ⟨50, by decide⟩).energy) (xi := (164544473829027 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12888 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12888]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12888])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12888) (a := (82357183598697 / 100000000000000 : ℝ)) (b := (15979525707 / 10000000000000 : ℝ)) (q := (2229153952757 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12888])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12888])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12888]

theorem cert12888_51 : CellCertificate 12888 (176302399163971 / 2000000000000000 : ℝ) (814879266107161 / 500000000000000000 : ℝ) (164544473829027 / 5000000000000000 : ℝ)
    (cell12888 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · have h := gap_lower (n := 12888) (a := (41161734796991 / 50000000000000 : ℝ)) (b := (15979525707 / 10000000000000 : ℝ)) (q := (445831589027 / 20000000000000 : ℝ))
      (E := (cell12888 ⟨51, by decide⟩).energy) (xi := (164544473829027 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12888 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12888]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12888])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12888) (a := (41161734796991 / 50000000000000 : ℝ)) (b := (15979525707 / 10000000000000 : ℝ)) (q := (445831589027 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12888])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12888])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12888]

theorem cert12888_52 : CellCertificate 12888 (176302399163971 / 2000000000000000 : ℝ) (814879266107161 / 500000000000000000 : ℝ) (164544473829027 / 5000000000000000 : ℝ)
    (cell12888 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · have h := gap_lower (n := 12888) (a := (20572444708873 / 25000000000000 : ℝ)) (b := (15979525707 / 10000000000000 : ℝ)) (q := (2229161939573 / 100000000000000 : ℝ))
      (E := (cell12888 ⟨52, by decide⟩).energy) (xi := (164544473829027 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12888 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12888]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12888])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12888) (a := (20572444708873 / 25000000000000 : ℝ)) (b := (15979525707 / 10000000000000 : ℝ)) (q := (2229161939573 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12888])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12888])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12888]

theorem cert12888_53 : CellCertificate 12888 (176302399163971 / 2000000000000000 : ℝ) (814879266107161 / 500000000000000000 : ℝ) (164544473829027 / 5000000000000000 : ℝ)
    (cell12888 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · have h := gap_lower (n := 12888) (a := (41128055647563 / 50000000000000 : ℝ)) (b := (15979525707 / 10000000000000 : ℝ)) (q := (2229165932857 / 100000000000000 : ℝ))
      (E := (cell12888 ⟨53, by decide⟩).energy) (xi := (164544473829027 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12888 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12888]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12888])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12888) (a := (41128055647563 / 50000000000000 : ℝ)) (b := (15979525707 / 10000000000000 : ℝ)) (q := (2229165932857 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12888])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12888])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12888]

theorem cert12888_54 : CellCertificate 12888 (176302399163971 / 2000000000000000 : ℝ) (814879266107161 / 500000000000000000 : ℝ) (164544473829027 / 5000000000000000 : ℝ)
    (cell12888 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · have h := gap_lower (n := 12888) (a := (41111233472461 / 50000000000000 : ℝ)) (b := (15979525707 / 10000000000000 : ℝ)) (q := (1114584990331 / 50000000000000 : ℝ))
      (E := (cell12888 ⟨54, by decide⟩).energy) (xi := (164544473829027 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12888 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12888]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12888])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12888) (a := (41111233472461 / 50000000000000 : ℝ)) (b := (15979525707 / 10000000000000 : ℝ)) (q := (1114584990331 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12888])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12888])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12888]

theorem cert12888_55 : CellCertificate 12888 (176302399163971 / 2000000000000000 : ℝ) (814879266107161 / 500000000000000000 : ℝ) (164544473829027 / 5000000000000000 : ℝ)
    (cell12888 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · have h := gap_lower (n := 12888) (a := (82188845757057 / 100000000000000 : ℝ)) (b := (15979525707 / 10000000000000 : ℝ)) (q := (557293490299 / 25000000000000 : ℝ))
      (E := (cell12888 ⟨55, by decide⟩).energy) (xi := (164544473829027 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12888 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12888]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12888])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12888) (a := (82188845757057 / 100000000000000 : ℝ)) (b := (15979525707 / 10000000000000 : ℝ)) (q := (557293490299 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12888])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12888])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12888]

theorem cert12888_56 : CellCertificate 12888 (176302399163971 / 2000000000000000 : ℝ) (814879266107161 / 500000000000000000 : ℝ) (164544473829027 / 5000000000000000 : ℝ)
    (cell12888 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · have h := gap_lower (n := 12888) (a := (1643104954077 / 2000000000000 : ℝ)) (b := (15979525707 / 10000000000000 : ℝ)) (q := (2229177988829 / 100000000000000 : ℝ))
      (E := (cell12888 ⟨56, by decide⟩).energy) (xi := (164544473829027 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12888 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12888]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12888])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12888) (a := (1643104954077 / 2000000000000 : ℝ)) (b := (15979525707 / 10000000000000 : ℝ)) (q := (2229177988829 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12888])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12888])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12888]

theorem cert12888_57 : CellCertificate 12888 (176302399163971 / 2000000000000000 : ℝ) (814879266107161 / 500000000000000000 : ℝ) (164544473829027 / 5000000000000000 : ℝ)
    (cell12888 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · have h := gap_lower (n := 12888) (a := (82121672757753 / 100000000000000 : ℝ)) (b := (15979525707 / 10000000000000 : ℝ)) (q := (1114591000213 / 50000000000000 : ℝ))
      (E := (cell12888 ⟨57, by decide⟩).energy) (xi := (164544473829027 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12888 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12888]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12888])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12888) (a := (82121672757753 / 100000000000000 : ℝ)) (b := (15979525707 / 10000000000000 : ℝ)) (q := (1114591000213 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12888])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12888])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12888]

theorem cert12888_58 : CellCertificate 12888 (176302399163971 / 2000000000000000 : ℝ) (814879266107161 / 500000000000000000 : ℝ) (164544473829027 / 5000000000000000 : ℝ)
    (cell12888 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · have h := gap_lower (n := 12888) (a := (513050755571 / 625000000000 : ℝ)) (b := (15979525707 / 10000000000000 : ℝ)) (q := (445837198347 / 20000000000000 : ℝ))
      (E := (cell12888 ⟨58, by decide⟩).energy) (xi := (164544473829027 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12888 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12888]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12888])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12888) (a := (513050755571 / 625000000000 : ℝ)) (b := (15979525707 / 10000000000000 : ℝ)) (q := (445837198347 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12888])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12888])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12888]

theorem cert12888_59 : CellCertificate 12888 (176302399163971 / 2000000000000000 : ℝ) (814879266107161 / 500000000000000000 : ℝ) (164544473829027 / 5000000000000000 : ℝ)
    (cell12888 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · have h := gap_lower (n := 12888) (a := (82054592077397 / 100000000000000 : ℝ)) (b := (15979525707 / 10000000000000 : ℝ)) (q := (1114595008757 / 50000000000000 : ℝ))
      (E := (cell12888 ⟨59, by decide⟩).energy) (xi := (164544473829027 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12888 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12888]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12888])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12888) (a := (82054592077397 / 100000000000000 : ℝ)) (b := (15979525707 / 10000000000000 : ℝ)) (q := (1114595008757 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12888])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12888])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12888]

theorem cert12889_40 : CellCertificate 12889 (440742418930111 / 5000000000000000 : ℝ) (1629632045556983 / 1000000000000000000 : ℝ) (65812562195919 / 2000000000000000 : ℝ)
    (cell12889 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · have h := gap_lower (n := 12889) (a := (41347802981083 / 50000000000000 : ℝ)) (b := (31956542519 / 20000000000000 : ℝ)) (q := (278624603219 / 12500000000000 : ℝ))
      (E := (cell12889 ⟨40, by decide⟩).energy) (xi := (65812562195919 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12889 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12889]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12889])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12889) (a := (41347802981083 / 50000000000000 : ℝ)) (b := (31956542519 / 20000000000000 : ℝ)) (q := (278624603219 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12889])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12889])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12889]

theorem cert12889_41 : CellCertificate 12889 (440742418930111 / 5000000000000000 : ℝ) (1629632045556983 / 1000000000000000000 : ℝ) (65812562195919 / 2000000000000000 : ℝ)
    (cell12889 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · have h := gap_lower (n := 12889) (a := (82661658214041 / 100000000000000 : ℝ)) (b := (31956542519 / 20000000000000 : ℝ)) (q := (1114500423821 / 50000000000000 : ℝ))
      (E := (cell12889 ⟨41, by decide⟩).energy) (xi := (65812562195919 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12889 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12889]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12889])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12889) (a := (82661658214041 / 100000000000000 : ℝ)) (b := (31956542519 / 20000000000000 : ℝ)) (q := (1114500423821 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12889])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12889])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12889]

theorem cert12889_42 : CellCertificate 12889 (440742418930111 / 5000000000000000 : ℝ) (1629632045556983 / 1000000000000000000 : ℝ) (65812562195919 / 2000000000000000 : ℝ)
    (cell12889 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · have h := gap_lower (n := 12889) (a := (82627734000647 / 100000000000000 : ℝ)) (b := (31956542519 / 20000000000000 : ℝ)) (q := (2229004834043 / 100000000000000 : ℝ))
      (E := (cell12889 ⟨42, by decide⟩).energy) (xi := (65812562195919 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12889 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12889]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12889])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12889) (a := (82627734000647 / 100000000000000 : ℝ)) (b := (31956542519 / 20000000000000 : ℝ)) (q := (2229004834043 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12889])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12889])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12889]

theorem cert12889_43 : CellCertificate 12889 (440742418930111 / 5000000000000000 : ℝ) (1629632045556983 / 1000000000000000000 : ℝ) (65812562195919 / 2000000000000000 : ℝ)
    (cell12889 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · have h := gap_lower (n := 12889) (a := (82593833292437 / 100000000000000 : ℝ)) (b := (31956542519 / 20000000000000 : ℝ)) (q := (2229008842639 / 100000000000000 : ℝ))
      (E := (cell12889 ⟨43, by decide⟩).energy) (xi := (65812562195919 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12889 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12889]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12889])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12889) (a := (82593833292437 / 100000000000000 : ℝ)) (b := (31956542519 / 20000000000000 : ℝ)) (q := (2229008842639 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12889])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12889])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12889]

theorem cert12889_44 : CellCertificate 12889 (440742418930111 / 5000000000000000 : ℝ) (1629632045556983 / 1000000000000000000 : ℝ) (65812562195919 / 2000000000000000 : ℝ)
    (cell12889 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · have h := gap_lower (n := 12889) (a := (82559956060009 / 100000000000000 : ℝ)) (b := (31956542519 / 20000000000000 : ℝ)) (q := (2229012872137 / 100000000000000 : ℝ))
      (E := (cell12889 ⟨44, by decide⟩).energy) (xi := (65812562195919 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12889 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12889]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12889])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12889) (a := (82559956060009 / 100000000000000 : ℝ)) (b := (31956542519 / 20000000000000 : ℝ)) (q := (2229012872137 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12889])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12889])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12889]

theorem cert12889_45 : CellCertificate 12889 (440742418930111 / 5000000000000000 : ℝ) (1629632045556983 / 1000000000000000000 : ℝ) (65812562195919 / 2000000000000000 : ℝ)
    (cell12889 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · have h := gap_lower (n := 12889) (a := (82526102274109 / 100000000000000 : ℝ)) (b := (31956542519 / 20000000000000 : ℝ)) (q := (2229016862147 / 100000000000000 : ℝ))
      (E := (cell12889 ⟨45, by decide⟩).energy) (xi := (65812562195919 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12889 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12889]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12889])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12889) (a := (82526102274109 / 100000000000000 : ℝ)) (b := (31956542519 / 20000000000000 : ℝ)) (q := (2229016862147 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12889])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12889])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12889]

theorem cert12889_46 : CellCertificate 12889 (440742418930111 / 5000000000000000 : ℝ) (1629632045556983 / 1000000000000000000 : ℝ) (65812562195919 / 2000000000000000 : ℝ)
    (cell12889 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · have h := gap_lower (n := 12889) (a := (82492271905633 / 100000000000000 : ℝ)) (b := (31956542519 / 20000000000000 : ℝ)) (q := (1114510434887 / 50000000000000 : ℝ))
      (E := (cell12889 ⟨46, by decide⟩).energy) (xi := (65812562195919 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12889 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12889]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12889])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12889) (a := (82492271905633 / 100000000000000 : ℝ)) (b := (31956542519 / 20000000000000 : ℝ)) (q := (1114510434887 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12889])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12889])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12889]

theorem cert12889_47 : CellCertificate 12889 (440742418930111 / 5000000000000000 : ℝ) (1629632045556983 / 1000000000000000000 : ℝ) (65812562195919 / 2000000000000000 : ℝ)
    (cell12889 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · have h := gap_lower (n := 12889) (a := (82458464925619 / 100000000000000 : ℝ)) (b := (31956542519 / 20000000000000 : ℝ)) (q := (2229024893081 / 100000000000000 : ℝ))
      (E := (cell12889 ⟨47, by decide⟩).energy) (xi := (65812562195919 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12889 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12889]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12889])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12889) (a := (82458464925619 / 100000000000000 : ℝ)) (b := (31956542519 / 20000000000000 : ℝ)) (q := (2229024893081 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12889])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12889])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12889]

theorem cert12889_48 : CellCertificate 12889 (440742418930111 / 5000000000000000 : ℝ) (1629632045556983 / 1000000000000000000 : ℝ) (65812562195919 / 2000000000000000 : ℝ)
    (cell12889 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · have h := gap_lower (n := 12889) (a := (41212340652627 / 50000000000000 : ℝ)) (b := (31956542519 / 20000000000000 : ℝ)) (q := (2229028870959 / 100000000000000 : ℝ))
      (E := (cell12889 ⟨48, by decide⟩).energy) (xi := (65812562195919 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12889 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12889]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12889])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12889) (a := (41212340652627 / 50000000000000 : ℝ)) (b := (31956542519 / 20000000000000 : ℝ)) (q := (2229028870959 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12889])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12889])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12889]

theorem cert12889_49 : CellCertificate 12889 (440742418930111 / 5000000000000000 : ℝ) (1629632045556983 / 1000000000000000000 : ℝ) (65812562195919 / 2000000000000000 : ℝ)
    (cell12889 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · have h := gap_lower (n := 12889) (a := (82390921015867 / 100000000000000 : ℝ)) (b := (31956542519 / 20000000000000 : ℝ)) (q := (2229032918923 / 100000000000000 : ℝ))
      (E := (cell12889 ⟨49, by decide⟩).energy) (xi := (65812562195919 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12889 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12889]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12889])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12889) (a := (82390921015867 / 100000000000000 : ℝ)) (b := (31956542519 / 20000000000000 : ℝ)) (q := (2229032918923 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12889])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12889])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12889]

theorem cert12889_50 : CellCertificate 12889 (440742418930111 / 5000000000000000 : ℝ) (1629632045556983 / 1000000000000000000 : ℝ) (65812562195919 / 2000000000000000 : ℝ)
    (cell12889 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · have h := gap_lower (n := 12889) (a := (8235718402893 / 10000000000000 : ℝ)) (b := (31956542519 / 20000000000000 : ℝ)) (q := (139314807279 / 6250000000000 : ℝ))
      (E := (cell12889 ⟨50, by decide⟩).energy) (xi := (65812562195919 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12889 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12889]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12889])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12889) (a := (8235718402893 / 10000000000000 : ℝ)) (b := (31956542519 / 20000000000000 : ℝ)) (q := (139314807279 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12889])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12889])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12889]

theorem cert12889_51 : CellCertificate 12889 (440742418930111 / 5000000000000000 : ℝ) (1629632045556983 / 1000000000000000000 : ℝ) (65812562195919 / 2000000000000000 : ℝ)
    (cell12889 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · have h := gap_lower (n := 12889) (a := (82323470316061 / 100000000000000 : ℝ)) (b := (31956542519 / 20000000000000 : ℝ)) (q := (2229040919743 / 100000000000000 : ℝ))
      (E := (cell12889 ⟨51, by decide⟩).energy) (xi := (65812562195919 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12889 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12889]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12889])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12889) (a := (82323470316061 / 100000000000000 : ℝ)) (b := (31956542519 / 20000000000000 : ℝ)) (q := (2229040919743 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12889])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12889])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12889]

theorem cert12889_52 : CellCertificate 12889 (440742418930111 / 5000000000000000 : ℝ) (1629632045556983 / 1000000000000000000 : ℝ) (65812562195919 / 2000000000000000 : ℝ)
    (cell12889 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · have h := gap_lower (n := 12889) (a := (82289779849017 / 100000000000000 : ℝ)) (b := (31956542519 / 20000000000000 : ℝ)) (q := (2229044925757 / 100000000000000 : ℝ))
      (E := (cell12889 ⟨52, by decide⟩).energy) (xi := (65812562195919 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12889 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12889]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12889])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12889) (a := (82289779849017 / 100000000000000 : ℝ)) (b := (31956542519 / 20000000000000 : ℝ)) (q := (2229044925757 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12889])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12889])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12889]

theorem cert12889_53 : CellCertificate 12889 (440742418930111 / 5000000000000000 : ℝ) (1629632045556983 / 1000000000000000000 : ℝ) (65812562195919 / 2000000000000000 : ℝ)
    (cell12889 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · have h := gap_lower (n := 12889) (a := (5141007037481 / 6250000000000 : ℝ)) (b := (31956542519 / 20000000000000 : ℝ)) (q := (69657779103 / 3125000000000 : ℝ))
      (E := (cell12889 ⟨53, by decide⟩).energy) (xi := (65812562195919 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12889 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12889]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12889])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12889) (a := (5141007037481 / 6250000000000 : ℝ)) (b := (31956542519 / 20000000000000 : ℝ)) (q := (69657779103 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12889])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12889])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12889]

theorem cert12889_54 : CellCertificate 12889 (440742418930111 / 5000000000000000 : ℝ) (1629632045556983 / 1000000000000000000 : ℝ) (65812562195919 / 2000000000000000 : ℝ)
    (cell12889 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · have h := gap_lower (n := 12889) (a := (41111234270069 / 50000000000000 : ℝ)) (b := (31956542519 / 20000000000000 : ℝ)) (q := (2229052932937 / 100000000000000 : ℝ))
      (E := (cell12889 ⟨54, by decide⟩).energy) (xi := (65812562195919 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12889 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12889]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12889])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12889) (a := (41111234270069 / 50000000000000 : ℝ)) (b := (31956542519 / 20000000000000 : ℝ)) (q := (2229052932937 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12889])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12889])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12889]

theorem cert12889_55 : CellCertificate 12889 (440742418930111 / 5000000000000000 : ℝ) (1629632045556983 / 1000000000000000000 : ℝ) (65812562195919 / 2000000000000000 : ℝ)
    (cell12889 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · have h := gap_lower (n := 12889) (a := (41094423821261 / 50000000000000 : ℝ)) (b := (31956542519 / 20000000000000 : ℝ)) (q := (2229056927049 / 100000000000000 : ℝ))
      (E := (cell12889 ⟨55, by decide⟩).energy) (xi := (65812562195919 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12889 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12889]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12889])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12889) (a := (41094423821261 / 50000000000000 : ℝ)) (b := (31956542519 / 20000000000000 : ℝ)) (q := (2229056927049 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12889])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12889])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12889]

theorem cert12889_56 : CellCertificate 12889 (440742418930111 / 5000000000000000 : ℝ) (1629632045556983 / 1000000000000000000 : ℝ) (65812562195919 / 2000000000000000 : ℝ)
    (cell12889 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · have h := gap_lower (n := 12889) (a := (16431049975833 / 20000000000000 : ℝ)) (b := (31956542519 / 20000000000000 : ℝ)) (q := (2229060968937 / 100000000000000 : ℝ))
      (E := (cell12889 ⟨56, by decide⟩).energy) (xi := (65812562195919 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12889 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12889]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12889])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12889) (a := (16431049975833 / 20000000000000 : ℝ)) (b := (31956542519 / 20000000000000 : ℝ)) (q := (2229060968937 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12889])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12889])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12889]

theorem cert12889_57 : CellCertificate 12889 (440742418930111 / 5000000000000000 : ℝ) (1629632045556983 / 1000000000000000000 : ℝ) (65812562195919 / 2000000000000000 : ℝ)
    (cell12889 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · have h := gap_lower (n := 12889) (a := (41060837611261 / 50000000000000 : ℝ)) (b := (31956542519 / 20000000000000 : ℝ)) (q := (1114532468149 / 50000000000000 : ℝ))
      (E := (cell12889 ⟨57, by decide⟩).energy) (xi := (65812562195919 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12889 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12889]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12889])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12889) (a := (41060837611261 / 50000000000000 : ℝ)) (b := (31956542519 / 20000000000000 : ℝ)) (q := (1114532468149 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12889])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12889])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12889]

theorem cert12889_58 : CellCertificate 12889 (440742418930111 / 5000000000000000 : ℝ) (1629632045556983 / 1000000000000000000 : ℝ) (65812562195919 / 2000000000000000 : ℝ)
    (cell12889 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · have h := gap_lower (n := 12889) (a := (41044061822593 / 50000000000000 : ℝ)) (b := (31956542519 / 20000000000000 : ℝ)) (q := (139316808949 / 6250000000000 : ℝ))
      (E := (cell12889 ⟨58, by decide⟩).energy) (xi := (65812562195919 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12889 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12889]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12889])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12889) (a := (41044061822593 / 50000000000000 : ℝ)) (b := (31956542519 / 20000000000000 : ℝ)) (q := (139316808949 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12889])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12889])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12889]

theorem cert12889_59 : CellCertificate 12889 (440742418930111 / 5000000000000000 : ℝ) (1629632045556983 / 1000000000000000000 : ℝ) (65812562195919 / 2000000000000000 : ℝ)
    (cell12889 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · have h := gap_lower (n := 12889) (a := (16410919023977 / 20000000000000 : ℝ)) (b := (31956542519 / 20000000000000 : ℝ)) (q := (557268246303 / 25000000000000 : ℝ))
      (E := (cell12889 ⟨59, by decide⟩).energy) (xi := (65812562195919 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12889 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12889]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12889])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12889) (a := (16410919023977 / 20000000000000 : ℝ)) (b := (31956542519 / 20000000000000 : ℝ)) (q := (557268246303 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12889])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12889])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12889]

theorem cert12890_40 : CellCertificate 12890 (88145768394063 / 1000000000000000 : ℝ) (407376394632887 / 250000000000000000 : ℝ) (329036678495491 / 10000000000000000 : ℝ)
    (cell12890 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · have h := gap_lower (n := 12890) (a := (10336950431573 / 12500000000000 : ℝ)) (b := (159770170099 / 100000000000000 : ℝ)) (q := (557219958087 / 25000000000000 : ℝ))
      (E := (cell12890 ⟨40, by decide⟩).energy) (xi := (329036678495491 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12890 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12890]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12890])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12890) (a := (10336950431573 / 12500000000000 : ℝ)) (b := (159770170099 / 100000000000000 : ℝ)) (q := (557219958087 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12890])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12890])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12890]

theorem cert12890_41 : CellCertificate 12890 (88145768394063 / 1000000000000000 : ℝ) (407376394632887 / 250000000000000000 : ℝ) (329036678495491 / 10000000000000000 : ℝ)
    (cell12890 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · have h := gap_lower (n := 12890) (a := (82661656000313 / 100000000000000 : ℝ)) (b := (159770170099 / 100000000000000 : ℝ)) (q := (557220949907 / 25000000000000 : ℝ))
      (E := (cell12890 ⟨41, by decide⟩).energy) (xi := (329036678495491 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12890 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12890]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12890])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12890) (a := (82661656000313 / 100000000000000 : ℝ)) (b := (159770170099 / 100000000000000 : ℝ)) (q := (557220949907 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12890])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12890])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12890]

theorem cert12890_42 : CellCertificate 12890 (88145768394063 / 1000000000000000 : ℝ) (407376394632887 / 250000000000000000 : ℝ) (329036678495491 / 10000000000000000 : ℝ)
    (cell12890 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · have h := gap_lower (n := 12890) (a := (41313866041183 / 50000000000000 : ℝ)) (b := (159770170099 / 100000000000000 : ℝ)) (q := (2228887849679 / 100000000000000 : ℝ))
      (E := (cell12890 ⟨42, by decide⟩).energy) (xi := (329036678495491 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12890 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12890]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12890])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12890) (a := (41313866041183 / 50000000000000 : ℝ)) (b := (159770170099 / 100000000000000 : ℝ)) (q := (2228887849679 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12890])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12890])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12890]

theorem cert12890_43 : CellCertificate 12890 (88145768394063 / 1000000000000000 : ℝ) (407376394632887 / 250000000000000000 : ℝ) (329036678495491 / 10000000000000000 : ℝ)
    (cell12890 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · have h := gap_lower (n := 12890) (a := (20648457917299 / 25000000000000 : ℝ)) (b := (159770170099 / 100000000000000 : ℝ)) (q := (278611475623 / 12500000000000 : ℝ))
      (E := (cell12890 ⟨43, by decide⟩).energy) (xi := (329036678495491 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12890 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12890]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12890])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12890) (a := (20648457917299 / 25000000000000 : ℝ)) (b := (159770170099 / 100000000000000 : ℝ)) (q := (278611475623 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12890])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12890])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12890]

theorem cert12890_44 : CellCertificate 12890 (88145768394063 / 1000000000000000 : ℝ) (407376394632887 / 250000000000000000 : ℝ) (329036678495491 / 10000000000000000 : ℝ)
    (cell12890 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · have h := gap_lower (n := 12890) (a := (82559954731401 / 100000000000000 : ℝ)) (b := (159770170099 / 100000000000000 : ℝ)) (q := (2228895840687 / 100000000000000 : ℝ))
      (E := (cell12890 ⟨44, by decide⟩).energy) (xi := (329036678495491 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12890 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12890]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12890])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12890) (a := (82559954731401 / 100000000000000 : ℝ)) (b := (159770170099 / 100000000000000 : ℝ)) (q := (2228895840687 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12890])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12890])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12890]

theorem cert12890_45 : CellCertificate 12890 (88145768394063 / 1000000000000000 : ℝ) (407376394632887 / 250000000000000000 : ℝ) (329036678495491 / 10000000000000000 : ℝ)
    (cell12890 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · have h := gap_lower (n := 12890) (a := (8252610123973 / 10000000000000 : ℝ)) (b := (159770170099 / 100000000000000 : ℝ)) (q := (2228899837581 / 100000000000000 : ℝ))
      (E := (cell12890 ⟨45, by decide⟩).energy) (xi := (329036678495491 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12890 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12890]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12890])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12890) (a := (8252610123973 / 10000000000000 : ℝ)) (b := (159770170099 / 100000000000000 : ℝ)) (q := (2228899837581 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12890])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12890])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12890]

theorem cert12890_46 : CellCertificate 12890 (88145768394063 / 1000000000000000 : ℝ) (407376394632887 / 250000000000000000 : ℝ) (329036678495491 / 10000000000000000 : ℝ)
    (cell12890 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · have h := gap_lower (n := 12890) (a := (41246135582539 / 50000000000000 : ℝ)) (b := (159770170099 / 100000000000000 : ℝ)) (q := (1114451926387 / 50000000000000 : ℝ))
      (E := (cell12890 ⟨46, by decide⟩).energy) (xi := (329036678495491 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12890 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12890]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12890])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12890) (a := (41246135582539 / 50000000000000 : ℝ)) (b := (159770170099 / 100000000000000 : ℝ)) (q := (1114451926387 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12890])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12890])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12890]

theorem cert12890_47 : CellCertificate 12890 (88145768394063 / 1000000000000000 : ℝ) (407376394632887 / 250000000000000000 : ℝ) (329036678495491 / 10000000000000000 : ℝ)
    (cell12890 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · have h := gap_lower (n := 12890) (a := (20614616119621 / 25000000000000 : ℝ)) (b := (159770170099 / 100000000000000 : ℝ)) (q := (2228907884327 / 100000000000000 : ℝ))
      (E := (cell12890 ⟨47, by decide⟩).energy) (xi := (329036678495491 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12890 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12890]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12890])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12890) (a := (20614616119621 / 25000000000000 : ℝ)) (b := (159770170099 / 100000000000000 : ℝ)) (q := (2228907884327 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12890])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12890])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12890]

theorem cert12890_48 : CellCertificate 12890 (88145768394063 / 1000000000000000 : ℝ) (407376394632887 / 250000000000000000 : ℝ) (329036678495491 / 10000000000000000 : ℝ)
    (cell12890 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · have h := gap_lower (n := 12890) (a := (16484936230227 / 20000000000000 : ℝ)) (b := (159770170099 / 100000000000000 : ℝ)) (q := (222891187113 / 10000000000000 : ℝ))
      (E := (cell12890 ⟨48, by decide⟩).energy) (xi := (329036678495491 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12890 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12890]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12890])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12890) (a := (16484936230227 / 20000000000000 : ℝ)) (b := (159770170099 / 100000000000000 : ℝ)) (q := (222891187113 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12890])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12890])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12890]

theorem cert12890_49 : CellCertificate 12890 (88145768394063 / 1000000000000000 : ℝ) (407376394632887 / 250000000000000000 : ℝ) (329036678495491 / 10000000000000000 : ℝ)
    (cell12890 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · have h := gap_lower (n := 12890) (a := (41195460577181 / 50000000000000 : ℝ)) (b := (159770170099 / 100000000000000 : ℝ)) (q := (1114457934861 / 50000000000000 : ℝ))
      (E := (cell12890 ⟨49, by decide⟩).energy) (xi := (329036678495491 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12890 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12890]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12890])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12890) (a := (41195460577181 / 50000000000000 : ℝ)) (b := (159770170099 / 100000000000000 : ℝ)) (q := (1114457934861 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12890])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12890])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12890]

theorem cert12890_50 : CellCertificate 12890 (88145768394063 / 1000000000000000 : ℝ) (407376394632887 / 250000000000000000 : ℝ) (329036678495491 / 10000000000000000 : ℝ)
    (cell12890 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · have h := gap_lower (n := 12890) (a := (41178592229819 / 50000000000000 : ℝ)) (b := (159770170099 / 100000000000000 : ℝ)) (q := (2228919877521 / 100000000000000 : ℝ))
      (E := (cell12890 ⟨50, by decide⟩).energy) (xi := (329036678495491 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12890 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12890]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12890])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12890) (a := (41178592229819 / 50000000000000 : ℝ)) (b := (159770170099 / 100000000000000 : ℝ)) (q := (2228919877521 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12890])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12890])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12890]

theorem cert12890_51 : CellCertificate 12890 (88145768394063 / 1000000000000000 : ℝ) (407376394632887 / 250000000000000000 : ℝ) (329036678495491 / 10000000000000000 : ℝ)
    (cell12890 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · have h := gap_lower (n := 12890) (a := (82323471038579 / 100000000000000 : ℝ)) (b := (159770170099 / 100000000000000 : ℝ)) (q := (2228923891737 / 100000000000000 : ℝ))
      (E := (cell12890 ⟨51, by decide⟩).energy) (xi := (329036678495491 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12890 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12890]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12890])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12890) (a := (82323471038579 / 100000000000000 : ℝ)) (b := (159770170099 / 100000000000000 : ℝ)) (q := (2228923891737 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12890])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12890])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12890]

theorem cert12890_52 : CellCertificate 12890 (88145768394063 / 1000000000000000 : ℝ) (407376394632887 / 250000000000000000 : ℝ) (329036678495491 / 10000000000000000 : ℝ)
    (cell12890 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · have h := gap_lower (n := 12890) (a := (41144890431473 / 50000000000000 : ℝ)) (b := (159770170099 / 100000000000000 : ℝ)) (q := (2228927909363 / 100000000000000 : ℝ))
      (E := (cell12890 ⟨52, by decide⟩).energy) (xi := (329036678495491 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12890 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12890]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12890])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12890) (a := (41144890431473 / 50000000000000 : ℝ)) (b := (159770170099 / 100000000000000 : ℝ)) (q := (2228927909363 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12890])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12890])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12890]

theorem cert12890_53 : CellCertificate 12890 (88145768394063 / 1000000000000000 : ℝ) (407376394632887 / 250000000000000000 : ℝ) (329036678495491 / 10000000000000000 : ℝ)
    (cell12890 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · have h := gap_lower (n := 12890) (a := (20564028476159 / 25000000000000 : ℝ)) (b := (159770170099 / 100000000000000 : ℝ)) (q := (2228931927191 / 100000000000000 : ℝ))
      (E := (cell12890 ⟨53, by decide⟩).energy) (xi := (329036678495491 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12890 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12890]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12890])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12890) (a := (20564028476159 / 25000000000000 : ℝ)) (b := (159770170099 / 100000000000000 : ℝ)) (q := (2228931927191 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12890])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12890])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12890]

theorem cert12890_54 : CellCertificate 12890 (88145768394063 / 1000000000000000 : ℝ) (407376394632887 / 250000000000000000 : ℝ) (329036678495491 / 10000000000000000 : ℝ)
    (cell12890 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · have h := gap_lower (n := 12890) (a := (8222247013569 / 10000000000000 : ℝ)) (b := (159770170099 / 100000000000000 : ℝ)) (q := (557233985449 / 25000000000000 : ℝ))
      (E := (cell12890 ⟨54, by decide⟩).energy) (xi := (329036678495491 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12890 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12890]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12890])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12890) (a := (8222247013569 / 10000000000000 : ℝ)) (b := (159770170099 / 100000000000000 : ℝ)) (q := (557233985449 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12890])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12890])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12890]

theorem cert12890_55 : CellCertificate 12890 (88145768394063 / 1000000000000000 : ℝ) (407376394632887 / 250000000000000000 : ℝ) (329036678495491 / 10000000000000000 : ℝ)
    (cell12890 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · have h := gap_lower (n := 12890) (a := (2568401547759 / 3125000000000 : ℝ)) (b := (159770170099 / 100000000000000 : ℝ)) (q := (2228939949547 / 100000000000000 : ℝ))
      (E := (cell12890 ⟨55, by decide⟩).energy) (xi := (329036678495491 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12890 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12890]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12890])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12890) (a := (2568401547759 / 3125000000000 : ℝ)) (b := (159770170099 / 100000000000000 : ℝ)) (q := (2228939949547 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12890])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12890])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12890]

theorem cert12890_56 : CellCertificate 12890 (88145768394063 / 1000000000000000 : ℝ) (407376394632887 / 250000000000000000 : ℝ) (329036678495491 / 10000000000000000 : ℝ)
    (cell12890 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · have h := gap_lower (n := 12890) (a := (82155252054747 / 100000000000000 : ℝ)) (b := (159770170099 / 100000000000000 : ℝ)) (q := (139308996663 / 6250000000000 : ℝ))
      (E := (cell12890 ⟨56, by decide⟩).energy) (xi := (329036678495491 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12890 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12890]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12890])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12890) (a := (82155252054747 / 100000000000000 : ℝ)) (b := (159770170099 / 100000000000000 : ℝ)) (q := (139308996663 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12890])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12890])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12890]

theorem cert12890_57 : CellCertificate 12890 (88145768394063 / 1000000000000000 : ℝ) (407376394632887 / 250000000000000000 : ℝ) (329036678495491 / 10000000000000000 : ℝ)
    (cell12890 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · have h := gap_lower (n := 12890) (a := (82121677687523 / 100000000000000 : ℝ)) (b := (159770170099 / 100000000000000 : ℝ)) (q := (2228947928931 / 100000000000000 : ℝ))
      (E := (cell12890 ⟨57, by decide⟩).energy) (xi := (329036678495491 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12890 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12890]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12890])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12890) (a := (82121677687523 / 100000000000000 : ℝ)) (b := (159770170099 / 100000000000000 : ℝ)) (q := (2228947928931 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12890])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12890])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12890]

theorem cert12890_58 : CellCertificate 12890 (88145768394063 / 1000000000000000 : ℝ) (407376394632887 / 250000000000000000 : ℝ) (329036678495491 / 10000000000000000 : ℝ)
    (cell12890 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · have h := gap_lower (n := 12890) (a := (82088126399209 / 100000000000000 : ℝ)) (b := (159770170099 / 100000000000000 : ℝ)) (q := (445790390291 / 20000000000000 : ℝ))
      (E := (cell12890 ⟨58, by decide⟩).energy) (xi := (329036678495491 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12890 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12890]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12890])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12890) (a := (82088126399209 / 100000000000000 : ℝ)) (b := (159770170099 / 100000000000000 : ℝ)) (q := (445790390291 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12890])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12890])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12890]

theorem cert12890_59 : CellCertificate 12890 (88145768394063 / 1000000000000000 : ℝ) (407376394632887 / 250000000000000000 : ℝ) (329036678495491 / 10000000000000000 : ℝ)
    (cell12890 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · have h := gap_lower (n := 12890) (a := (16410919632507 / 20000000000000 : ℝ)) (b := (159770170099 / 100000000000000 : ℝ)) (q := (2228955950579 / 100000000000000 : ℝ))
      (E := (cell12890 ⟨59, by decide⟩).energy) (xi := (329036678495491 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12890 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12890]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12890])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12890) (a := (16410919632507 / 20000000000000 : ℝ)) (b := (159770170099 / 100000000000000 : ℝ)) (q := (2228955950579 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12890])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12890])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12890]

theorem cert12891_40 : CellCertificate 12891 (110178816757517 / 1250000000000000 : ℝ) (814689565566723 / 500000000000000000 : ℝ) (329010550204659 / 10000000000000000 : ℝ)
    (cell12891 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · have h := gap_lower (n := 12891) (a := (82695600943827 / 100000000000000 : ℝ)) (b := (159757629583 / 100000000000000 : ℝ)) (q := (1114381417967 / 50000000000000 : ℝ))
      (E := (cell12891 ⟨40, by decide⟩).energy) (xi := (329010550204659 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12891 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12891]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12891])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12891) (a := (82695600943827 / 100000000000000 : ℝ)) (b := (159757629583 / 100000000000000 : ℝ)) (q := (1114381417967 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12891])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12891])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12891]

theorem cert12891_41 : CellCertificate 12891 (110178816757517 / 1250000000000000 : ℝ) (814689565566723 / 500000000000000000 : ℝ) (329010550204659 / 10000000000000000 : ℝ)
    (cell12891 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · have h := gap_lower (n := 12891) (a := (661293230299 / 800000000000 : ℝ)) (b := (159757629583 / 100000000000000 : ℝ)) (q := (2228766807429 / 100000000000000 : ℝ))
      (E := (cell12891 ⟨41, by decide⟩).energy) (xi := (329010550204659 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12891 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12891]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12891])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12891) (a := (661293230299 / 800000000000 : ℝ)) (b := (159757629583 / 100000000000000 : ℝ)) (q := (2228766807429 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12891])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12891])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12891]

theorem cert12891_42 : CellCertificate 12891 (110178816757517 / 1250000000000000 : ℝ) (814689565566723 / 500000000000000000 : ℝ) (329010550204659 / 10000000000000000 : ℝ)
    (cell12891 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · have h := gap_lower (n := 12891) (a := (2065693254121 / 2500000000000 : ℝ)) (b := (159757629583 / 100000000000000 : ℝ)) (q := (2228770862377 / 100000000000000 : ℝ))
      (E := (cell12891 ⟨42, by decide⟩).energy) (xi := (329010550204659 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12891 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12891]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12891])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12891) (a := (2065693254121 / 2500000000000 : ℝ)) (b := (159757629583 / 100000000000000 : ℝ)) (q := (2228770862377 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12891])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12891])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12891]

theorem cert12891_43 : CellCertificate 12891 (110178816757517 / 1250000000000000 : ℝ) (814689565566723 / 500000000000000000 : ℝ) (329010550204659 / 10000000000000000 : ℝ)
    (cell12891 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · have h := gap_lower (n := 12891) (a := (41296915023337 / 50000000000000 : ℝ)) (b := (159757629583 / 100000000000000 : ℝ)) (q := (69649213227 / 3125000000000 : ℝ))
      (E := (cell12891 ⟨43, by decide⟩).energy) (xi := (329010550204659 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12891 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12891]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12891])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12891) (a := (41296915023337 / 50000000000000 : ℝ)) (b := (159757629583 / 100000000000000 : ℝ)) (q := (69649213227 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12891])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12891])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12891]

theorem cert12891_44 : CellCertificate 12891 (110178816757517 / 1250000000000000 : ℝ) (814689565566723 / 500000000000000000 : ℝ) (329010550204659 / 10000000000000000 : ℝ)
    (cell12891 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · have h := gap_lower (n := 12891) (a := (41279976701739 / 50000000000000 : ℝ)) (b := (159757629583 / 100000000000000 : ℝ)) (q := (2228778865229 / 100000000000000 : ℝ))
      (E := (cell12891 ⟨44, by decide⟩).energy) (xi := (329010550204659 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12891 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12891]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12891])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12891) (a := (41279976701739 / 50000000000000 : ℝ)) (b := (159757629583 / 100000000000000 : ℝ)) (q := (2228778865229 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12891])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12891])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12891]

theorem cert12891_45 : CellCertificate 12891 (110178816757517 / 1250000000000000 : ℝ) (814689565566723 / 500000000000000000 : ℝ) (329010550204659 / 10000000000000000 : ℝ)
    (cell12891 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · have h := gap_lower (n := 12891) (a := (41263050103 / 50000000000 : ℝ)) (b := (159757629583 / 100000000000000 : ℝ)) (q := (557195717267 / 25000000000000 : ℝ))
      (E := (cell12891 ⟨45, by decide⟩).energy) (xi := (329010550204659 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12891 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12891]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12891])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12891) (a := (41263050103 / 50000000000 : ℝ)) (b := (159757629583 / 100000000000000 : ℝ)) (q := (557195717267 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12891])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12891])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12891]

theorem cert12891_46 : CellCertificate 12891 (110178816757517 / 1250000000000000 : ℝ) (814689565566723 / 500000000000000000 : ℝ) (329010550204659 / 10000000000000000 : ℝ)
    (cell12891 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · have h := gap_lower (n := 12891) (a := (5155766901571 / 6250000000000 : ℝ)) (b := (159757629583 / 100000000000000 : ℝ)) (q := (2228786891887 / 100000000000000 : ℝ))
      (E := (cell12891 ⟨46, by decide⟩).energy) (xi := (329010550204659 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12891 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12891]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12891])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12891) (a := (5155766901571 / 6250000000000 : ℝ)) (b := (159757629583 / 100000000000000 : ℝ)) (q := (2228786891887 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12891])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12891])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12891]

theorem cert12891_47 : CellCertificate 12891 (110178816757517 / 1250000000000000 : ℝ) (814689565566723 / 500000000000000000 : ℝ) (329010550204659 / 10000000000000000 : ℝ)
    (cell12891 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · have h := gap_lower (n := 12891) (a := (82458464031927 / 100000000000000 : ℝ)) (b := (159757629583 / 100000000000000 : ℝ)) (q := (445758174563 / 20000000000000 : ℝ))
      (E := (cell12891 ⟨47, by decide⟩).energy) (xi := (329010550204659 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12891 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12891]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12891])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12891) (a := (82458464031927 / 100000000000000 : ℝ)) (b := (159757629583 / 100000000000000 : ℝ)) (q := (445758174563 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12891])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12891])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12891]

theorem cert12891_48 : CellCertificate 12891 (110178816757517 / 1250000000000000 : ℝ) (814689565566723 / 500000000000000000 : ℝ) (329010550204659 / 10000000000000000 : ℝ)
    (cell12891 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · have h := gap_lower (n := 12891) (a := (2060617024939 / 2500000000000 : ℝ)) (b := (159757629583 / 100000000000000 : ℝ)) (q := (2228794868579 / 100000000000000 : ℝ))
      (E := (cell12891 ⟨48, by decide⟩).energy) (xi := (329010550204659 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12891 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12891]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12891])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12891) (a := (2060617024939 / 2500000000000 : ℝ)) (b := (159757629583 / 100000000000000 : ℝ)) (q := (2228794868579 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12891])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12891])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12891]

theorem cert12891_49 : CellCertificate 12891 (110178816757517 / 1250000000000000 : ℝ) (814689565566723 / 500000000000000000 : ℝ) (329010550204659 / 10000000000000000 : ℝ)
    (cell12891 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · have h := gap_lower (n := 12891) (a := (16478184258673 / 20000000000000 : ℝ)) (b := (159757629583 / 100000000000000 : ℝ)) (q := (557199719203 / 25000000000000 : ℝ))
      (E := (cell12891 ⟨49, by decide⟩).energy) (xi := (329010550204659 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12891 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12891]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12891])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12891) (a := (16478184258673 / 20000000000000 : ℝ)) (b := (159757629583 / 100000000000000 : ℝ)) (q := (557199719203 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12891])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12891])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12891]

theorem cert12891_50 : CellCertificate 12891 (110178816757517 / 1250000000000000 : ℝ) (814689565566723 / 500000000000000000 : ℝ) (329010550204659 / 10000000000000000 : ℝ)
    (cell12891 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · have h := gap_lower (n := 12891) (a := (82357184890819 / 100000000000000 : ℝ)) (b := (159757629583 / 100000000000000 : ℝ)) (q := (139300180933 / 6250000000000 : ℝ))
      (E := (cell12891 ⟨50, by decide⟩).energy) (xi := (329010550204659 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12891 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12891]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12891])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12891) (a := (82357184890819 / 100000000000000 : ℝ)) (b := (159757629583 / 100000000000000 : ℝ)) (q := (139300180933 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12891])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12891])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12891]

theorem cert12891_51 : CellCertificate 12891 (110178816757517 / 1250000000000000 : ℝ) (814689565566723 / 500000000000000000 : ℝ) (329010550204659 / 10000000000000000 : ℝ)
    (cell12891 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · have h := gap_lower (n := 12891) (a := (82323471761537 / 100000000000000 : ℝ)) (b := (159757629583 / 100000000000000 : ℝ)) (q := (1114403460069 / 50000000000000 : ℝ))
      (E := (cell12891 ⟨51, by decide⟩).energy) (xi := (329010550204659 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12891 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12891]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12891])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12891) (a := (82323471761537 / 100000000000000 : ℝ)) (b := (159757629583 / 100000000000000 : ℝ)) (q := (1114403460069 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12891])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12891])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12891]

theorem cert12891_52 : CellCertificate 12891 (110178816757517 / 1250000000000000 : ℝ) (814689565566723 / 500000000000000000 : ℝ) (329010550204659 / 10000000000000000 : ℝ)
    (cell12891 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · have h := gap_lower (n := 12891) (a := (82289781877279 / 100000000000000 : ℝ)) (b := (159757629583 / 100000000000000 : ℝ)) (q := (1114405474719 / 50000000000000 : ℝ))
      (E := (cell12891 ⟨52, by decide⟩).energy) (xi := (329010550204659 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12891 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12891]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12891])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12891) (a := (82289781877279 / 100000000000000 : ℝ)) (b := (159757629583 / 100000000000000 : ℝ)) (q := (1114405474719 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12891])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12891])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12891]

theorem cert12891_53 : CellCertificate 12891 (110178816757517 / 1250000000000000 : ℝ) (814689565566723 / 500000000000000000 : ℝ) (329010550204659 / 10000000000000000 : ℝ)
    (cell12891 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · have h := gap_lower (n := 12891) (a := (41128057604973 / 50000000000000 : ℝ)) (b := (159757629583 / 100000000000000 : ℝ)) (q := (1114407460271 / 50000000000000 : ℝ))
      (E := (cell12891 ⟨53, by decide⟩).energy) (xi := (329010550204659 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12891 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12891]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12891])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12891) (a := (41128057604973 / 50000000000000 : ℝ)) (b := (159757629583 / 100000000000000 : ℝ)) (q := (1114407460271 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12891])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12891])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12891]

theorem cert12891_54 : CellCertificate 12891 (110178816757517 / 1250000000000000 : ℝ) (814689565566723 / 500000000000000000 : ℝ) (329010550204659 / 10000000000000000 : ℝ)
    (cell12891 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · have h := gap_lower (n := 12891) (a := (82222471731577 / 100000000000000 : ℝ)) (b := (159757629583 / 100000000000000 : ℝ)) (q := (2228818948147 / 100000000000000 : ℝ))
      (E := (cell12891 ⟨54, by decide⟩).energy) (xi := (329010550204659 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12891 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12891]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12891])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12891) (a := (82222471731577 / 100000000000000 : ℝ)) (b := (159757629583 / 100000000000000 : ℝ)) (q := (2228818948147 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12891])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12891])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12891]

theorem cert12891_55 : CellCertificate 12891 (110178816757517 / 1250000000000000 : ℝ) (814689565566723 / 500000000000000000 : ℝ) (329010550204659 / 10000000000000000 : ℝ)
    (cell12891 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · have h := gap_lower (n := 12891) (a := (41094425707177 / 50000000000000 : ℝ)) (b := (159757629583 / 100000000000000 : ℝ)) (q := (2228822969573 / 100000000000000 : ℝ))
      (E := (cell12891 ⟨55, by decide⟩).energy) (xi := (329010550204659 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12891 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12891]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12891])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12891) (a := (41094425707177 / 50000000000000 : ℝ)) (b := (159757629583 / 100000000000000 : ℝ)) (q := (2228822969573 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12891])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12891])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12891]

theorem cert12891_56 : CellCertificate 12891 (110178816757517 / 1250000000000000 : ℝ) (814689565566723 / 500000000000000000 : ℝ) (329010550204659 / 10000000000000000 : ℝ)
    (cell12891 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · have h := gap_lower (n := 12891) (a := (16431050846119 / 20000000000000 : ℝ)) (b := (159757629583 / 100000000000000 : ℝ)) (q := (2228826980981 / 100000000000000 : ℝ))
      (E := (cell12891 ⟨56, by decide⟩).energy) (xi := (329010550204659 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12891 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12891]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12891])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12891) (a := (16431050846119 / 20000000000000 : ℝ)) (b := (159757629583 / 100000000000000 : ℝ)) (q := (2228826980981 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12891])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12891])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12891]

theorem cert12891_57 : CellCertificate 12891 (110178816757517 / 1250000000000000 : ℝ) (814689565566723 / 500000000000000000 : ℝ) (329010550204659 / 10000000000000000 : ℝ)
    (cell12891 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · have h := gap_lower (n := 12891) (a := (16424336030551 / 20000000000000 : ℝ)) (b := (159757629583 / 100000000000000 : ℝ)) (q := (278603872291 / 12500000000000 : ℝ))
      (E := (cell12891 ⟨57, by decide⟩).energy) (xi := (329010550204659 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12891 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12891]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12891])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12891) (a := (16424336030551 / 20000000000000 : ℝ)) (b := (159757629583 / 100000000000000 : ℝ)) (q := (278603872291 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12891])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12891])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12891]

theorem cert12891_58 : CellCertificate 12891 (110178816757517 / 1250000000000000 : ℝ) (814689565566723 / 500000000000000000 : ℝ) (329010550204659 / 10000000000000000 : ℝ)
    (cell12891 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · have h := gap_lower (n := 12891) (a := (8208812915343 / 10000000000000 : ℝ)) (b := (159757629583 / 100000000000000 : ℝ)) (q := (2228834957357 / 100000000000000 : ℝ))
      (E := (cell12891 ⟨58, by decide⟩).energy) (xi := (329010550204659 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12891 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12891]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12891])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12891) (a := (8208812915343 / 10000000000000 : ℝ)) (b := (159757629583 / 100000000000000 : ℝ)) (q := (2228834957357 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12891])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12891])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12891]

theorem cert12891_59 : CellCertificate 12891 (110178816757517 / 1250000000000000 : ℝ) (814689565566723 / 500000000000000000 : ℝ) (329010550204659 / 10000000000000000 : ℝ)
    (cell12891 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · have h := gap_lower (n := 12891) (a := (20513650301337 / 25000000000000 : ℝ)) (b := (159757629583 / 100000000000000 : ℝ)) (q := (1114419486413 / 50000000000000 : ℝ))
      (E := (cell12891 ⟨59, by decide⟩).energy) (xi := (329010550204659 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12891 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12891]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12891])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12891) (a := (20513650301337 / 25000000000000 : ℝ)) (b := (159757629583 / 100000000000000 : ℝ)) (q := (1114419486413 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12891])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12891])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12891]

theorem cert12892_40 : CellCertificate 12892 (881403388217793 / 10000000000000000 : ℝ) (1629252703358109 / 1000000000000000000 : ℝ) (164492213053009 / 5000000000000000 : ℝ)
    (cell12892 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · have h := gap_lower (n := 12892) (a := (16539119687179 / 20000000000000 : ℝ)) (b := (79872545523 / 50000000000000 : ℝ)) (q := (557161473819 / 25000000000000 : ℝ))
      (E := (cell12892 ⟨40, by decide⟩).energy) (xi := (164492213053009 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12892 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12892]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12892])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12892) (a := (16539119687179 / 20000000000000 : ℝ)) (b := (79872545523 / 50000000000000 : ℝ)) (q := (557161473819 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12892])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12892])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12892]

theorem cert12892_41 : CellCertificate 12892 (881403388217793 / 10000000000000000 : ℝ) (1629252703358109 / 1000000000000000000 : ℝ) (164492213053009 / 5000000000000000 : ℝ)
    (cell12892 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · have h := gap_lower (n := 12892) (a := (41330825787613 / 50000000000000 : ℝ)) (b := (79872545523 / 50000000000000 : ℝ)) (q := (1114324935523 / 50000000000000 : ℝ))
      (E := (cell12892 ⟨41, by decide⟩).energy) (xi := (164492213053009 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12892 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12892]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12892])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12892) (a := (41330825787613 / 50000000000000 : ℝ)) (b := (79872545523 / 50000000000000 : ℝ)) (q := (1114324935523 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12892])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12892])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12892]

theorem cert12892_42 : CellCertificate 12892 (881403388217793 / 10000000000000000 : ℝ) (1629252703358109 / 1000000000000000000 : ℝ) (164492213053009 / 5000000000000000 : ℝ)
    (cell12892 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · have h := gap_lower (n := 12892) (a := (82627728248067 / 100000000000000 : ℝ)) (b := (79872545523 / 50000000000000 : ℝ)) (q := (111432693607 / 5000000000000 : ℝ))
      (E := (cell12892 ⟨42, by decide⟩).energy) (xi := (164492213053009 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12892 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12892]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12892])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12892) (a := (82627728248067 / 100000000000000 : ℝ)) (b := (79872545523 / 50000000000000 : ℝ)) (q := (111432693607 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12892])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12892])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12892]

theorem cert12892_43 : CellCertificate 12892 (881403388217793 / 10000000000000000 : ℝ) (1629252703358109 / 1000000000000000000 : ℝ) (164492213053009 / 5000000000000000 : ℝ)
    (cell12892 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · have h := gap_lower (n := 12892) (a := (82593828424871 / 100000000000000 : ℝ)) (b := (79872545523 / 50000000000000 : ℝ)) (q := (2228657897479 / 100000000000000 : ℝ))
      (E := (cell12892 ⟨43, by decide⟩).energy) (xi := (164492213053009 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12892 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12892]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12892])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12892) (a := (82593828424871 / 100000000000000 : ℝ)) (b := (79872545523 / 50000000000000 : ℝ)) (q := (2228657897479 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12892])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12892])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12892]

theorem cert12892_44 : CellCertificate 12892 (881403388217793 / 10000000000000000 : ℝ) (1629252703358109 / 1000000000000000000 : ℝ) (164492213053009 / 5000000000000000 : ℝ)
    (cell12892 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · have h := gap_lower (n := 12892) (a := (41279976038119 / 50000000000000 : ℝ)) (b := (79872545523 / 50000000000000 : ℝ)) (q := (557165471727 / 25000000000000 : ℝ))
      (E := (cell12892 ⟨44, by decide⟩).energy) (xi := (164492213053009 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12892 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12892]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12892])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12892) (a := (41279976038119 / 50000000000000 : ℝ)) (b := (79872545523 / 50000000000000 : ℝ)) (q := (557165471727 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12892])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12892])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12892]

theorem cert12892_45 : CellCertificate 12892 (881403388217793 / 10000000000000000 : ℝ) (1629252703358109 / 1000000000000000000 : ℝ) (164492213053009 / 5000000000000000 : ℝ)
    (cell12892 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · have h := gap_lower (n := 12892) (a := (41263049586459 / 50000000000000 : ℝ)) (b := (79872545523 / 50000000000000 : ℝ)) (q := (2228665897727 / 100000000000000 : ℝ))
      (E := (cell12892 ⟨45, by decide⟩).energy) (xi := (164492213053009 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12892 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12892]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12892])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12892) (a := (41263049586459 / 50000000000000 : ℝ)) (b := (79872545523 / 50000000000000 : ℝ)) (q := (2228665897727 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12892])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12892])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12892]

theorem cert12892_46 : CellCertificate 12892 (881403388217793 / 10000000000000000 : ℝ) (1629252703358109 / 1000000000000000000 : ℝ) (164492213053009 / 5000000000000000 : ℝ)
    (cell12892 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · have h := gap_lower (n := 12892) (a := (5155766855363 / 6250000000000 : ℝ)) (b := (79872545523 / 50000000000000 : ℝ)) (q := (2228669928207 / 100000000000000 : ℝ))
      (E := (cell12892 ⟨46, by decide⟩).energy) (xi := (164492213053009 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12892 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12892]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12892])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12892) (a := (5155766855363 / 6250000000000 : ℝ)) (b := (79872545523 / 50000000000000 : ℝ)) (q := (2228669928207 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12892])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12892])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12892]

theorem cert12892_47 : CellCertificate 12892 (881403388217793 / 10000000000000000 : ℝ) (1629252703358109 / 1000000000000000000 : ℝ) (164492213053009 / 5000000000000000 : ℝ)
    (cell12892 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · have h := gap_lower (n := 12892) (a := (20614615896487 / 25000000000000 : ℝ)) (b := (79872545523 / 50000000000000 : ℝ)) (q := (2228673917477 / 100000000000000 : ℝ))
      (E := (cell12892 ⟨47, by decide⟩).energy) (xi := (164492213053009 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12892 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12892]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12892])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12892) (a := (20614615896487 / 25000000000000 : ℝ)) (b := (79872545523 / 50000000000000 : ℝ)) (q := (2228673917477 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12892])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12892])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12892]

theorem cert12892_48 : CellCertificate 12892 (881403388217793 / 10000000000000000 : ℝ) (1629252703358109 / 1000000000000000000 : ℝ) (164492213053009 / 5000000000000000 : ℝ)
    (cell12892 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · have h := gap_lower (n := 12892) (a := (5151542552783 / 6250000000000 : ℝ)) (b := (79872545523 / 50000000000000 : ℝ)) (q := (2228677922261 / 100000000000000 : ℝ))
      (E := (cell12892 ⟨48, by decide⟩).energy) (xi := (164492213053009 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12892 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12892]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12892])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12892) (a := (5151542552783 / 6250000000000 : ℝ)) (b := (79872545523 / 50000000000000 : ℝ)) (q := (2228677922261 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12892])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12892])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12892]

theorem cert12892_49 : CellCertificate 12892 (881403388217793 / 10000000000000000 : ℝ) (1629252703358109 / 1000000000000000000 : ℝ) (164492213053009 / 5000000000000000 : ℝ)
    (cell12892 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · have h := gap_lower (n := 12892) (a := (41195460716439 / 50000000000000 : ℝ)) (b := (79872545523 / 50000000000000 : ℝ)) (q := (2228681940191 / 100000000000000 : ℝ))
      (E := (cell12892 ⟨49, by decide⟩).energy) (xi := (164492213053009 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12892 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12892]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12892])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12892) (a := (41195460716439 / 50000000000000 : ℝ)) (b := (79872545523 / 50000000000000 : ℝ)) (q := (2228681940191 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12892])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12892])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12892]

theorem cert12892_50 : CellCertificate 12892 (881403388217793 / 10000000000000000 : ℝ) (1629252703358109 / 1000000000000000000 : ℝ) (164492213053009 / 5000000000000000 : ℝ)
    (cell12892 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · have h := gap_lower (n := 12892) (a := (41178592661237 / 50000000000000 : ℝ)) (b := (79872545523 / 50000000000000 : ℝ)) (q := (445737193737 / 20000000000000 : ℝ))
      (E := (cell12892 ⟨50, by decide⟩).energy) (xi := (164492213053009 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12892 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12892]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12892])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12892) (a := (41178592661237 / 50000000000000 : ℝ)) (b := (79872545523 / 50000000000000 : ℝ)) (q := (445737193737 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12892])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12892])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12892]

theorem cert12892_51 : CellCertificate 12892 (881403388217793 / 10000000000000000 : ℝ) (1629252703358109 / 1000000000000000000 : ℝ) (164492213053009 / 5000000000000000 : ℝ)
    (cell12892 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · have h := gap_lower (n := 12892) (a := (82323472484933 / 100000000000000 : ℝ)) (b := (79872545523 / 50000000000000 : ℝ)) (q := (2228689945927 / 100000000000000 : ℝ))
      (E := (cell12892 ⟨51, by decide⟩).energy) (xi := (164492213053009 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12892 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12892]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12892])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12892) (a := (82323472484933 / 100000000000000 : ℝ)) (b := (79872545523 / 50000000000000 : ℝ)) (q := (2228689945927 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12892])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12892])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12892]

theorem cert12892_52 : CellCertificate 12892 (881403388217793 / 10000000000000000 : ℝ) (1629252703358109 / 1000000000000000000 : ℝ) (164492213053009 / 5000000000000000 : ℝ)
    (cell12892 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · have h := gap_lower (n := 12892) (a := (82289782892017 / 100000000000000 : ℝ)) (b := (79872545523 / 50000000000000 : ℝ)) (q := (2228693986933 / 100000000000000 : ℝ))
      (E := (cell12892 ⟨52, by decide⟩).energy) (xi := (164492213053009 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12892 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12892]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12892])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12892) (a := (82289782892017 / 100000000000000 : ℝ)) (b := (79872545523 / 50000000000000 : ℝ)) (q := (2228693986933 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12892])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12892])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12892]

theorem cert12892_53 : CellCertificate 12892 (881403388217793 / 10000000000000000 : ℝ) (1629252703358109 / 1000000000000000000 : ℝ) (164492213053009 / 5000000000000000 : ℝ)
    (cell12892 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · have h := gap_lower (n := 12892) (a := (5264391457 / 6400000000 : ℝ)) (b := (79872545523 / 50000000000000 : ℝ)) (q := (2228697970421 / 100000000000000 : ℝ))
      (E := (cell12892 ⟨53, by decide⟩).energy) (xi := (164492213053009 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12892 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12892]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12892])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12892) (a := (5264391457 / 6400000000 : ℝ)) (b := (79872545523 / 50000000000000 : ℝ)) (q := (2228697970421 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12892])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12892])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12892]

theorem cert12892_54 : CellCertificate 12892 (881403388217793 / 10000000000000000 : ℝ) (1629252703358109 / 1000000000000000000 : ℝ) (164492213053009 / 5000000000000000 : ℝ)
    (cell12892 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · have h := gap_lower (n := 12892) (a := (411112366639 / 500000000000 : ℝ)) (b := (79872545523 / 50000000000000 : ℝ)) (q := (557175502771 / 25000000000000 : ℝ))
      (E := (cell12892 ⟨54, by decide⟩).energy) (xi := (164492213053009 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12892 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12892]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12892])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12892) (a := (411112366639 / 500000000000 : ℝ)) (b := (79872545523 / 50000000000000 : ℝ)) (q := (557175502771 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12892])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12892])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12892]

theorem cert12892_55 : CellCertificate 12892 (881403388217793 / 10000000000000000 : ℝ) (1629252703358109 / 1000000000000000000 : ℝ) (164492213053009 / 5000000000000000 : ℝ)
    (cell12892 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · have h := gap_lower (n := 12892) (a := (82188853300721 / 100000000000000 : ℝ)) (b := (79872545523 / 50000000000000 : ℝ)) (q := (1114352993563 / 50000000000000 : ℝ))
      (E := (cell12892 ⟨55, by decide⟩).energy) (xi := (164492213053009 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12892 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12892]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12892])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12892) (a := (82188853300721 / 100000000000000 : ℝ)) (b := (79872545523 / 50000000000000 : ℝ)) (q := (1114352993563 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12892])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12892])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12892]

theorem cert12892_56 : CellCertificate 12892 (881403388217793 / 10000000000000000 : ℝ) (1629252703358109 / 1000000000000000000 : ℝ) (164492213053009 / 5000000000000000 : ℝ)
    (cell12892 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · have h := gap_lower (n := 12892) (a := (20538814101677 / 25000000000000 : ℝ)) (b := (79872545523 / 50000000000000 : ℝ)) (q := (2228710012919 / 100000000000000 : ℝ))
      (E := (cell12892 ⟨56, by decide⟩).energy) (xi := (164492213053009 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12892 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12892]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12892])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12892) (a := (20538814101677 / 25000000000000 : ℝ)) (b := (79872545523 / 50000000000000 : ℝ)) (q := (2228710012919 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12892])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12892])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12892]

theorem cert12892_57 : CellCertificate 12892 (881403388217793 / 10000000000000000 : ℝ) (1629252703358109 / 1000000000000000000 : ℝ) (164492213053009 / 5000000000000000 : ℝ)
    (cell12892 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · have h := gap_lower (n := 12892) (a := (82121682618219 / 100000000000000 : ℝ)) (b := (79872545523 / 50000000000000 : ℝ)) (q := (1114357012661 / 50000000000000 : ℝ))
      (E := (cell12892 ⟨57, by decide⟩).energy) (xi := (164492213053009 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12892 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12892]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12892])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12892) (a := (82121682618219 / 100000000000000 : ℝ)) (b := (79872545523 / 50000000000000 : ℝ)) (q := (1114357012661 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12892])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12892])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12892]

theorem cert12892_58 : CellCertificate 12892 (881403388217793 / 10000000000000000 : ℝ) (1629252703358109 / 1000000000000000000 : ℝ) (164492213053009 / 5000000000000000 : ℝ)
    (cell12892 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · have h := gap_lower (n := 12892) (a := (82088131907847 / 100000000000000 : ℝ)) (b := (79872545523 / 50000000000000 : ℝ)) (q := (1114359010041 / 50000000000000 : ℝ))
      (E := (cell12892 ⟨58, by decide⟩).energy) (xi := (164492213053009 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12892 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12892]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12892])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12892) (a := (82088131907847 / 100000000000000 : ℝ)) (b := (79872545523 / 50000000000000 : ℝ)) (q := (1114359010041 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12892])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12892])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12892]

theorem cert12892_59 : CellCertificate 12892 (881403388217793 / 10000000000000000 : ℝ) (1629252703358109 / 1000000000000000000 : ℝ) (164492213053009 / 5000000000000000 : ℝ)
    (cell12892 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · have h := gap_lower (n := 12892) (a := (20513651062081 / 25000000000000 : ℝ)) (b := (79872545523 / 50000000000000 : ℝ)) (q := (139295128247 / 6250000000000 : ℝ))
      (E := (cell12892 ⟨59, by decide⟩).energy) (xi := (164492213053009 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12892 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12892]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12892])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12892) (a := (20513651062081 / 25000000000000 : ℝ)) (b := (79872545523 / 50000000000000 : ℝ)) (q := (139295128247 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12892])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12892])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12892]

theorem cert12893_40 : CellCertificate 12893 (440688123206329 / 5000000000000000 : ℝ) (162912629520097 / 100000000000000000 : ℝ) (328958306198489 / 10000000000000000 : ℝ)
    (cell12893 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · have h := gap_lower (n := 12893) (a := (82695595928787 / 100000000000000 : ℝ)) (b := (159732554487 / 100000000000000 : ℝ)) (q := (2228528951611 / 100000000000000 : ℝ))
      (E := (cell12893 ⟨40, by decide⟩).energy) (xi := (328958306198489 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12893 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12893]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12893])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12893) (a := (82695595928787 / 100000000000000 : ℝ)) (b := (159732554487 / 100000000000000 : ℝ)) (q := (2228528951611 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12893])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12893])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12893]

theorem cert12893_41 : CellCertificate 12893 (440688123206329 / 5000000000000000 : ℝ) (162912629520097 / 100000000000000000 : ℝ) (328958306198489 / 10000000000000000 : ℝ)
    (cell12893 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · have h := gap_lower (n := 12893) (a := (82661649363867 / 100000000000000 : ℝ)) (b := (159732554487 / 100000000000000 : ℝ)) (q := (2228532931691 / 100000000000000 : ℝ))
      (E := (cell12893 ⟨41, by decide⟩).energy) (xi := (328958306198489 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12893 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12893]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12893])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12893) (a := (82661649363867 / 100000000000000 : ℝ)) (b := (159732554487 / 100000000000000 : ℝ)) (q := (2228532931691 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12893])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12893])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12893]

theorem cert12893_42 : CellCertificate 12893 (440688123206329 / 5000000000000000 : ℝ) (162912629520097 / 100000000000000000 : ℝ) (328958306198489 / 10000000000000000 : ℝ)
    (cell12893 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · have h := gap_lower (n := 12893) (a := (5164232895753 / 6250000000000 : ℝ)) (b := (159732554487 / 100000000000000 : ℝ)) (q := (111426846889 / 5000000000000 : ℝ))
      (E := (cell12893 ⟨42, by decide⟩).energy) (xi := (328958306198489 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12893 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12893]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12893])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12893) (a := (5164232895753 / 6250000000000 : ℝ)) (b := (159732554487 / 100000000000000 : ℝ)) (q := (111426846889 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12893])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12893])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12893]

theorem cert12893_43 : CellCertificate 12893 (440688123206329 / 5000000000000000 : ℝ) (162912629520097 / 100000000000000000 : ℝ) (328958306198489 / 10000000000000000 : ℝ)
    (cell12893 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · have h := gap_lower (n := 12893) (a := (41296913401893 / 50000000000000 : ℝ)) (b := (159732554487 / 100000000000000 : ℝ)) (q := (445708193759 / 20000000000000 : ℝ))
      (E := (cell12893 ⟨43, by decide⟩).energy) (xi := (328958306198489 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12893 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12893]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12893])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12893) (a := (41296913401893 / 50000000000000 : ℝ)) (b := (159732554487 / 100000000000000 : ℝ)) (q := (445708193759 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12893])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12893])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12893]

theorem cert12893_44 : CellCertificate 12893 (440688123206329 / 5000000000000000 : ℝ) (162912629520097 / 100000000000000000 : ℝ) (328958306198489 / 10000000000000000 : ℝ)
    (cell12893 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · have h := gap_lower (n := 12893) (a := (41279975374841 / 50000000000000 : ℝ)) (b := (159732554487 / 100000000000000 : ℝ)) (q := (2228544964583 / 100000000000000 : ℝ))
      (E := (cell12893 ⟨44, by decide⟩).energy) (xi := (328958306198489 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12893 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12893]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12893])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12893) (a := (41279975374841 / 50000000000000 : ℝ)) (b := (159732554487 / 100000000000000 : ℝ)) (q := (2228544964583 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12893])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12893])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12893]

theorem cert12893_45 : CellCertificate 12893 (440688123206329 / 5000000000000000 : ℝ) (162912629520097 / 100000000000000000 : ℝ) (328958306198489 / 10000000000000000 : ℝ)
    (cell12893 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · have h := gap_lower (n := 12893) (a := (16505219628097 / 20000000000000 : ℝ)) (b := (159732554487 / 100000000000000 : ℝ)) (q := (2228548982441 / 100000000000000 : ℝ))
      (E := (cell12893 ⟨45, by decide⟩).energy) (xi := (328958306198489 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12893 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12893]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12893])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12893) (a := (16505219628097 / 20000000000000 : ℝ)) (b := (159732554487 / 100000000000000 : ℝ)) (q := (2228548982441 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12893])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12893])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12893]

theorem cert12893_46 : CellCertificate 12893 (440688123206329 / 5000000000000000 : ℝ) (162912629520097 / 100000000000000000 : ℝ) (328958306198489 / 10000000000000000 : ℝ)
    (cell12893 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · have h := gap_lower (n := 12893) (a := (82492268947093 / 100000000000000 : ℝ)) (b := (159732554487 / 100000000000000 : ℝ)) (q := (278569120217 / 12500000000000 : ℝ))
      (E := (cell12893 ⟨46, by decide⟩).energy) (xi := (328958306198489 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12893 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12893]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12893])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12893) (a := (82492268947093 / 100000000000000 : ℝ)) (b := (159732554487 / 100000000000000 : ℝ)) (q := (278569120217 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12893])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12893])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12893]

theorem cert12893_47 : CellCertificate 12893 (440688123206329 / 5000000000000000 : ℝ) (162912629520097 / 100000000000000000 : ℝ) (328958306198489 / 10000000000000000 : ℝ)
    (cell12893 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · have h := gap_lower (n := 12893) (a := (20614615785137 / 25000000000000 : ℝ)) (b := (159732554487 / 100000000000000 : ℝ)) (q := (278569627289 / 12500000000000 : ℝ))
      (E := (cell12893 ⟨47, by decide⟩).energy) (xi := (328958306198489 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12893 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12893]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12893])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12893) (a := (20614615785137 / 25000000000000 : ℝ)) (b := (159732554487 / 100000000000000 : ℝ)) (q := (278569627289 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12893])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12893])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12893]

theorem cert12893_48 : CellCertificate 12893 (440688123206329 / 5000000000000000 : ℝ) (162912629520097 / 100000000000000000 : ℝ) (328958306198489 / 10000000000000000 : ℝ)
    (cell12893 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · have h := gap_lower (n := 12893) (a := (2060617017301 / 2500000000000 : ℝ)) (b := (159732554487 / 100000000000000 : ℝ)) (q := (2228560973223 / 100000000000000 : ℝ))
      (E := (cell12893 ⟨48, by decide⟩).energy) (xi := (328958306198489 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12893 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12893]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12893])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12893) (a := (2060617017301 / 2500000000000 : ℝ)) (b := (159732554487 / 100000000000000 : ℝ)) (q := (2228560973223 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12893])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12893])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12893]

theorem cert12893_49 : CellCertificate 12893 (440688123206329 / 5000000000000000 : ℝ) (162912629520097 / 100000000000000000 : ℝ) (328958306198489 / 10000000000000000 : ℝ)
    (cell12893 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · have h := gap_lower (n := 12893) (a := (82390921572899 / 100000000000000 : ℝ)) (b := (159732554487 / 100000000000000 : ℝ)) (q := (278570625111 / 12500000000000 : ℝ))
      (E := (cell12893 ⟨49, by decide⟩).energy) (xi := (328958306198489 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12893 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12893]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12893])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12893) (a := (82390921572899 / 100000000000000 : ℝ)) (b := (159732554487 / 100000000000000 : ℝ)) (q := (278570625111 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12893])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12893])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12893]

theorem cert12893_50 : CellCertificate 12893 (440688123206329 / 5000000000000000 : ℝ) (162912629520097 / 100000000000000000 : ℝ) (328958306198489 / 10000000000000000 : ℝ)
    (cell12893 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · have h := gap_lower (n := 12893) (a := (41178592877301 / 50000000000000 : ℝ)) (b := (159732554487 / 100000000000000 : ℝ)) (q := (445713807959 / 20000000000000 : ℝ))
      (E := (cell12893 ⟨50, by decide⟩).energy) (xi := (328958306198489 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12893 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12893]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12893])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12893) (a := (41178592877301 / 50000000000000 : ℝ)) (b := (159732554487 / 100000000000000 : ℝ)) (q := (445713807959 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12893])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12893])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12893]

theorem cert12893_51 : CellCertificate 12893 (440688123206329 / 5000000000000000 : ℝ) (162912629520097 / 100000000000000000 : ℝ) (328958306198489 / 10000000000000000 : ℝ)
    (cell12893 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · have h := gap_lower (n := 12893) (a := (82323473208769 / 100000000000000 : ℝ)) (b := (159732554487 / 100000000000000 : ℝ)) (q := (713143369 / 32000000000 : ℝ))
      (E := (cell12893 ⟨51, by decide⟩).energy) (xi := (328958306198489 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12893 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12893]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12893])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12893) (a := (82323473208769 / 100000000000000 : ℝ)) (b := (159732554487 / 100000000000000 : ℝ)) (q := (713143369 / 32000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12893])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12893])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12893]

theorem cert12893_52 : CellCertificate 12893 (440688123206329 / 5000000000000000 : ℝ) (162912629520097 / 100000000000000000 : ℝ) (328958306198489 / 10000000000000000 : ℝ)
    (cell12893 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · have h := gap_lower (n := 12893) (a := (82289783907159 / 100000000000000 : ℝ)) (b := (159732554487 / 100000000000000 : ℝ)) (q := (2228577021851 / 100000000000000 : ℝ))
      (E := (cell12893 ⟨52, by decide⟩).energy) (xi := (328958306198489 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12893 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12893]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12893])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12893) (a := (82289783907159 / 100000000000000 : ℝ)) (b := (159732554487 / 100000000000000 : ℝ)) (q := (2228577021851 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12893])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12893])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12893]

theorem cert12893_53 : CellCertificate 12893 (440688123206329 / 5000000000000000 : ℝ) (162912629520097 / 100000000000000000 : ℝ) (328958306198489 / 10000000000000000 : ℝ)
    (cell12893 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · have h := gap_lower (n := 12893) (a := (41128058910837 / 50000000000000 : ℝ)) (b := (159732554487 / 100000000000000 : ℝ)) (q := (1114290508879 / 50000000000000 : ℝ))
      (E := (cell12893 ⟨53, by decide⟩).energy) (xi := (328958306198489 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12893 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12893]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12893])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12893) (a := (41128058910837 / 50000000000000 : ℝ)) (b := (159732554487 / 100000000000000 : ℝ)) (q := (1114290508879 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12893])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12893])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12893]

theorem cert12893_54 : CellCertificate 12893 (440688123206329 / 5000000000000000 : ℝ) (162912629520097 / 100000000000000000 : ℝ) (328958306198489 / 10000000000000000 : ℝ)
    (cell12893 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · have h := gap_lower (n := 12893) (a := (20555618731089 / 25000000000000 : ℝ)) (b := (159732554487 / 100000000000000 : ℝ)) (q := (557146267879 / 25000000000000 : ℝ))
      (E := (cell12893 ⟨54, by decide⟩).energy) (xi := (328958306198489 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12893 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12893]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12893])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12893) (a := (20555618731089 / 25000000000000 : ℝ)) (b := (159732554487 / 100000000000000 : ℝ)) (q := (557146267879 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12893])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12893])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12893]

theorem cert12893_55 : CellCertificate 12893 (440688123206329 / 5000000000000000 : ℝ) (162912629520097 / 100000000000000000 : ℝ) (328958306198489 / 10000000000000000 : ℝ)
    (cell12893 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · have h := gap_lower (n := 12893) (a := (20547213796847 / 25000000000000 : ℝ)) (b := (159732554487 / 100000000000000 : ℝ)) (q := (1114294530663 / 50000000000000 : ℝ))
      (E := (cell12893 ⟨55, by decide⟩).energy) (xi := (328958306198489 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12893 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12893]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12893])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12893) (a := (20547213796847 / 25000000000000 : ℝ)) (b := (159732554487 / 100000000000000 : ℝ)) (q := (1114294530663 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12893])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12893])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12893]

theorem cert12893_56 : CellCertificate 12893 (440688123206329 / 5000000000000000 : ℝ) (162912629520097 / 100000000000000000 : ℝ) (328958306198489 / 10000000000000000 : ℝ)
    (cell12893 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · have h := gap_lower (n := 12893) (a := (82155258583087 / 100000000000000 : ℝ)) (b := (159732554487 / 100000000000000 : ℝ)) (q := (1114296550781 / 50000000000000 : ℝ))
      (E := (cell12893 ⟨56, by decide⟩).energy) (xi := (328958306198489 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12893 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12893]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12893])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12893) (a := (82155258583087 / 100000000000000 : ℝ)) (b := (159732554487 / 100000000000000 : ℝ)) (q := (1114296550781 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12893])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12893])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12893]

theorem cert12893_57 : CellCertificate 12893 (440688123206329 / 5000000000000000 : ℝ) (162912629520097 / 100000000000000000 : ℝ) (328958306198489 / 10000000000000000 : ℝ)
    (cell12893 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · have h := gap_lower (n := 12893) (a := (82121685083913 / 100000000000000 : ℝ)) (b := (159732554487 / 100000000000000 : ℝ)) (q := (2228597069917 / 100000000000000 : ℝ))
      (E := (cell12893 ⟨57, by decide⟩).energy) (xi := (328958306198489 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12893 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12893]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12893])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12893) (a := (82121685083913 / 100000000000000 : ℝ)) (b := (159732554487 / 100000000000000 : ℝ)) (q := (2228597069917 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12893])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12893])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12893]

theorem cert12893_58 : CellCertificate 12893 (440688123206329 / 5000000000000000 : ℝ) (162912629520097 / 100000000000000000 : ℝ) (328958306198489 / 10000000000000000 : ℝ)
    (cell12893 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · have h := gap_lower (n := 12893) (a := (82088134662461 / 100000000000000 : ℝ)) (b := (159732554487 / 100000000000000 : ℝ)) (q := (1114300540221 / 50000000000000 : ℝ))
      (E := (cell12893 ⟨58, by decide⟩).energy) (xi := (328958306198489 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12893 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12893]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12893])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12893) (a := (82088134662461 / 100000000000000 : ℝ)) (b := (159732554487 / 100000000000000 : ℝ)) (q := (1114300540221 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12893])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12893])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12893]

theorem cert12893_59 : CellCertificate 12893 (440688123206329 / 5000000000000000 : ℝ) (162912629520097 / 100000000000000000 : ℝ) (328958306198489 / 10000000000000000 : ℝ)
    (cell12893 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · have h := gap_lower (n := 12893) (a := (41027303645731 / 50000000000000 : ℝ)) (b := (159732554487 / 100000000000000 : ℝ)) (q := (2228605128749 / 100000000000000 : ℝ))
      (E := (cell12893 ⟨59, by decide⟩).energy) (xi := (328958306198489 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12893 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12893]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12893])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12893) (a := (41027303645731 / 50000000000000 : ℝ)) (b := (159732554487 / 100000000000000 : ℝ)) (q := (2228605128749 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12893])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12893])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12893]

theorem cert12894_40 : CellCertificate 12894 (176269821728757 / 2000000000000000 : ℝ) (1628999906657463 / 1000000000000000000 : ℝ) (328932190480991 / 10000000000000000 : ℝ)
    (cell12894 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · have h := gap_lower (n := 12894) (a := (10336949177813 / 12500000000000 : ℝ)) (b := (159720019907 / 100000000000000 : ℝ)) (q := (278551507963 / 12500000000000 : ℝ))
      (E := (cell12894 ⟨40, by decide⟩).energy) (xi := (328932190480991 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12894 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12894]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12894])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12894) (a := (10336949177813 / 12500000000000 : ℝ)) (b := (159720019907 / 100000000000000 : ℝ)) (q := (278551507963 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12894])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12894])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12894]

theorem cert12894_41 : CellCertificate 12894 (176269821728757 / 2000000000000000 : ℝ) (1628999906657463 / 1000000000000000000 : ℝ) (328932190480991 / 10000000000000000 : ℝ)
    (cell12894 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · have h := gap_lower (n := 12894) (a := (5166352947081 / 6250000000000 : ℝ)) (b := (159720019907 / 100000000000000 : ℝ)) (q := (445683209631 / 20000000000000 : ℝ))
      (E := (cell12894 ⟨41, by decide⟩).energy) (xi := (328932190480991 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12894 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12894]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12894])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12894) (a := (5166352947081 / 6250000000000 : ℝ)) (b := (159720019907 / 100000000000000 : ℝ)) (q := (445683209631 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12894])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12894])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12894]

theorem cert12894_42 : CellCertificate 12894 (176269821728757 / 2000000000000000 : ℝ) (1628999906657463 / 1000000000000000000 : ℝ) (328932190480991 / 10000000000000000 : ℝ)
    (cell12894 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · have h := gap_lower (n := 12894) (a := (82627724416783 / 100000000000000 : ℝ)) (b := (159720019907 / 100000000000000 : ℝ)) (q := (69638126853 / 3125000000000 : ℝ))
      (E := (cell12894 ⟨42, by decide⟩).energy) (xi := (328932190480991 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12894 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12894]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12894])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12894) (a := (82627724416783 / 100000000000000 : ℝ)) (b := (159720019907 / 100000000000000 : ℝ)) (q := (69638126853 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12894])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12894])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12894]

theorem cert12894_43 : CellCertificate 12894 (176269821728757 / 2000000000000000 : ℝ) (1628999906657463 / 1000000000000000000 : ℝ) (328932190480991 / 10000000000000000 : ℝ)
    (cell12894 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · have h := gap_lower (n := 12894) (a := (4129691259171 / 5000000000000 : ℝ)) (b := (159720019907 / 100000000000000 : ℝ)) (q := (557106009303 / 25000000000000 : ℝ))
      (E := (cell12894 ⟨43, by decide⟩).energy) (xi := (328932190480991 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12894 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12894]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12894])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12894) (a := (4129691259171 / 5000000000000 : ℝ)) (b := (159720019907 / 100000000000000 : ℝ)) (q := (557106009303 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12894])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12894])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12894]

theorem cert12894_44 : CellCertificate 12894 (176269821728757 / 2000000000000000 : ℝ) (1628999906657463 / 1000000000000000000 : ℝ) (328932190480991 / 10000000000000000 : ℝ)
    (cell12894 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · have h := gap_lower (n := 12894) (a := (82559949423809 / 100000000000000 : ℝ)) (b := (159720019907 / 100000000000000 : ℝ)) (q := (1114214019697 / 50000000000000 : ℝ))
      (E := (cell12894 ⟨44, by decide⟩).energy) (xi := (328932190480991 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12894 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12894]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12894])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12894) (a := (82559949423809 / 100000000000000 : ℝ)) (b := (159720019907 / 100000000000000 : ℝ)) (q := (1114214019697 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12894])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12894])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12894]

theorem cert12894_45 : CellCertificate 12894 (176269821728757 / 2000000000000000 : ℝ) (1628999906657463 / 1000000000000000000 : ℝ) (328932190480991 / 10000000000000000 : ℝ)
    (cell12894 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · have h := gap_lower (n := 12894) (a := (825260971087 / 1000000000000 : ℝ)) (b := (159720019907 / 100000000000000 : ℝ)) (q := (278554008041 / 12500000000000 : ℝ))
      (E := (cell12894 ⟨45, by decide⟩).energy) (xi := (328932190480991 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12894 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12894]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12894])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12894) (a := (825260971087 / 1000000000000 : ℝ)) (b := (159720019907 / 100000000000000 : ℝ)) (q := (278554008041 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12894])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12894])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12894]

theorem cert12894_46 : CellCertificate 12894 (176269821728757 / 2000000000000000 : ℝ) (1628999906657463 / 1000000000000000000 : ℝ) (328932190480991 / 10000000000000000 : ℝ)
    (cell12894 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · have h := gap_lower (n := 12894) (a := (82492268208991 / 100000000000000 : ℝ)) (b := (159720019907 / 100000000000000 : ℝ)) (q := (1114218055143 / 50000000000000 : ℝ))
      (E := (cell12894 ⟨46, by decide⟩).energy) (xi := (328932190480991 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12894 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12894]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12894])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12894) (a := (82492268208991 / 100000000000000 : ℝ)) (b := (159720019907 / 100000000000000 : ℝ)) (q := (1114218055143 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12894])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12894])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12894]

theorem cert12894_47 : CellCertificate 12894 (176269821728757 / 2000000000000000 : ℝ) (1628999906657463 / 1000000000000000000 : ℝ) (328932190480991 / 10000000000000000 : ℝ)
    (cell12894 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · have h := gap_lower (n := 12894) (a := (82458462695727 / 100000000000000 : ℝ)) (b := (159720019907 / 100000000000000 : ℝ)) (q := (2228440116391 / 100000000000000 : ℝ))
      (E := (cell12894 ⟨47, by decide⟩).energy) (xi := (328932190480991 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12894 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12894]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12894])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12894) (a := (82458462695727 / 100000000000000 : ℝ)) (b := (159720019907 / 100000000000000 : ℝ)) (q := (2228440116391 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12894])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12894])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12894]

theorem cert12894_48 : CellCertificate 12894 (176269821728757 / 2000000000000000 : ℝ) (1628999906657463 / 1000000000000000000 : ℝ) (328932190480991 / 10000000000000000 : ℝ)
    (cell12894 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · have h := gap_lower (n := 12894) (a := (41212340270047 / 50000000000000 : ℝ)) (b := (159720019907 / 100000000000000 : ℝ)) (q := (1114222040209 / 50000000000000 : ℝ))
      (E := (cell12894 ⟨48, by decide⟩).energy) (xi := (328932190480991 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12894 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12894]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12894])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12894) (a := (41212340270047 / 50000000000000 : ℝ)) (b := (159720019907 / 100000000000000 : ℝ)) (q := (1114222040209 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12894])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12894])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12894]

theorem cert12894_49 : CellCertificate 12894 (176269821728757 / 2000000000000000 : ℝ) (1628999906657463 / 1000000000000000000 : ℝ) (328932190480991 / 10000000000000000 : ℝ)
    (cell12894 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · have h := gap_lower (n := 12894) (a := (20597730428357 / 25000000000000 : ℝ)) (b := (159720019907 / 100000000000000 : ℝ)) (q := (2228448117877 / 100000000000000 : ℝ))
      (E := (cell12894 ⟨49, by decide⟩).energy) (xi := (328932190480991 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12894 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12894]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12894])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12894) (a := (20597730428357 / 25000000000000 : ℝ)) (b := (159720019907 / 100000000000000 : ℝ)) (q := (2228448117877 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12894])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12894])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12894]

theorem cert12894_50 : CellCertificate 12894 (176269821728757 / 2000000000000000 : ℝ) (1628999906657463 / 1000000000000000000 : ℝ) (328932190480991 / 10000000000000000 : ℝ)
    (cell12894 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · have h := gap_lower (n := 12894) (a := (20589296546801 / 25000000000000 : ℝ)) (b := (159720019907 / 100000000000000 : ℝ)) (q := (69639128383 / 3125000000000 : ℝ))
      (E := (cell12894 ⟨50, by decide⟩).energy) (xi := (328932190480991 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12894 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12894]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12894])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12894) (a := (20589296546801 / 25000000000000 : ℝ)) (b := (159720019907 / 100000000000000 : ℝ)) (q := (69639128383 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12894])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12894])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12894]

theorem cert12894_51 : CellCertificate 12894 (176269821728757 / 2000000000000000 : ℝ) (1628999906657463 / 1000000000000000000 : ℝ) (328932190480991 / 10000000000000000 : ℝ)
    (cell12894 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · have h := gap_lower (n := 12894) (a := (82323473933043 / 100000000000000 : ℝ)) (b := (159720019907 / 100000000000000 : ℝ)) (q := (2228456107711 / 100000000000000 : ℝ))
      (E := (cell12894 ⟨51, by decide⟩).energy) (xi := (328932190480991 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12894 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12894]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12894])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12894) (a := (82323473933043 / 100000000000000 : ℝ)) (b := (159720019907 / 100000000000000 : ℝ)) (q := (2228456107711 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12894])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12894])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12894]

theorem cert12894_52 : CellCertificate 12894 (176269821728757 / 2000000000000000 : ℝ) (1628999906657463 / 1000000000000000000 : ℝ) (328932190480991 / 10000000000000000 : ℝ)
    (cell12894 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · have h := gap_lower (n := 12894) (a := (16457956984541 / 20000000000000 : ℝ)) (b := (159720019907 / 100000000000000 : ℝ)) (q := (2228460113239 / 100000000000000 : ℝ))
      (E := (cell12894 ⟨52, by decide⟩).energy) (xi := (328932190480991 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12894 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12894]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12894])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12894) (a := (16457956984541 / 20000000000000 : ℝ)) (b := (159720019907 / 100000000000000 : ℝ)) (q := (2228460113239 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12894])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12894])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12894]

theorem cert12894_53 : CellCertificate 12894 (176269821728757 / 2000000000000000 : ℝ) (1628999906657463 / 1000000000000000000 : ℝ) (328932190480991 / 10000000000000000 : ℝ)
    (cell12894 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · have h := gap_lower (n := 12894) (a := (20564029782023 / 25000000000000 : ℝ)) (b := (159720019907 / 100000000000000 : ℝ)) (q := (278558015203 / 12500000000000 : ℝ))
      (E := (cell12894 ⟨53, by decide⟩).energy) (xi := (328932190480991 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12894 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12894]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12894])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12894) (a := (20564029782023 / 25000000000000 : ℝ)) (b := (159720019907 / 100000000000000 : ℝ)) (q := (278558015203 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12894])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12894])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12894]

theorem cert12894_54 : CellCertificate 12894 (176269821728757 / 2000000000000000 : ℝ) (1628999906657463 / 1000000000000000000 : ℝ) (328932190480991 / 10000000000000000 : ℝ)
    (cell12894 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · have h := gap_lower (n := 12894) (a := (2569452391289 / 3125000000000 : ℝ)) (b := (159720019907 / 100000000000000 : ℝ)) (q := (13927925809 / 625000000000 : ℝ))
      (E := (cell12894 ⟨54, by decide⟩).energy) (xi := (328932190480991 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12894 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12894]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12894])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12894) (a := (2569452391289 / 3125000000000 : ℝ)) (b := (159720019907 / 100000000000000 : ℝ)) (q := (13927925809 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12894])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12894])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12894]

theorem cert12894_55 : CellCertificate 12894 (176269821728757 / 2000000000000000 : ℝ) (1628999906657463 / 1000000000000000000 : ℝ) (328932190480991 / 10000000000000000 : ℝ)
    (cell12894 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · have h := gap_lower (n := 12894) (a := (41094428537177 / 50000000000000 : ℝ)) (b := (159720019907 / 100000000000000 : ℝ)) (q := (445694426611 / 20000000000000 : ℝ))
      (E := (cell12894 ⟨55, by decide⟩).energy) (xi := (328932190480991 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12894 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12894]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12894])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12894) (a := (41094428537177 / 50000000000000 : ℝ)) (b := (159720019907 / 100000000000000 : ℝ)) (q := (445694426611 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12894])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12894])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12894]

theorem cert12894_56 : CellCertificate 12894 (176269821728757 / 2000000000000000 : ℝ) (1628999906657463 / 1000000000000000000 : ℝ) (328932190480991 / 10000000000000000 : ℝ)
    (cell12894 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · have h := gap_lower (n := 12894) (a := (20538815189933 / 25000000000000 : ℝ)) (b := (159720019907 / 100000000000000 : ℝ)) (q := (2228476187769 / 100000000000000 : ℝ))
      (E := (cell12894 ⟨56, by decide⟩).energy) (xi := (328932190480991 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12894 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12894]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12894])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12894) (a := (20538815189933 / 25000000000000 : ℝ)) (b := (159720019907 / 100000000000000 : ℝ)) (q := (2228476187769 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12894])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12894])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12894]

theorem cert12894_57 : CellCertificate 12894 (176269821728757 / 2000000000000000 : ℝ) (1628999906657463 / 1000000000000000000 : ℝ) (328932190480991 / 10000000000000000 : ℝ)
    (cell12894 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · have h := gap_lower (n := 12894) (a := (82121687549839 / 100000000000000 : ℝ)) (b := (159720019907 / 100000000000000 : ℝ)) (q := (89139206851 / 4000000000000 : ℝ))
      (E := (cell12894 ⟨57, by decide⟩).energy) (xi := (328932190480991 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12894 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12894]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12894])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12894) (a := (82121687549839 / 100000000000000 : ℝ)) (b := (159720019907 / 100000000000000 : ℝ)) (q := (89139206851 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12894])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12894])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12894]

theorem cert12894_58 : CellCertificate 12894 (176269821728757 / 2000000000000000 : ℝ) (1628999906657463 / 1000000000000000000 : ℝ) (328932190480991 / 10000000000000000 : ℝ)
    (cell12894 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · have h := gap_lower (n := 12894) (a := (10261017177159 / 12500000000000 : ℝ)) (b := (159720019907 / 100000000000000 : ℝ)) (q := (278560524703 / 12500000000000 : ℝ))
      (E := (cell12894 ⟨58, by decide⟩).energy) (xi := (328932190480991 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12894 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12894]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12894])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12894) (a := (10261017177159 / 12500000000000 : ℝ)) (b := (159720019907 / 100000000000000 : ℝ)) (q := (278560524703 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12894])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12894])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12894]

theorem cert12894_59 : CellCertificate 12894 (176269821728757 / 2000000000000000 : ℝ) (1628999906657463 / 1000000000000000000 : ℝ) (328932190480991 / 10000000000000000 : ℝ)
    (cell12894 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · have h := gap_lower (n := 12894) (a := (41027305167381 / 50000000000000 : ℝ)) (b := (159720019907 / 100000000000000 : ℝ)) (q := (139280512701 / 6250000000000 : ℝ))
      (E := (cell12894 ⟨59, by decide⟩).energy) (xi := (328932190480991 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12894 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12894]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12894])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12894) (a := (41027305167381 / 50000000000000 : ℝ)) (b := (159720019907 / 100000000000000 : ℝ)) (q := (139280512701 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12894])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12894])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12894]

theorem cert12895_40 : CellCertificate 12895 (881321974910231 / 10000000000000000 : ℝ) (814436768861511 / 500000000000000000 : ℝ) (82226519738111 / 2500000000000000 : ℝ)
    (cell12895 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · have h := gap_lower (n := 12895) (a := (20673897729261 / 25000000000000 : ℝ)) (b := (19963435913 / 12500000000000 : ℝ)) (q := (278536896599 / 12500000000000 : ℝ))
      (E := (cell12895 ⟨40, by decide⟩).energy) (xi := (82226519738111 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12895 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12895]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12895])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12895) (a := (20673897729261 / 25000000000000 : ℝ)) (b := (19963435913 / 12500000000000 : ℝ)) (q := (278536896599 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12895])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12895])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12895]

theorem cert12895_41 : CellCertificate 12895 (881321974910231 / 10000000000000000 : ℝ) (814436768861511 / 500000000000000000 : ℝ) (82226519738111 / 2500000000000000 : ℝ)
    (cell12895 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · have h := gap_lower (n := 12895) (a := (41330822471757 / 50000000000000 : ℝ)) (b := (19963435913 / 12500000000000 : ℝ)) (q := (139268697603 / 6250000000000 : ℝ))
      (E := (cell12895 ⟨41, by decide⟩).energy) (xi := (82226519738111 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12895 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12895]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12895])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12895) (a := (41330822471757 / 50000000000000 : ℝ)) (b := (19963435913 / 12500000000000 : ℝ)) (q := (139268697603 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12895])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12895])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12895]

theorem cert12895_42 : CellCertificate 12895 (881321974910231 / 10000000000000000 : ℝ) (814436768861511 / 500000000000000000 : ℝ) (82226519738111 / 2500000000000000 : ℝ)
    (cell12895 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · have h := gap_lower (n := 12895) (a := (645529082049 / 781250000000 : ℝ)) (b := (19963435913 / 12500000000000 : ℝ)) (q := (2228303177879 / 100000000000000 : ℝ))
      (E := (cell12895 ⟨42, by decide⟩).energy) (xi := (82226519738111 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12895 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12895]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12895])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12895) (a := (645529082049 / 781250000000 : ℝ)) (b := (19963435913 / 12500000000000 : ℝ)) (q := (2228303177879 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12895])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12895])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12895]

theorem cert12895_43 : CellCertificate 12895 (881321974910231 / 10000000000000000 : ℝ) (814436768861511 / 500000000000000000 : ℝ) (82226519738111 / 2500000000000000 : ℝ)
    (cell12895 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · have h := gap_lower (n := 12895) (a := (20648455890943 / 25000000000000 : ℝ)) (b := (19963435913 / 12500000000000 : ℝ)) (q := (69634598799 / 3125000000000 : ℝ))
      (E := (cell12895 ⟨43, by decide⟩).energy) (xi := (82226519738111 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12895 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12895]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12895])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12895) (a := (20648455890943 / 25000000000000 : ℝ)) (b := (19963435913 / 12500000000000 : ℝ)) (q := (69634598799 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12895])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12895])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12895]

theorem cert12895_44 : CellCertificate 12895 (881321974910231 / 10000000000000000 : ℝ) (814436768861511 / 500000000000000000 : ℝ) (82226519738111 / 2500000000000000 : ℝ)
    (cell12895 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · have h := gap_lower (n := 12895) (a := (82559948098619 / 100000000000000 : ℝ)) (b := (19963435913 / 12500000000000 : ℝ)) (q := (2228311170203 / 100000000000000 : ℝ))
      (E := (cell12895 ⟨44, by decide⟩).energy) (xi := (82226519738111 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12895 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12895]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12895])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12895) (a := (82559948098619 / 100000000000000 : ℝ)) (b := (19963435913 / 12500000000000 : ℝ)) (q := (2228311170203 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12895])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12895])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12895]

theorem cert12895_45 : CellCertificate 12895 (881321974910231 / 10000000000000000 : ℝ) (814436768861511 / 500000000000000000 : ℝ) (82226519738111 / 2500000000000000 : ℝ)
    (cell12895 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · have h := gap_lower (n := 12895) (a := (82526096077563 / 100000000000000 : ℝ)) (b := (19963435913 / 12500000000000 : ℝ)) (q := (2228315202273 / 100000000000000 : ℝ))
      (E := (cell12895 ⟨45, by decide⟩).energy) (xi := (82226519738111 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12895 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12895]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12895])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12895) (a := (82526096077563 / 100000000000000 : ℝ)) (b := (19963435913 / 12500000000000 : ℝ)) (q := (2228315202273 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12895])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12895])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12895]

theorem cert12895_46 : CellCertificate 12895 (881321974910231 / 10000000000000000 : ℝ) (814436768861511 / 500000000000000000 : ℝ) (82226519738111 / 2500000000000000 : ℝ)
    (cell12895 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · have h := gap_lower (n := 12895) (a := (82492267471503 / 100000000000000 : ℝ)) (b := (19963435913 / 12500000000000 : ℝ)) (q := (2228319197139 / 100000000000000 : ℝ))
      (E := (cell12895 ⟨46, by decide⟩).energy) (xi := (82226519738111 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12895 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12895]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12895])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12895) (a := (82492267471503 / 100000000000000 : ℝ)) (b := (19963435913 / 12500000000000 : ℝ)) (q := (2228319197139 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12895])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12895])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12895]

theorem cert12895_47 : CellCertificate 12895 (881321974910231 / 10000000000000000 : ℝ) (814436768861511 / 500000000000000000 : ℝ) (82226519738111 / 2500000000000000 : ℝ)
    (cell12895 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · have h := gap_lower (n := 12895) (a := (82458462251483 / 100000000000000 : ℝ)) (b := (19963435913 / 12500000000000 : ℝ)) (q := (2228323211717 / 100000000000000 : ℝ))
      (E := (cell12895 ⟨47, by decide⟩).energy) (xi := (82226519738111 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12895 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12895]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12895])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12895) (a := (82458462251483 / 100000000000000 : ℝ)) (b := (19963435913 / 12500000000000 : ℝ)) (q := (2228323211717 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12895])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12895])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12895]

theorem cert12895_48 : CellCertificate 12895 (881321974910231 / 10000000000000000 : ℝ) (814436768861511 / 500000000000000000 : ℝ) (82226519738111 / 2500000000000000 : ℝ)
    (cell12895 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · have h := gap_lower (n := 12895) (a := (20606170097173 / 25000000000000 : ℝ)) (b := (19963435913 / 12500000000000 : ℝ)) (q := (2228327243849 / 100000000000000 : ℝ))
      (E := (cell12895 ⟨48, by decide⟩).energy) (xi := (82226519738111 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12895 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12895]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12895])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12895) (a := (20606170097173 / 25000000000000 : ℝ)) (b := (19963435913 / 12500000000000 : ℝ)) (q := (2228327243849 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12895])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12895])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12895]

theorem cert12895_49 : CellCertificate 12895 (881321974910231 / 10000000000000000 : ℝ) (814436768861511 / 500000000000000000 : ℝ) (82226519738111 / 2500000000000000 : ℝ)
    (cell12895 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · have h := gap_lower (n := 12895) (a := (41195460927233 / 50000000000000 : ℝ)) (b := (19963435913 / 12500000000000 : ℝ)) (q := (2228331232183 / 100000000000000 : ℝ))
      (E := (cell12895 ⟨49, by decide⟩).energy) (xi := (82226519738111 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12895 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12895]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12895])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12895) (a := (41195460927233 / 50000000000000 : ℝ)) (b := (19963435913 / 12500000000000 : ℝ)) (q := (2228331232183 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12895])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12895])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12895]

theorem cert12895_50 : CellCertificate 12895 (881321974910231 / 10000000000000000 : ℝ) (814436768861511 / 500000000000000000 : ℝ) (82226519738111 / 2500000000000000 : ℝ)
    (cell12895 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · have h := gap_lower (n := 12895) (a := (2058929665507 / 2500000000000 : ℝ)) (b := (19963435913 / 12500000000000 : ℝ)) (q := (2228335233069 / 100000000000000 : ℝ))
      (E := (cell12895 ⟨50, by decide⟩).energy) (xi := (82226519738111 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12895 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12895]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12895])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12895) (a := (2058929665507 / 2500000000000 : ℝ)) (b := (19963435913 / 12500000000000 : ℝ)) (q := (2228335233069 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12895])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12895])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12895]

theorem cert12895_51 : CellCertificate 12895 (881321974910231 / 10000000000000000 : ℝ) (814436768861511 / 500000000000000000 : ℝ) (82226519738111 / 2500000000000000 : ℝ)
    (cell12895 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · have h := gap_lower (n := 12895) (a := (16464694931551 / 20000000000000 : ℝ)) (b := (19963435913 / 12500000000000 : ℝ)) (q := (222833924371 / 10000000000000 : ℝ))
      (E := (cell12895 ⟨51, by decide⟩).energy) (xi := (82226519738111 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12895 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12895]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12895])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12895) (a := (16464694931551 / 20000000000000 : ℝ)) (b := (19963435913 / 12500000000000 : ℝ)) (q := (222833924371 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12895])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12895])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12895]

theorem cert12895_52 : CellCertificate 12895 (881321974910231 / 10000000000000000 : ℝ) (814436768861511 / 500000000000000000 : ℝ) (82226519738111 / 2500000000000000 : ℝ)
    (cell12895 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · have h := gap_lower (n := 12895) (a := (41144892969327 / 50000000000000 : ℝ)) (b := (19963435913 / 12500000000000 : ℝ)) (q := (2228343261099 / 100000000000000 : ℝ))
      (E := (cell12895 ⟨52, by decide⟩).energy) (xi := (82226519738111 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12895 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12895]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12895])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12895) (a := (41144892969327 / 50000000000000 : ℝ)) (b := (19963435913 / 12500000000000 : ℝ)) (q := (2228343261099 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12895])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12895])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12895]

theorem cert12895_53 : CellCertificate 12895 (881321974910231 / 10000000000000000 : ℝ) (814436768861511 / 500000000000000000 : ℝ) (82226519738111 / 2500000000000000 : ℝ)
    (cell12895 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · have h := gap_lower (n := 12895) (a := (82256120434879 / 100000000000000 : ℝ)) (b := (19963435913 / 12500000000000 : ℝ)) (q := (2228347282021 / 100000000000000 : ℝ))
      (E := (cell12895 ⟨53, by decide⟩).energy) (xi := (82226519738111 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12895 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12895]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12895])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12895) (a := (82256120434879 / 100000000000000 : ℝ)) (b := (19963435913 / 12500000000000 : ℝ)) (q := (2228347282021 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12895])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12895])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12895]

theorem cert12895_54 : CellCertificate 12895 (881321974910231 / 10000000000000000 : ℝ) (814436768861511 / 500000000000000000 : ℝ) (82226519738111 / 2500000000000000 : ℝ)
    (cell12895 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · have h := gap_lower (n := 12895) (a := (41111239059237 / 50000000000000 : ℝ)) (b := (19963435913 / 12500000000000 : ℝ)) (q := (1114175621977 / 50000000000000 : ℝ))
      (E := (cell12895 ⟨54, by decide⟩).energy) (xi := (82226519738111 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12895 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12895]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12895])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12895) (a := (41111239059237 / 50000000000000 : ℝ)) (b := (19963435913 / 12500000000000 : ℝ)) (q := (1114175621977 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12895])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12895])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12895]

theorem cert12895_55 : CellCertificate 12895 (881321974910231 / 10000000000000000 : ℝ) (814436768861511 / 500000000000000000 : ℝ) (82226519738111 / 2500000000000000 : ℝ)
    (cell12895 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · have h := gap_lower (n := 12895) (a := (82188858961621 / 100000000000000 : ℝ)) (b := (19963435913 / 12500000000000 : ℝ)) (q := (278544407679 / 12500000000000 : ℝ))
      (E := (cell12895 ⟨55, by decide⟩).energy) (xi := (82226519738111 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12895 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12895]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12895])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12895) (a := (82188858961621 / 100000000000000 : ℝ)) (b := (19963435913 / 12500000000000 : ℝ)) (q := (278544407679 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12895])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12895])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12895]

theorem cert12895_56 : CellCertificate 12895 (881321974910231 / 10000000000000000 : ℝ) (814436768861511 / 500000000000000000 : ℝ) (82226519738111 / 2500000000000000 : ℝ)
    (cell12895 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · have h := gap_lower (n := 12895) (a := (41077631468321 / 50000000000000 : ℝ)) (b := (19963435913 / 12500000000000 : ℝ)) (q := (1114179635771 / 50000000000000 : ℝ))
      (E := (cell12895 ⟨56, by decide⟩).energy) (xi := (82226519738111 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12895 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12895]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12895])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12895) (a := (41077631468321 / 50000000000000 : ℝ)) (b := (19963435913 / 12500000000000 : ℝ)) (q := (1114179635771 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12895])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12895])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12895]

theorem cert12895_57 : CellCertificate 12895 (881321974910231 / 10000000000000000 : ℝ) (814436768861511 / 500000000000000000 : ℝ) (82226519738111 / 2500000000000000 : ℝ)
    (cell12895 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · have h := gap_lower (n := 12895) (a := (20530422503999 / 25000000000000 : ℝ)) (b := (19963435913 / 12500000000000 : ℝ)) (q := (2228363329399 / 100000000000000 : ℝ))
      (E := (cell12895 ⟨57, by decide⟩).energy) (xi := (82226519738111 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12895 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12895]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12895])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12895) (a := (20530422503999 / 25000000000000 : ℝ)) (b := (19963435913 / 12500000000000 : ℝ)) (q := (2228363329399 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12895])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12895])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12895]

theorem cert12895_58 : CellCertificate 12895 (881321974910231 / 10000000000000000 : ℝ) (814436768861511 / 500000000000000000 : ℝ) (82226519738111 / 2500000000000000 : ℝ)
    (cell12895 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · have h := gap_lower (n := 12895) (a := (82088140172279 / 100000000000000 : ℝ)) (b := (19963435913 / 12500000000000 : ℝ)) (q := (2228367312443 / 100000000000000 : ℝ))
      (E := (cell12895 ⟨58, by decide⟩).energy) (xi := (82226519738111 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12895 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12895]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12895])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12895) (a := (82088140172279 / 100000000000000 : ℝ)) (b := (19963435913 / 12500000000000 : ℝ)) (q := (2228367312443 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12895])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12895])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12895]

theorem cert12895_59 : CellCertificate 12895 (881321974910231 / 10000000000000000 : ℝ) (814436768861511 / 500000000000000000 : ℝ) (82226519738111 / 2500000000000000 : ℝ)
    (cell12895 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · have h := gap_lower (n := 12895) (a := (5128413336139 / 6250000000000 : ℝ)) (b := (19963435913 / 12500000000000 : ℝ)) (q := (2228371334567 / 100000000000000 : ℝ))
      (E := (cell12895 ⟨59, by decide⟩).energy) (xi := (82226519738111 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12895 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12895]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12895])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12895) (a := (5128413336139 / 6250000000000 : ℝ)) (b := (19963435913 / 12500000000000 : ℝ)) (q := (2228371334567 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12895])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12895])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12895]

theorem cert12896_40 : CellCertificate 12896 (881294845211053 / 10000000000000000 : ℝ) (325749437678617 / 200000000000000000 : ℝ) (32887997161177 / 1000000000000000 : ℝ)
    (cell12896 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · have h := gap_lower (n := 12896) (a := (10336948551551 / 12500000000000 : ℝ)) (b := (79847478339 / 50000000000000 : ℝ)) (q := (1114089139437 / 50000000000000 : ℝ))
      (E := (cell12896 ⟨40, by decide⟩).energy) (xi := (32887997161177 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12896 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12896]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12896])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12896) (a := (10336948551551 / 12500000000000 : ℝ)) (b := (79847478339 / 50000000000000 : ℝ)) (q := (1114089139437 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12896])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12896])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12896]

theorem cert12896_41 : CellCertificate 12896 (881294845211053 / 10000000000000000 : ℝ) (325749437678617 / 200000000000000000 : ℝ) (32887997161177 / 1000000000000000 : ℝ)
    (cell12896 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · have h := gap_lower (n := 12896) (a := (2066541068363 / 2500000000000 : ℝ)) (b := (79847478339 / 50000000000000 : ℝ)) (q := (2228182330963 / 100000000000000 : ℝ))
      (E := (cell12896 ⟨41, by decide⟩).energy) (xi := (32887997161177 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12896 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12896]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12896])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12896) (a := (2066541068363 / 2500000000000 : ℝ)) (b := (79847478339 / 50000000000000 : ℝ)) (q := (2228182330963 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12896])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12896])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12896]

theorem cert12896_42 : CellCertificate 12896 (881294845211053 / 10000000000000000 : ℝ) (325749437678617 / 200000000000000000 : ℝ) (32887997161177 / 1000000000000000 : ℝ)
    (cell12896 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · have h := gap_lower (n := 12896) (a := (82627720588513 / 100000000000000 : ℝ)) (b := (79847478339 / 50000000000000 : ℝ)) (q := (222818629353 / 10000000000000 : ℝ))
      (E := (cell12896 ⟨42, by decide⟩).energy) (xi := (32887997161177 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12896 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12896]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12896])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12896) (a := (82627720588513 / 100000000000000 : ℝ)) (b := (79847478339 / 50000000000000 : ℝ)) (q := (222818629353 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12896])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12896])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12896]

theorem cert12896_43 : CellCertificate 12896 (881294845211053 / 10000000000000000 : ℝ) (325749437678617 / 200000000000000000 : ℝ) (32887997161177 / 1000000000000000 : ℝ)
    (cell12896 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · have h := gap_lower (n := 12896) (a := (41296910972421 / 50000000000000 : ℝ)) (b := (79847478339 / 50000000000000 : ℝ)) (q := (1114095170931 / 50000000000000 : ℝ))
      (E := (cell12896 ⟨43, by decide⟩).energy) (xi := (32887997161177 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12896 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12896]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12896])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12896) (a := (41296910972421 / 50000000000000 : ℝ)) (b := (79847478339 / 50000000000000 : ℝ)) (q := (1114095170931 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12896])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12896])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12896]

theorem cert12896_44 : CellCertificate 12896 (881294845211053 / 10000000000000000 : ℝ) (325749437678617 / 200000000000000000 : ℝ) (32887997161177 / 1000000000000000 : ℝ)
    (cell12896 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · have h := gap_lower (n := 12896) (a := (82559946774111 / 100000000000000 : ℝ)) (b := (79847478339 / 50000000000000 : ℝ)) (q := (557048589253 / 25000000000000 : ℝ))
      (E := (cell12896 ⟨44, by decide⟩).energy) (xi := (32887997161177 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12896 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12896]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12896])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12896) (a := (82559946774111 / 100000000000000 : ℝ)) (b := (79847478339 / 50000000000000 : ℝ)) (q := (557048589253 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12896])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12896])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12896]

theorem cert12896_45 : CellCertificate 12896 (881294845211053 / 10000000000000000 : ℝ) (325749437678617 / 200000000000000000 : ℝ) (32887997161177 / 1000000000000000 : ℝ)
    (cell12896 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · have h := gap_lower (n := 12896) (a := (82526095047073 / 100000000000000 : ℝ)) (b := (79847478339 / 50000000000000 : ℝ)) (q := (2228198337393 / 100000000000000 : ℝ))
      (E := (cell12896 ⟨45, by decide⟩).energy) (xi := (32887997161177 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12896 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12896]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12896])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12896) (a := (82526095047073 / 100000000000000 : ℝ)) (b := (79847478339 / 50000000000000 : ℝ)) (q := (2228198337393 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12896])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12896])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12896]

theorem cert12896_46 : CellCertificate 12896 (881294845211053 / 10000000000000000 : ℝ) (325749437678617 / 200000000000000000 : ℝ) (32887997161177 / 1000000000000000 : ℝ)
    (cell12896 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · have h := gap_lower (n := 12896) (a := (82492266734627 / 100000000000000 : ℝ)) (b := (79847478339 / 50000000000000 : ℝ)) (q := (222820234011 / 10000000000000 : ℝ))
      (E := (cell12896 ⟨46, by decide⟩).energy) (xi := (32887997161177 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12896 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12896]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12896])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12896) (a := (82492266734627 / 100000000000000 : ℝ)) (b := (79847478339 / 50000000000000 : ℝ)) (q := (222820234011 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12896])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12896])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12896]

theorem cert12896_47 : CellCertificate 12896 (881294845211053 / 10000000000000000 : ℝ) (325749437678617 / 200000000000000000 : ℝ) (32887997161177 / 1000000000000000 : ℝ)
    (cell12896 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · have h := gap_lower (n := 12896) (a := (10307307725977 / 12500000000000 : ℝ)) (b := (79847478339 / 50000000000000 : ℝ)) (q := (111410318161 / 5000000000000 : ℝ))
      (E := (cell12896 ⟨47, by decide⟩).energy) (xi := (32887997161177 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12896 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12896]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12896])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12896) (a := (10307307725977 / 12500000000000 : ℝ)) (b := (79847478339 / 50000000000000 : ℝ)) (q := (111410318161 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12896])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12896])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12896]

theorem cert12896_48 : CellCertificate 12896 (881294845211053 / 10000000000000000 : ℝ) (325749437678617 / 200000000000000000 : ℝ) (32887997161177 / 1000000000000000 : ℝ)
    (cell12896 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · have h := gap_lower (n := 12896) (a := (82424680237833 / 100000000000000 : ℝ)) (b := (79847478339 / 50000000000000 : ℝ)) (q := (2228210345607 / 100000000000000 : ℝ))
      (E := (cell12896 ⟨48, by decide⟩).energy) (xi := (32887997161177 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12896 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12896]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12896])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12896) (a := (82424680237833 / 100000000000000 : ℝ)) (b := (79847478339 / 50000000000000 : ℝ)) (q := (2228210345607 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12896])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12896])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12896]

theorem cert12896_49 : CellCertificate 12896 (881294845211053 / 10000000000000000 : ℝ) (325749437678617 / 200000000000000000 : ℝ) (32887997161177 / 1000000000000000 : ℝ)
    (cell12896 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · have h := gap_lower (n := 12896) (a := (82390921996011 / 100000000000000 : ℝ)) (b := (79847478339 / 50000000000000 : ℝ)) (q := (445642880557 / 20000000000000 : ℝ))
      (E := (cell12896 ⟨49, by decide⟩).energy) (xi := (32887997161177 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12896 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12896]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12896])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12896) (a := (82390921996011 / 100000000000000 : ℝ)) (b := (79847478339 / 50000000000000 : ℝ)) (q := (445642880557 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12896])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12896])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12896]

theorem cert12896_50 : CellCertificate 12896 (881294845211053 / 10000000000000000 : ℝ) (325749437678617 / 200000000000000000 : ℝ) (32887997161177 / 1000000000000000 : ℝ)
    (cell12896 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · have h := gap_lower (n := 12896) (a := (20589296763457 / 25000000000000 : ℝ)) (b := (79847478339 / 50000000000000 : ℝ)) (q := (1114109207119 / 50000000000000 : ℝ))
      (E := (cell12896 ⟨50, by decide⟩).energy) (xi := (32887997161177 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12896 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12896]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12896])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12896) (a := (20589296763457 / 25000000000000 : ℝ)) (b := (79847478339 / 50000000000000 : ℝ)) (q := (1114109207119 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12896])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12896])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12896]

theorem cert12896_51 : CellCertificate 12896 (881294845211053 / 10000000000000000 : ℝ) (325749437678617 / 200000000000000000 : ℝ) (32887997161177 / 1000000000000000 : ℝ)
    (cell12896 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · have h := gap_lower (n := 12896) (a := (41161737691453 / 50000000000000 : ℝ)) (b := (79847478339 / 50000000000000 : ℝ)) (q := (1114111188549 / 50000000000000 : ℝ))
      (E := (cell12896 ⟨51, by decide⟩).energy) (xi := (32887997161177 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12896 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12896]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12896])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12896) (a := (41161737691453 / 50000000000000 : ℝ)) (b := (79847478339 / 50000000000000 : ℝ)) (q := (1114111188549 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12896])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12896])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12896]

theorem cert12896_52 : CellCertificate 12896 (881294845211053 / 10000000000000000 : ℝ) (325749437678617 / 200000000000000000 : ℝ) (32887997161177 / 1000000000000000 : ℝ)
    (cell12896 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · have h := gap_lower (n := 12896) (a := (321444480293 / 390625000000 : ℝ)) (b := (79847478339 / 50000000000000 : ℝ)) (q := (2228226406383 / 100000000000000 : ℝ))
      (E := (cell12896 ⟨52, by decide⟩).energy) (xi := (32887997161177 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12896 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12896]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12896])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12896) (a := (321444480293 / 390625000000 : ℝ)) (b := (79847478339 / 50000000000000 : ℝ)) (q := (2228226406383 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12896])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12896])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12896]

theorem cert12896_53 : CellCertificate 12896 (881294845211053 / 10000000000000000 : ℝ) (325749437678617 / 200000000000000000 : ℝ) (32887997161177 / 1000000000000000 : ℝ)
    (cell12896 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · have h := gap_lower (n := 12896) (a := (20564030435509 / 25000000000000 : ℝ)) (b := (79847478339 / 50000000000000 : ℝ)) (q := (557057609969 / 25000000000000 : ℝ))
      (E := (cell12896 ⟨53, by decide⟩).energy) (xi := (32887997161177 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12896 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12896]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12896])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12896) (a := (20564030435509 / 25000000000000 : ℝ)) (b := (79847478339 / 50000000000000 : ℝ)) (q := (557057609969 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12896])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12896])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12896]

theorem cert12896_54 : CellCertificate 12896 (881294845211053 / 10000000000000000 : ℝ) (325749437678617 / 200000000000000000 : ℝ) (32887997161177 / 1000000000000000 : ℝ)
    (cell12896 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · have h := gap_lower (n := 12896) (a := (16444495943207 / 20000000000000 : ℝ)) (b := (79847478339 / 50000000000000 : ℝ)) (q := (1114117207529 / 50000000000000 : ℝ))
      (E := (cell12896 ⟨54, by decide⟩).energy) (xi := (32887997161177 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12896 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12896]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12896])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12896) (a := (16444495943207 / 20000000000000 : ℝ)) (b := (79847478339 / 50000000000000 : ℝ)) (q := (1114117207529 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12896])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12896])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12896]

theorem cert12896_55 : CellCertificate 12896 (881294845211053 / 10000000000000000 : ℝ) (325749437678617 / 200000000000000000 : ℝ) (32887997161177 / 1000000000000000 : ℝ)
    (cell12896 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · have h := gap_lower (n := 12896) (a := (20547215212297 / 25000000000000 : ℝ)) (b := (79847478339 / 50000000000000 : ℝ)) (q := (1114119223229 / 50000000000000 : ℝ))
      (E := (cell12896 ⟨55, by decide⟩).energy) (xi := (32887997161177 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12896 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12896]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12896])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12896) (a := (20547215212297 / 25000000000000 : ℝ)) (b := (79847478339 / 50000000000000 : ℝ)) (q := (1114119223229 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12896])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12896])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12896]

theorem cert12896_56 : CellCertificate 12896 (881294845211053 / 10000000000000000 : ℝ) (325749437678617 / 200000000000000000 : ℝ) (32887997161177 / 1000000000000000 : ℝ)
    (cell12896 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · have h := gap_lower (n := 12896) (a := (82155265113817 / 100000000000000 : ℝ)) (b := (79847478339 / 50000000000000 : ℝ)) (q := (1114121206011 / 50000000000000 : ℝ))
      (E := (cell12896 ⟨56, by decide⟩).energy) (xi := (32887997161177 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12896 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12896]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12896])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12896) (a := (82155265113817 / 100000000000000 : ℝ)) (b := (79847478339 / 50000000000000 : ℝ)) (q := (1114121206011 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12896])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12896])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12896]

theorem cert12896_57 : CellCertificate 12896 (881294845211053 / 10000000000000000 : ℝ) (325749437678617 / 200000000000000000 : ℝ) (32887997161177 / 1000000000000000 : ℝ)
    (cell12896 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · have h := gap_lower (n := 12896) (a := (82121692482383 / 100000000000000 : ℝ)) (b := (79847478339 / 50000000000000 : ℝ)) (q := (55706160649 / 2500000000000 : ℝ))
      (E := (cell12896 ⟨57, by decide⟩).energy) (xi := (32887997161177 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12896 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12896]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12896])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12896) (a := (82121692482383 / 100000000000000 : ℝ)) (b := (79847478339 / 50000000000000 : ℝ)) (q := (55706160649 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12896])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12896])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12896]

theorem cert12896_58 : CellCertificate 12896 (881294845211053 / 10000000000000000 : ℝ) (325749437678617 / 200000000000000000 : ℝ) (32887997161177 / 1000000000000000 : ℝ)
    (cell12896 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · have h := gap_lower (n := 12896) (a := (82088142927483 / 100000000000000 : ℝ)) (b := (79847478339 / 50000000000000 : ℝ)) (q := (1114125242043 / 50000000000000 : ℝ))
      (E := (cell12896 ⟨58, by decide⟩).energy) (xi := (32887997161177 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12896 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12896]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12896])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12896) (a := (82088142927483 / 100000000000000 : ℝ)) (b := (79847478339 / 50000000000000 : ℝ)) (q := (1114125242043 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12896])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12896])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12896]

theorem cert12896_59 : CellCertificate 12896 (881294845211053 / 10000000000000000 : ℝ) (325749437678617 / 200000000000000000 : ℝ) (32887997161177 / 1000000000000000 : ℝ)
    (cell12896 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · have h := gap_lower (n := 12896) (a := (82054616421849 / 100000000000000 : ℝ)) (b := (79847478339 / 50000000000000 : ℝ)) (q := (557063615897 / 25000000000000 : ℝ))
      (E := (cell12896 ⟨59, by decide⟩).energy) (xi := (32887997161177 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12896 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12896]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12896])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12896) (a := (82054616421849 / 100000000000000 : ℝ)) (b := (79847478339 / 50000000000000 : ℝ)) (q := (557063615897 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12896])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12896])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12896]

theorem cert12897_40 : CellCertificate 12897 (440633859772653 / 5000000000000000 : ℝ) (162862085866309 / 100000000000000000 : ℝ) (32885386845789 / 1000000000000000 : ℝ)
    (cell12897 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · have h := gap_lower (n := 12897) (a := (16539117181719 / 20000000000000 : ℝ)) (b := (159682428029 / 100000000000000 : ℝ)) (q := (557015374871 / 25000000000000 : ℝ))
      (E := (cell12897 ⟨40, by decide⟩).energy) (xi := (32885386845789 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12897 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12897]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12897])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12897) (a := (16539117181719 / 20000000000000 : ℝ)) (b := (159682428029 / 100000000000000 : ℝ)) (q := (557015374871 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12897])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12897])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12897]

theorem cert12897_41 : CellCertificate 12897 (440633859772653 / 5000000000000000 : ℝ) (162862085866309 / 100000000000000000 : ℝ) (32885386845789 / 1000000000000000 : ℝ)
    (cell12897 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · have h := gap_lower (n := 12897) (a := (41330820263157 / 50000000000000 : ℝ)) (b := (159682428029 / 100000000000000 : ℝ)) (q := (2228065497309 / 100000000000000 : ℝ))
      (E := (cell12897 ⟨41, by decide⟩).energy) (xi := (32885386845789 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12897 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12897]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12897])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12897) (a := (41330820263157 / 50000000000000 : ℝ)) (b := (159682428029 / 100000000000000 : ℝ)) (q := (2228065497309 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12897])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12897])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12897]

theorem cert12897_42 : CellCertificate 12897 (440633859772653 / 5000000000000000 : ℝ) (162862085866309 / 100000000000000000 : ℝ) (32885386845789 / 1000000000000000 : ℝ)
    (cell12897 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · have h := gap_lower (n := 12897) (a := (82627718675507 / 100000000000000 : ℝ)) (b := (159682428029 / 100000000000000 : ℝ)) (q := (2228069523873 / 100000000000000 : ℝ))
      (E := (cell12897 ⟨42, by decide⟩).energy) (xi := (32885386845789 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12897 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12897]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12897])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12897) (a := (82627718675507 / 100000000000000 : ℝ)) (b := (159682428029 / 100000000000000 : ℝ)) (q := (2228069523873 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12897])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12897])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12897]

theorem cert12897_43 : CellCertificate 12897 (440633859772653 / 5000000000000000 : ℝ) (162862085866309 / 100000000000000000 : ℝ) (32885386845789 / 1000000000000000 : ℝ)
    (cell12897 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · have h := gap_lower (n := 12897) (a := (8259382032663 / 10000000000000 : ℝ)) (b := (159682428029 / 100000000000000 : ℝ)) (q := (111403675963 / 5000000000000 : ℝ))
      (E := (cell12897 ⟨43, by decide⟩).energy) (xi := (32885386845789 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12897 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12897]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12897])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12897) (a := (8259382032663 / 10000000000000 : ℝ)) (b := (159682428029 / 100000000000000 : ℝ)) (q := (111403675963 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12897])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12897])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12897]

theorem cert12897_44 : CellCertificate 12897 (440633859772653 / 5000000000000000 : ℝ) (162862085866309 / 100000000000000000 : ℝ) (32885386845789 / 1000000000000000 : ℝ)
    (cell12897 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · have h := gap_lower (n := 12897) (a := (82559945450287 / 100000000000000 : ℝ)) (b := (159682428029 / 100000000000000 : ℝ)) (q := (2228077540959 / 100000000000000 : ℝ))
      (E := (cell12897 ⟨44, by decide⟩).energy) (xi := (32885386845789 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12897 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12897]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12897])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12897) (a := (82559945450287 / 100000000000000 : ℝ)) (b := (159682428029 / 100000000000000 : ℝ)) (q := (2228077540959 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12897])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12897])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12897]

theorem cert12897_45 : CellCertificate 12897 (440633859772653 / 5000000000000000 : ℝ) (162862085866309 / 100000000000000000 : ℝ) (32885386845789 / 1000000000000000 : ℝ)
    (cell12897 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · have h := gap_lower (n := 12897) (a := (82526094017231 / 100000000000000 : ℝ)) (b := (159682428029 / 100000000000000 : ℝ)) (q := (2228081528571 / 100000000000000 : ℝ))
      (E := (cell12897 ⟨45, by decide⟩).energy) (xi := (32885386845789 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12897 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12897]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12897])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12897) (a := (82526094017231 / 100000000000000 : ℝ)) (b := (159682428029 / 100000000000000 : ℝ)) (q := (2228081528571 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12897])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12897])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12897]

theorem cert12897_46 : CellCertificate 12897 (440633859772653 / 5000000000000000 : ℝ) (162862085866309 / 100000000000000000 : ℝ) (32885386845789 / 1000000000000000 : ℝ)
    (cell12897 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · have h := gap_lower (n := 12897) (a := (82492265998363 / 100000000000000 : ℝ)) (b := (159682428029 / 100000000000000 : ℝ)) (q := (2228085539199 / 100000000000000 : ℝ))
      (E := (cell12897 ⟨46, by decide⟩).energy) (xi := (32885386845789 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12897 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12897]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12897])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12897) (a := (82492265998363 / 100000000000000 : ℝ)) (b := (159682428029 / 100000000000000 : ℝ)) (q := (2228085539199 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12897])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12897])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12897]

theorem cert12897_47 : CellCertificate 12897 (440633859772653 / 5000000000000000 : ℝ) (162862085866309 / 100000000000000000 : ℝ) (32885386845789 / 1000000000000000 : ℝ)
    (cell12897 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · have h := gap_lower (n := 12897) (a := (10307307670591 / 12500000000000 : ℝ)) (b := (159682428029 / 100000000000000 : ℝ)) (q := (2228089511969 / 100000000000000 : ℝ))
      (E := (cell12897 ⟨47, by decide⟩).energy) (xi := (32885386845789 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12897 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12897]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12897])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12897) (a := (10307307670591 / 12500000000000 : ℝ)) (b := (159682428029 / 100000000000000 : ℝ)) (q := (2228089511969 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12897])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12897])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12897]

theorem cert12897_48 : CellCertificate 12897 (440633859772653 / 5000000000000000 : ℝ) (162862085866309 / 100000000000000000 : ℝ) (32885386845789 / 1000000000000000 : ℝ)
    (cell12897 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · have h := gap_lower (n := 12897) (a := (20606170021879 / 25000000000000 : ℝ)) (b := (159682428029 / 100000000000000 : ℝ)) (q := (2228093562557 / 100000000000000 : ℝ))
      (E := (cell12897 ⟨48, by decide⟩).energy) (xi := (32885386845789 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12897 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12897]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12897])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12897) (a := (20606170021879 / 25000000000000 : ℝ)) (b := (159682428029 / 100000000000000 : ℝ)) (q := (2228093562557 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12897])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12897])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12897]

theorem cert12897_49 : CellCertificate 12897 (440633859772653 / 5000000000000000 : ℝ) (162862085866309 / 100000000000000000 : ℝ) (32885386845789 / 1000000000000000 : ℝ)
    (cell12897 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · have h := gap_lower (n := 12897) (a := (5149432633629 / 6250000000000 : ℝ)) (b := (159682428029 / 100000000000000 : ℝ)) (q := (445619514141 / 20000000000000 : ℝ))
      (E := (cell12897 ⟨49, by decide⟩).energy) (xi := (32885386845789 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12897 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12897]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12897])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12897) (a := (5149432633629 / 6250000000000 : ℝ)) (b := (159682428029 / 100000000000000 : ℝ)) (q := (445619514141 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12897])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12897])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12897]

theorem cert12897_50 : CellCertificate 12897 (440633859772653 / 5000000000000000 : ℝ) (162862085866309 / 100000000000000000 : ℝ) (32885386845789 / 1000000000000000 : ℝ)
    (cell12897 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · have h := gap_lower (n := 12897) (a := (1647143749757 / 2000000000000 : ℝ)) (b := (159682428029 / 100000000000000 : ℝ)) (q := (2228101533759 / 100000000000000 : ℝ))
      (E := (cell12897 ⟨50, by decide⟩).energy) (xi := (32885386845789 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12897 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12897]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12897])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12897) (a := (1647143749757 / 2000000000000 : ℝ)) (b := (159682428029 / 100000000000000 : ℝ)) (q := (2228101533759 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12897])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12897])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12897]

theorem cert12897_51 : CellCertificate 12897 (440633859772653 / 5000000000000000 : ℝ) (162862085866309 / 100000000000000000 : ℝ) (32885386845789 / 1000000000000000 : ℝ)
    (cell12897 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · have h := gap_lower (n := 12897) (a := (5145217256781 / 6250000000000 : ℝ)) (b := (159682428029 / 100000000000000 : ℝ)) (q := (1114052783449 / 50000000000000 : ℝ))
      (E := (cell12897 ⟨51, by decide⟩).energy) (xi := (32885386845789 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12897 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12897]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12897])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12897) (a := (5145217256781 / 6250000000000 : ℝ)) (b := (159682428029 / 100000000000000 : ℝ)) (q := (1114052783449 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12897])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12897])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12897]

theorem cert12897_52 : CellCertificate 12897 (440633859772653 / 5000000000000000 : ℝ) (162862085866309 / 100000000000000000 : ℝ) (32885386845789 / 1000000000000000 : ℝ)
    (cell12897 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · have h := gap_lower (n := 12897) (a := (20572446992941 / 25000000000000 : ℝ)) (b := (159682428029 / 100000000000000 : ℝ)) (q := (111405480407 / 5000000000000 : ℝ))
      (E := (cell12897 ⟨52, by decide⟩).energy) (xi := (32885386845789 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12897 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12897]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12897])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12897) (a := (20572446992941 / 25000000000000 : ℝ)) (b := (159682428029 / 100000000000000 : ℝ)) (q := (111405480407 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12897])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12897])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12897]

theorem cert12897_53 : CellCertificate 12897 (440633859772653 / 5000000000000000 : ℝ) (162862085866309 / 100000000000000000 : ℝ) (32885386845789 / 1000000000000000 : ℝ)
    (cell12897 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · have h := gap_lower (n := 12897) (a := (82256123049561 / 100000000000000 : ℝ)) (b := (159682428029 / 100000000000000 : ℝ)) (q := (2228113595193 / 100000000000000 : ℝ))
      (E := (cell12897 ⟨53, by decide⟩).energy) (xi := (32885386845789 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12897 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12897]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12897])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12897) (a := (82256123049561 / 100000000000000 : ℝ)) (b := (159682428029 / 100000000000000 : ℝ)) (q := (2228113595193 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12897])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12897])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12897]

theorem cert12897_54 : CellCertificate 12897 (440633859772653 / 5000000000000000 : ℝ) (162862085866309 / 100000000000000000 : ℝ) (32885386845789 / 1000000000000000 : ℝ)
    (cell12897 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · have h := gap_lower (n := 12897) (a := (82222481313929 / 100000000000000 : ℝ)) (b := (159682428029 / 100000000000000 : ℝ)) (q := (1114058791829 / 50000000000000 : ℝ))
      (E := (cell12897 ⟨54, by decide⟩).energy) (xi := (32885386845789 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12897 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12897]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12897])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12897) (a := (82222481313929 / 100000000000000 : ℝ)) (b := (159682428029 / 100000000000000 : ℝ)) (q := (1114058791829 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12897])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12897])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12897]

theorem cert12897_55 : CellCertificate 12897 (440633859772653 / 5000000000000000 : ℝ) (162862085866309 / 100000000000000000 : ℝ) (32885386845789 / 1000000000000000 : ℝ)
    (cell12897 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · have h := gap_lower (n := 12897) (a := (41094431368527 / 50000000000000 : ℝ)) (b := (159682428029 / 100000000000000 : ℝ)) (q := (445624325803 / 20000000000000 : ℝ))
      (E := (cell12897 ⟨55, by decide⟩).energy) (xi := (32885386845789 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12897 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12897]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12897])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12897) (a := (41094431368527 / 50000000000000 : ℝ)) (b := (159682428029 / 100000000000000 : ℝ)) (q := (445624325803 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12897])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12897])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12897]

theorem cert12897_56 : CellCertificate 12897 (440633859772653 / 5000000000000000 : ℝ) (162862085866309 / 100000000000000000 : ℝ) (32885386845789 / 1000000000000000 : ℝ)
    (cell12897 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · have h := gap_lower (n := 12897) (a := (41077633645629 / 50000000000000 : ℝ)) (b := (159682428029 / 100000000000000 : ℝ)) (q := (222812560921 / 10000000000000 : ℝ))
      (E := (cell12897 ⟨56, by decide⟩).energy) (xi := (32885386845789 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12897 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12897]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12897])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12897) (a := (41077633645629 / 50000000000000 : ℝ)) (b := (159682428029 / 100000000000000 : ℝ)) (q := (222812560921 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12897])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12897])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12897]

theorem cert12897_57 : CellCertificate 12897 (440633859772653 / 5000000000000000 : ℝ) (162862085866309 / 100000000000000000 : ℝ) (32885386845789 / 1000000000000000 : ℝ)
    (cell12897 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · have h := gap_lower (n := 12897) (a := (41060847474501 / 50000000000000 : ℝ)) (b := (159682428029 / 100000000000000 : ℝ)) (q := (557032409613 / 25000000000000 : ℝ))
      (E := (cell12897 ⟨57, by decide⟩).energy) (xi := (32885386845789 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12897 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12897]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12897])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12897) (a := (41060847474501 / 50000000000000 : ℝ)) (b := (159682428029 / 100000000000000 : ℝ)) (q := (557032409613 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12897])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12897])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12897]

theorem cert12897_58 : CellCertificate 12897 (440633859772653 / 5000000000000000 : ℝ) (162862085866309 / 100000000000000000 : ℝ) (32885386845789 / 1000000000000000 : ℝ)
    (cell12897 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · have h := gap_lower (n := 12897) (a := (82088145682883 / 100000000000000 : ℝ)) (b := (159682428029 / 100000000000000 : ℝ)) (q := (2228133653367 / 100000000000000 : ℝ))
      (E := (cell12897 ⟨58, by decide⟩).energy) (xi := (32885386845789 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12897 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12897]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12897])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12897) (a := (82088145682883 / 100000000000000 : ℝ)) (b := (159682428029 / 100000000000000 : ℝ)) (q := (2228133653367 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12897])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12897])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12897]

theorem cert12897_59 : CellCertificate 12897 (440633859772653 / 5000000000000000 : ℝ) (162862085866309 / 100000000000000000 : ℝ) (32885386845789 / 1000000000000000 : ℝ)
    (cell12897 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · have h := gap_lower (n := 12897) (a := (16410923893127 / 20000000000000 : ℝ)) (b := (159682428029 / 100000000000000 : ℝ)) (q := (1114068824747 / 50000000000000 : ℝ))
      (E := (cell12897 ⟨59, by decide⟩).energy) (xi := (32885386845789 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12897 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12897]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12897])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12897) (a := (16410923893127 / 20000000000000 : ℝ)) (b := (159682428029 / 100000000000000 : ℝ)) (q := (1114068824747 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12897])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12897])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12897]

theorem cert12898_40 : CellCertificate 12898 (55077537369503 / 625000000000000 : ℝ) (1628494548528477 / 1000000000000000000 : ℝ) (13153110779589 / 400000000000000 : ℝ)
    (cell12898 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · have h := gap_lower (n := 12898) (a := (16539116681121 / 20000000000000 : ℝ)) (b := (39917475339 / 25000000000000 : ℝ)) (q := (556986164581 / 25000000000000 : ℝ))
      (E := (cell12898 ⟨40, by decide⟩).energy) (xi := (13153110779589 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12898 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12898]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12898])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12898) (a := (16539116681121 / 20000000000000 : ℝ)) (b := (39917475339 / 25000000000000 : ℝ)) (q := (556986164581 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12898])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12898])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12898]

theorem cert12898_41 : CellCertificate 12898 (55077537369503 / 625000000000000 : ℝ) (1628494548528477 / 1000000000000000000 : ℝ) (13153110779589 / 400000000000000 : ℝ)
    (cell12898 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · have h := gap_lower (n := 12898) (a := (82661638318897 / 100000000000000 : ℝ)) (b := (39917475339 / 25000000000000 : ℝ)) (q := (89117948779 / 4000000000000 : ℝ))
      (E := (cell12898 ⟨41, by decide⟩).energy) (xi := (13153110779589 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12898 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12898]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12898])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12898) (a := (82661638318897 / 100000000000000 : ℝ)) (b := (39917475339 / 25000000000000 : ℝ)) (q := (89117948779 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12898])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12898])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12898]

theorem cert12898_42 : CellCertificate 12898 (55077537369503 / 625000000000000 : ℝ) (1628494548528477 / 1000000000000000000 : ℝ) (13153110779589 / 400000000000000 : ℝ)
    (cell12898 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · have h := gap_lower (n := 12898) (a := (41313858381627 / 50000000000000 : ℝ)) (b := (39917475339 / 25000000000000 : ℝ)) (q := (2227952692473 / 100000000000000 : ℝ))
      (E := (cell12898 ⟨42, by decide⟩).energy) (xi := (13153110779589 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12898 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12898]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12898])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12898) (a := (41313858381627 / 50000000000000 : ℝ)) (b := (39917475339 / 25000000000000 : ℝ)) (q := (2227952692473 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12898])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12898])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12898]

theorem cert12898_43 : CellCertificate 12898 (55077537369503 / 625000000000000 : ℝ) (1628494548528477 / 1000000000000000000 : ℝ) (13153110779589 / 400000000000000 : ℝ)
    (cell12898 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · have h := gap_lower (n := 12898) (a := (16518763741827 / 20000000000000 : ℝ)) (b := (39917475339 / 25000000000000 : ℝ)) (q := (2227956693763 / 100000000000000 : ℝ))
      (E := (cell12898 ⟨43, by decide⟩).energy) (xi := (13153110779589 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12898 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12898]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12898])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12898) (a := (16518763741827 / 20000000000000 : ℝ)) (b := (39917475339 / 25000000000000 : ℝ)) (q := (2227956693763 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12898])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12898])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12898]

theorem cert12898_44 : CellCertificate 12898 (55077537369503 / 625000000000000 : ℝ) (1628494548528477 / 1000000000000000000 : ℝ) (13153110779589 / 400000000000000 : ℝ)
    (cell12898 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · have h := gap_lower (n := 12898) (a := (16511988825429 / 20000000000000 : ℝ)) (b := (39917475339 / 25000000000000 : ℝ)) (q := (2227960722047 / 100000000000000 : ℝ))
      (E := (cell12898 ⟨44, by decide⟩).energy) (xi := (13153110779589 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12898 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12898]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12898])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12898) (a := (16511988825429 / 20000000000000 : ℝ)) (b := (39917475339 / 25000000000000 : ℝ)) (q := (2227960722047 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12898])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12898])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12898]

theorem cert12898_45 : CellCertificate 12898 (55077537369503 / 625000000000000 : ℝ) (1628494548528477 / 1000000000000000000 : ℝ) (13153110779589 / 400000000000000 : ℝ)
    (cell12898 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · have h := gap_lower (n := 12898) (a := (82526092988037 / 100000000000000 : ℝ)) (b := (39917475339 / 25000000000000 : ℝ)) (q := (89118588677 / 4000000000000 : ℝ))
      (E := (cell12898 ⟨45, by decide⟩).energy) (xi := (13153110779589 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12898 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12898]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12898])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12898) (a := (82526092988037 / 100000000000000 : ℝ)) (b := (39917475339 / 25000000000000 : ℝ)) (q := (89118588677 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12898])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12898])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12898]

theorem cert12898_46 : CellCertificate 12898 (55077537369503 / 625000000000000 : ℝ) (1628494548528477 / 1000000000000000000 : ℝ) (13153110779589 / 400000000000000 : ℝ)
    (cell12898 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · have h := gap_lower (n := 12898) (a := (10311533157839 / 12500000000000 : ℝ)) (b := (39917475339 / 25000000000000 : ℝ)) (q := (4455937471 / 200000000000 : ℝ))
      (E := (cell12898 ⟨46, by decide⟩).energy) (xi := (13153110779589 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12898 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12898]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12898])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12898) (a := (10311533157839 / 12500000000000 : ℝ)) (b := (39917475339 / 25000000000000 : ℝ)) (q := (4455937471 / 200000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12898])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12898])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12898]

theorem cert12898_47 : CellCertificate 12898 (55077537369503 / 625000000000000 : ℝ) (1628494548528477 / 1000000000000000000 : ℝ) (13153110779589 / 400000000000000 : ℝ)
    (cell12898 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · have h := gap_lower (n := 12898) (a := (10307307615277 / 12500000000000 : ℝ)) (b := (39917475339 / 25000000000000 : ℝ)) (q := (2227972716897 / 100000000000000 : ℝ))
      (E := (cell12898 ⟨47, by decide⟩).energy) (xi := (13153110779589 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12898 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12898]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12898])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12898) (a := (10307307615277 / 12500000000000 : ℝ)) (b := (39917475339 / 25000000000000 : ℝ)) (q := (2227972716897 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12898])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12898])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12898]

theorem cert12898_48 : CellCertificate 12898 (55077537369503 / 625000000000000 : ℝ) (1628494548528477 / 1000000000000000000 : ℝ) (13153110779589 / 400000000000000 : ℝ)
    (cell12898 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · have h := gap_lower (n := 12898) (a := (41212339968871 / 50000000000000 : ℝ)) (b := (39917475339 / 25000000000000 : ℝ)) (q := (445595343567 / 20000000000000 : ℝ))
      (E := (cell12898 ⟨48, by decide⟩).energy) (xi := (13153110779589 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12898 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12898]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12898])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12898) (a := (41212339968871 / 50000000000000 : ℝ)) (b := (39917475339 / 25000000000000 : ℝ)) (q := (445595343567 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12898])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12898])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12898]

theorem cert12898_49 : CellCertificate 12898 (55077537369503 / 625000000000000 : ℝ) (1628494548528477 / 1000000000000000000 : ℝ) (13153110779589 / 400000000000000 : ℝ)
    (cell12898 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · have h := gap_lower (n := 12898) (a := (131825475649 / 160000000000 : ℝ)) (b := (39917475339 / 25000000000000 : ℝ)) (q := (278497591993 / 12500000000000 : ℝ))
      (E := (cell12898 ⟨49, by decide⟩).energy) (xi := (13153110779589 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12898 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12898]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12898])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12898) (a := (131825475649 / 160000000000 : ℝ)) (b := (39917475339 / 25000000000000 : ℝ)) (q := (278497591993 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12898])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12898])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12898]

theorem cert12898_50 : CellCertificate 12898 (55077537369503 / 625000000000000 : ℝ) (1628494548528477 / 1000000000000000000 : ℝ) (13153110779589 / 400000000000000 : ℝ)
    (cell12898 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · have h := gap_lower (n := 12898) (a := (10294648490293 / 12500000000000 : ℝ)) (b := (39917475339 / 25000000000000 : ℝ)) (q := (2227984768637 / 100000000000000 : ℝ))
      (E := (cell12898 ⟨50, by decide⟩).energy) (xi := (13153110779589 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12898 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12898]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12898])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12898) (a := (10294648490293 / 12500000000000 : ℝ)) (b := (39917475339 / 25000000000000 : ℝ)) (q := (2227984768637 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12898])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12898])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12898]

theorem cert12898_51 : CellCertificate 12898 (55077537369503 / 625000000000000 : ℝ) (1628494548528477 / 1000000000000000000 : ℝ) (13153110779589 / 400000000000000 : ℝ)
    (cell12898 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · have h := gap_lower (n := 12898) (a := (82323476834523 / 100000000000000 : ℝ)) (b := (39917475339 / 25000000000000 : ℝ)) (q := (222798875409 / 10000000000000 : ℝ))
      (E := (cell12898 ⟨51, by decide⟩).energy) (xi := (13153110779589 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12898 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12898]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12898])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12898) (a := (82323476834523 / 100000000000000 : ℝ)) (b := (39917475339 / 25000000000000 : ℝ)) (q := (222798875409 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12898])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12898])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12898]

theorem cert12898_52 : CellCertificate 12898 (55077537369503 / 625000000000000 : ℝ) (1628494548528477 / 1000000000000000000 : ℝ) (13153110779589 / 400000000000000 : ℝ)
    (cell12898 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · have h := gap_lower (n := 12898) (a := (3291591559557 / 4000000000000 : ℝ)) (b := (39917475339 / 25000000000000 : ℝ)) (q := (1113996403661 / 50000000000000 : ℝ))
      (E := (cell12898 ⟨52, by decide⟩).energy) (xi := (13153110779589 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12898 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12898]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12898])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12898) (a := (3291591559557 / 4000000000000 : ℝ)) (b := (39917475339 / 25000000000000 : ℝ)) (q := (1113996403661 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12898])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12898])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12898]

theorem cert12898_53 : CellCertificate 12898 (55077537369503 / 625000000000000 : ℝ) (1628494548528477 / 1000000000000000000 : ℝ) (13153110779589 / 400000000000000 : ℝ)
    (cell12898 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · have h := gap_lower (n := 12898) (a := (41128062178727 / 50000000000000 : ℝ)) (b := (39917475339 / 25000000000000 : ℝ)) (q := (556999201761 / 25000000000000 : ℝ))
      (E := (cell12898 ⟨53, by decide⟩).energy) (xi := (13153110779589 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12898 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12898]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12898])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12898) (a := (41128062178727 / 50000000000000 : ℝ)) (b := (39917475339 / 25000000000000 : ℝ)) (q := (556999201761 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12898])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12898])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12898]

theorem cert12898_54 : CellCertificate 12898 (55077537369503 / 625000000000000 : ℝ) (1628494548528477 / 1000000000000000000 : ℝ) (13153110779589 / 400000000000000 : ℝ)
    (cell12898 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · have h := gap_lower (n := 12898) (a := (41111241456079 / 50000000000000 : ℝ)) (b := (39917475339 / 25000000000000 : ℝ)) (q := (2228000808849 / 100000000000000 : ℝ))
      (E := (cell12898 ⟨54, by decide⟩).energy) (xi := (13153110779589 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12898 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12898]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12898])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12898) (a := (41111241456079 / 50000000000000 : ℝ)) (b := (39917475339 / 25000000000000 : ℝ)) (q := (2228000808849 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12898])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12898])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12898]

theorem cert12898_55 : CellCertificate 12898 (55077537369503 / 625000000000000 : ℝ) (1628494548528477 / 1000000000000000000 : ℝ) (13153110779589 / 400000000000000 : ℝ)
    (cell12898 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · have h := gap_lower (n := 12898) (a := (4109443231261 / 5000000000000 : ℝ)) (b := (39917475339 / 25000000000000 : ℝ)) (q := (445600961821 / 20000000000000 : ℝ))
      (E := (cell12898 ⟨55, by decide⟩).energy) (xi := (13153110779589 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12898 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12898]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12898])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12898) (a := (4109443231261 / 5000000000000 : ℝ)) (b := (39917475339 / 25000000000000 : ℝ)) (q := (445600961821 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12898])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12898])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12898]

theorem cert12898_56 : CellCertificate 12898 (55077537369503 / 625000000000000 : ℝ) (1628494548528477 / 1000000000000000000 : ℝ) (13153110779589 / 400000000000000 : ℝ)
    (cell12898 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · have h := gap_lower (n := 12898) (a := (20538817367241 / 25000000000000 : ℝ)) (b := (39917475339 / 25000000000000 : ℝ)) (q := (445601760793 / 20000000000000 : ℝ))
      (E := (cell12898 ⟨56, by decide⟩).energy) (xi := (13153110779589 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12898 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12898]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12898])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12898) (a := (20538817367241 / 25000000000000 : ℝ)) (b := (39917475339 / 25000000000000 : ℝ)) (q := (445601760793 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12898])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12898])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12898]

theorem cert12898_57 : CellCertificate 12898 (55077537369503 / 625000000000000 : ℝ) (1628494548528477 / 1000000000000000000 : ℝ) (13153110779589 / 400000000000000 : ℝ)
    (cell12898 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · have h := gap_lower (n := 12898) (a := (82121697415851 / 100000000000000 : ℝ)) (b := (39917475339 / 25000000000000 : ℝ)) (q := (2228012848547 / 100000000000000 : ℝ))
      (E := (cell12898 ⟨57, by decide⟩).energy) (xi := (13153110779589 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12898 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12898]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12898])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12898) (a := (82121697415851 / 100000000000000 : ℝ)) (b := (39917475339 / 25000000000000 : ℝ)) (q := (2228012848547 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12898])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12898])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12898]

theorem cert12898_58 : CellCertificate 12898 (55077537369503 / 625000000000000 : ℝ) (1628494548528477 / 1000000000000000000 : ℝ) (13153110779589 / 400000000000000 : ℝ)
    (cell12898 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · have h := gap_lower (n := 12898) (a := (82088148438479 / 100000000000000 : ℝ)) (b := (39917475339 / 25000000000000 : ℝ)) (q := (1114008410143 / 50000000000000 : ℝ))
      (E := (cell12898 ⟨58, by decide⟩).energy) (xi := (13153110779589 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12898 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12898]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12898])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12898) (a := (82088148438479 / 100000000000000 : ℝ)) (b := (39917475339 / 25000000000000 : ℝ)) (q := (1114008410143 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12898])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12898])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12898]

theorem cert12898_59 : CellCertificate 12898 (55077537369503 / 625000000000000 : ℝ) (1628494548528477 / 1000000000000000000 : ℝ) (13153110779589 / 400000000000000 : ℝ)
    (cell12898 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · have h := gap_lower (n := 12898) (a := (82054622509583 / 100000000000000 : ℝ)) (b := (39917475339 / 25000000000000 : ℝ)) (q := (2228020833073 / 100000000000000 : ℝ))
      (E := (cell12898 ⟨59, by decide⟩).energy) (xi := (13153110779589 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12898 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12898]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12898])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12898) (a := (82054622509583 / 100000000000000 : ℝ)) (b := (39917475339 / 25000000000000 : ℝ)) (q := (2228020833073 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12898])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12898])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12898]

theorem cert12899_40 : CellCertificate 12899 (13768960629849 / 156250000000000 : ℝ) (1628368257984687 / 1000000000000000000 : ℝ) (164400837353099 / 5000000000000000 : ℝ)
    (cell12899 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · have h := gap_lower (n := 12899) (a := (82695580903439 / 100000000000000 : ℝ)) (b := (79828688329 / 50000000000000 : ℝ)) (q := (2227827931693 / 100000000000000 : ℝ))
      (E := (cell12899 ⟨40, by decide⟩).energy) (xi := (164400837353099 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12899 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12899]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12899])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12899) (a := (82695580903439 / 100000000000000 : ℝ)) (b := (79828688329 / 50000000000000 : ℝ)) (q := (2227827931693 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12899])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12899])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12899]

theorem cert12899_41 : CellCertificate 12899 (13768960629849 / 156250000000000 : ℝ) (1628368257984687 / 1000000000000000000 : ℝ) (164400837353099 / 5000000000000000 : ℝ)
    (cell12899 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · have h := gap_lower (n := 12899) (a := (82661636112267 / 100000000000000 : ℝ)) (b := (79828688329 / 50000000000000 : ℝ)) (q := (2227831938677 / 100000000000000 : ℝ))
      (E := (cell12899 ⟨41, by decide⟩).energy) (xi := (164400837353099 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12899 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12899]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12899])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12899) (a := (82661636112267 / 100000000000000 : ℝ)) (b := (79828688329 / 50000000000000 : ℝ)) (q := (2227831938677 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12899])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12899])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12899]

theorem cert12899_42 : CellCertificate 12899 (13768960629849 / 156250000000000 : ℝ) (1628368257984687 / 1000000000000000000 : ℝ) (164400837353099 / 5000000000000000 : ℝ)
    (cell12899 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · have h := gap_lower (n := 12899) (a := (41313857425877 / 50000000000000 : ℝ)) (b := (79828688329 / 50000000000000 : ℝ)) (q := (1113917958477 / 50000000000000 : ℝ))
      (E := (cell12899 ⟨42, by decide⟩).energy) (xi := (164400837353099 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12899 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12899]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12899])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12899) (a := (41313857425877 / 50000000000000 : ℝ)) (b := (79828688329 / 50000000000000 : ℝ)) (q := (1113917958477 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12899])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12899])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12899]

theorem cert12899_43 : CellCertificate 12899 (13768960629849 / 156250000000000 : ℝ) (1628368257984687 / 1000000000000000000 : ℝ) (164400837353099 / 5000000000000000 : ℝ)
    (cell12899 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · have h := gap_lower (n := 12899) (a := (41296908546179 / 50000000000000 : ℝ)) (b := (79828688329 / 50000000000000 : ℝ)) (q := (139239995263 / 6250000000000 : ℝ))
      (E := (cell12899 ⟨43, by decide⟩).energy) (xi := (164400837353099 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12899 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12899]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12899])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12899) (a := (41296908546179 / 50000000000000 : ℝ)) (b := (79828688329 / 50000000000000 : ℝ)) (q := (139239995263 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12899])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12899])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12899]

theorem cert12899_44 : CellCertificate 12899 (13768960629849 / 156250000000000 : ℝ) (1628368257984687 / 1000000000000000000 : ℝ) (164400837353099 / 5000000000000000 : ℝ)
    (cell12899 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · have h := gap_lower (n := 12899) (a := (16511988560937 / 20000000000000 : ℝ)) (b := (79828688329 / 50000000000000 : ℝ)) (q := (2227843959137 / 100000000000000 : ℝ))
      (E := (cell12899 ⟨44, by decide⟩).energy) (xi := (164400837353099 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12899 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12899]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12899])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12899) (a := (16511988560937 / 20000000000000 : ℝ)) (b := (79828688329 / 50000000000000 : ℝ)) (q := (2227843959137 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12899])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12899])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12899]

theorem cert12899_45 : CellCertificate 12899 (13768960629849 / 156250000000000 : ℝ) (1628368257984687 / 1000000000000000000 : ℝ) (164400837353099 / 5000000000000000 : ℝ)
    (cell12899 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · have h := gap_lower (n := 12899) (a := (8252609195949 / 10000000000000 : ℝ)) (b := (79828688329 / 50000000000000 : ℝ)) (q := (111392398067 / 5000000000000 : ℝ))
      (E := (cell12899 ⟨45, by decide⟩).energy) (xi := (164400837353099 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12899 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12899]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12899])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12899) (a := (8252609195949 / 10000000000000 : ℝ)) (b := (79828688329 / 50000000000000 : ℝ)) (q := (111392398067 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12899])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12899])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12899]

theorem cert12899_46 : CellCertificate 12899 (13768960629849 / 156250000000000 : ℝ) (1628368257984687 / 1000000000000000000 : ℝ) (164400837353099 / 5000000000000000 : ℝ)
    (cell12899 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · have h := gap_lower (n := 12899) (a := (82492264527673 / 100000000000000 : ℝ)) (b := (79828688329 / 50000000000000 : ℝ)) (q := (445570385803 / 20000000000000 : ℝ))
      (E := (cell12899 ⟨46, by decide⟩).energy) (xi := (164400837353099 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12899 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12899]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12899])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12899) (a := (82492264527673 / 100000000000000 : ℝ)) (b := (79828688329 / 50000000000000 : ℝ)) (q := (445570385803 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12899])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12899])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12899]

theorem cert12899_47 : CellCertificate 12899 (13768960629849 / 156250000000000 : ℝ) (1628368257984687 / 1000000000000000000 : ℝ) (164400837353099 / 5000000000000000 : ℝ)
    (cell12899 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · have h := gap_lower (n := 12899) (a := (41229230240141 / 50000000000000 : ℝ)) (b := (79828688329 / 50000000000000 : ℝ)) (q := (2227855978003 / 100000000000000 : ℝ))
      (E := (cell12899 ⟨47, by decide⟩).energy) (xi := (164400837353099 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12899 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12899]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12899])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12899) (a := (41229230240141 / 50000000000000 : ℝ)) (b := (79828688329 / 50000000000000 : ℝ)) (q := (2227855978003 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12899])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12899])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12899]

theorem cert12899_48 : CellCertificate 12899 (13768960629849 / 156250000000000 : ℝ) (1628368257984687 / 1000000000000000000 : ℝ) (164400837353099 / 5000000000000000 : ℝ)
    (cell12899 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · have h := gap_lower (n := 12899) (a := (8242467978851 / 10000000000000 : ℝ)) (b := (79828688329 / 50000000000000 : ℝ)) (q := (2227859988307 / 100000000000000 : ℝ))
      (E := (cell12899 ⟨48, by decide⟩).energy) (xi := (164400837353099 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12899 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12899]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12899])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12899) (a := (8242467978851 / 10000000000000 : ℝ)) (b := (79828688329 / 50000000000000 : ℝ)) (q := (2227859988307 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12899])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12899])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12899]

theorem cert12899_49 : CellCertificate 12899 (13768960629849 / 156250000000000 : ℝ) (1628368257984687 / 1000000000000000000 : ℝ) (164400837353099 / 5000000000000000 : ℝ)
    (cell12899 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · have h := gap_lower (n := 12899) (a := (82390922423693 / 100000000000000 : ℝ)) (b := (79828688329 / 50000000000000 : ℝ)) (q := (2227863957481 / 100000000000000 : ℝ))
      (E := (cell12899 ⟨49, by decide⟩).energy) (xi := (164400837353099 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12899 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12899]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12899])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12899) (a := (82390922423693 / 100000000000000 : ℝ)) (b := (79828688329 / 50000000000000 : ℝ)) (q := (2227863957481 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12899])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12899])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12899]

theorem cert12899_50 : CellCertificate 12899 (13768960629849 / 156250000000000 : ℝ) (1628368257984687 / 1000000000000000000 : ℝ) (164400837353099 / 5000000000000000 : ℝ)
    (cell12899 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · have h := gap_lower (n := 12899) (a := (82357188357311 / 100000000000000 : ℝ)) (b := (79828688329 / 50000000000000 : ℝ)) (q := (2227868000871 / 100000000000000 : ℝ))
      (E := (cell12899 ⟨50, by decide⟩).energy) (xi := (164400837353099 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12899 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12899]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12899])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12899) (a := (82357188357311 / 100000000000000 : ℝ)) (b := (79828688329 / 50000000000000 : ℝ)) (q := (2227868000871 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12899])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12899])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12899]

theorem cert12899_51 : CellCertificate 12899 (13768960629849 / 156250000000000 : ℝ) (1628368257984687 / 1000000000000000000 : ℝ) (164400837353099 / 5000000000000000 : ℝ)
    (cell12899 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · have h := gap_lower (n := 12899) (a := (20580869390247 / 25000000000000 : ℝ)) (b := (79828688329 / 50000000000000 : ℝ)) (q := (1113935998849 / 50000000000000 : ℝ))
      (E := (cell12899 ⟨51, by decide⟩).energy) (xi := (164400837353099 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12899 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12899]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12899])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12899) (a := (20580869390247 / 25000000000000 : ℝ)) (b := (79828688329 / 50000000000000 : ℝ)) (q := (1113935998849 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12899])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12899])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12899]

theorem cert12899_52 : CellCertificate 12899 (13768960629849 / 156250000000000 : ℝ) (1628368257984687 / 1000000000000000000 : ℝ) (164400837353099 / 5000000000000000 : ℝ)
    (cell12899 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · have h := gap_lower (n := 12899) (a := (10286223750811 / 12500000000000 : ℝ)) (b := (79828688329 / 50000000000000 : ℝ)) (q := (2227876003933 / 100000000000000 : ℝ))
      (E := (cell12899 ⟨52, by decide⟩).energy) (xi := (164400837353099 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12899 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12899]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12899])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12899) (a := (10286223750811 / 12500000000000 : ℝ)) (b := (79828688329 / 50000000000000 : ℝ)) (q := (2227876003933 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12899])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12899])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12899]

theorem cert12899_53 : CellCertificate 12899 (13768960629849 / 156250000000000 : ℝ) (1628368257984687 / 1000000000000000000 : ℝ) (164400837353099 / 5000000000000000 : ℝ)
    (cell12899 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · have h := gap_lower (n := 12899) (a := (82256125665717 / 100000000000000 : ℝ)) (b := (79828688329 / 50000000000000 : ℝ)) (q := (556970004089 / 25000000000000 : ℝ))
      (E := (cell12899 ⟨53, by decide⟩).energy) (xi := (164400837353099 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12899 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12899]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12899])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12899) (a := (82256125665717 / 100000000000000 : ℝ)) (b := (79828688329 / 50000000000000 : ℝ)) (q := (556970004089 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12899])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12899])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12899]

theorem cert12899_54 : CellCertificate 12899 (13768960629849 / 156250000000000 : ℝ) (1628368257984687 / 1000000000000000000 : ℝ) (164400837353099 / 5000000000000000 : ℝ)
    (cell12899 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · have h := gap_lower (n := 12899) (a := (82222484510721 / 100000000000000 : ℝ)) (b := (79828688329 / 50000000000000 : ℝ)) (q := (2227884031539 / 100000000000000 : ℝ))
      (E := (cell12899 ⟨54, by decide⟩).energy) (xi := (164400837353099 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12899 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12899]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12899])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12899) (a := (82222484510721 / 100000000000000 : ℝ)) (b := (79828688329 / 50000000000000 : ℝ)) (q := (2227884031539 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12899])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12899])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12899]

theorem cert12899_55 : CellCertificate 12899 (13768960629849 / 156250000000000 : ℝ) (1628368257984687 / 1000000000000000000 : ℝ) (164400837353099 / 5000000000000000 : ℝ)
    (cell12899 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · have h := gap_lower (n := 12899) (a := (16437773302737 / 20000000000000 : ℝ)) (b := (79828688329 / 50000000000000 : ℝ)) (q := (1113944022923 / 50000000000000 : ℝ))
      (E := (cell12899 ⟨55, by decide⟩).energy) (xi := (164400837353099 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12899 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12899]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12899])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12899) (a := (16437773302737 / 20000000000000 : ℝ)) (b := (79828688329 / 50000000000000 : ℝ)) (q := (1113944022923 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12899])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12899])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12899]

theorem cert12899_56 : CellCertificate 12899 (13768960629849 / 156250000000000 : ℝ) (1628368257984687 / 1000000000000000000 : ℝ) (164400837353099 / 5000000000000000 : ℝ)
    (cell12899 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · have h := gap_lower (n := 12899) (a := (41077635823467 / 50000000000000 : ℝ)) (b := (79828688329 / 50000000000000 : ℝ)) (q := (278486506929 / 12500000000000 : ℝ))
      (E := (cell12899 ⟨56, by decide⟩).energy) (xi := (164400837353099 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12899 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12899]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12899])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12899) (a := (41077635823467 / 50000000000000 : ℝ)) (b := (79828688329 / 50000000000000 : ℝ)) (q := (278486506929 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12899])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12899])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12899]

theorem cert12899_57 : CellCertificate 12899 (13768960629849 / 156250000000000 : ℝ) (1628368257984687 / 1000000000000000000 : ℝ) (164400837353099 / 5000000000000000 : ℝ)
    (cell12899 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · have h := gap_lower (n := 12899) (a := (8212169988293 / 10000000000000 : ℝ)) (b := (79828688329 / 50000000000000 : ℝ)) (q := (2227896056247 / 100000000000000 : ℝ))
      (E := (cell12899 ⟨57, by decide⟩).energy) (xi := (164400837353099 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12899 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12899]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12899])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12899) (a := (8212169988293 / 10000000000000 : ℝ)) (b := (79828688329 / 50000000000000 : ℝ)) (q := (2227896056247 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12899])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12899])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12899]

theorem cert12899_58 : CellCertificate 12899 (13768960629849 / 156250000000000 : ℝ) (1628368257984687 / 1000000000000000000 : ℝ) (164400837353099 / 5000000000000000 : ℝ)
    (cell12899 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · have h := gap_lower (n := 12899) (a := (82088151194271 / 100000000000000 : ℝ)) (b := (79828688329 / 50000000000000 : ℝ)) (q := (2227900044033 / 100000000000000 : ℝ))
      (E := (cell12899 ⟨58, by decide⟩).energy) (xi := (164400837353099 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12899 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12899]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12899])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12899) (a := (82088151194271 / 100000000000000 : ℝ)) (b := (79828688329 / 50000000000000 : ℝ)) (q := (2227900044033 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12899])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12899])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12899]

theorem cert12899_59 : CellCertificate 12899 (13768960629849 / 156250000000000 : ℝ) (1628368257984687 / 1000000000000000000 : ℝ) (164400837353099 / 5000000000000000 : ℝ)
    (cell12899 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · have h := gap_lower (n := 12899) (a := (82054625553693 / 100000000000000 : ℝ)) (b := (79828688329 / 50000000000000 : ℝ)) (q := (2227904073539 / 100000000000000 : ℝ))
      (E := (cell12899 ⟨59, by decide⟩).energy) (xi := (164400837353099 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12899 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12899]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12899])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12899) (a := (82054625553693 / 100000000000000 : ℝ)) (b := (79828688329 / 50000000000000 : ℝ)) (q := (2227904073539 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12899])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12899])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12899]

end BstLean.Part268
