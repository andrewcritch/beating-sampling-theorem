import BstLean.Part263Shard1Checks1

/-! Twenty scalar cells per dimension in a 25-dimension shard. -/
namespace BstLean.Part263
open Real

theorem cert12250_40 : CellCertificate 12250 (35988224234511 / 400000000000000 : ℝ) (1714667950701239 / 1000000000000000000 : ℝ) (346669699379957 / 10000000000000000 : ℝ)
    (cell12250 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · have h := gap_lower (n := 12250) (a := (20674347371291 / 25000000000000 : ℝ)) (b := (16822475233 / 10000000000000 : ℝ)) (q := (288940997251 / 12500000000000 : ℝ))
      (E := (cell12250 ⟨40, by decide⟩).energy) (xi := (346669699379957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12250 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12250]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12250])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12250) (a := (20674347371291 / 25000000000000 : ℝ)) (b := (16822475233 / 10000000000000 : ℝ)) (q := (288940997251 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12250])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12250])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12250]

theorem cert12250_41 : CellCertificate 12250 (35988224234511 / 400000000000000 : ℝ) (1714667950701239 / 1000000000000000000 : ℝ) (346669699379957 / 10000000000000000 : ℝ)
    (cell12250 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · have h := gap_lower (n := 12250) (a := (41331622572047 / 50000000000000 : ℝ)) (b := (16822475233 / 10000000000000 : ℝ)) (q := (46230639303 / 2000000000000 : ℝ))
      (E := (cell12250 ⟨41, by decide⟩).energy) (xi := (346669699379957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12250 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12250]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12250])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12250) (a := (41331622572047 / 50000000000000 : ℝ)) (b := (16822475233 / 10000000000000 : ℝ)) (q := (46230639303 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12250])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12250])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12250]

theorem cert12250_42 : CellCertificate 12250 (35988224234511 / 400000000000000 : ℝ) (1714667950701239 / 1000000000000000000 : ℝ) (346669699379957 / 10000000000000000 : ℝ)
    (cell12250 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · have h := gap_lower (n := 12250) (a := (41314562304667 / 50000000000000 : ℝ)) (b := (16822475233 / 10000000000000 : ℝ)) (q := (2311535991159 / 100000000000000 : ℝ))
      (E := (cell12250 ⟨42, by decide⟩).energy) (xi := (346669699379957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12250 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12250]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12250])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12250) (a := (41314562304667 / 50000000000000 : ℝ)) (b := (16822475233 / 10000000000000 : ℝ)) (q := (2311535991159 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12250])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12250])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12250]

theorem cert12250_43 : CellCertificate 12250 (35988224234511 / 400000000000000 : ℝ) (1714667950701239 / 1000000000000000000 : ℝ) (346669699379957 / 10000000000000000 : ℝ)
    (cell12250 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · have h := gap_lower (n := 12250) (a := (82595027850841 / 100000000000000 : ℝ)) (b := (16822475233 / 10000000000000 : ℝ)) (q := (46230798769 / 2000000000000 : ℝ))
      (E := (cell12250 ⟨43, by decide⟩).energy) (xi := (346669699379957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12250 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12250]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12250])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12250) (a := (82595027850841 / 100000000000000 : ℝ)) (b := (16822475233 / 10000000000000 : ℝ)) (q := (46230798769 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12250])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12250])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12250]

theorem cert12250_44 : CellCertificate 12250 (35988224234511 / 400000000000000 : ℝ) (1714667950701239 / 1000000000000000000 : ℝ) (346669699379957 / 10000000000000000 : ℝ)
    (cell12250 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · have h := gap_lower (n := 12250) (a := (82560954838721 / 100000000000000 : ℝ)) (b := (16822475233 / 10000000000000 : ℝ)) (q := (462308784843 / 20000000000000 : ℝ))
      (E := (cell12250 ⟨44, by decide⟩).energy) (xi := (346669699379957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12250 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12250]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12250])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12250) (a := (82560954838721 / 100000000000000 : ℝ)) (b := (16822475233 / 10000000000000 : ℝ)) (q := (462308784843 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12250])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12250])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12250]

theorem cert12250_45 : CellCertificate 12250 (35988224234511 / 400000000000000 : ℝ) (1714667950701239 / 1000000000000000000 : ℝ) (346669699379957 / 10000000000000000 : ℝ)
    (cell12250 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · have h := gap_lower (n := 12250) (a := (16505381108647 / 20000000000000 : ℝ)) (b := (16822475233 / 10000000000000 : ℝ)) (q := (231154794797 / 10000000000000 : ℝ))
      (E := (cell12250 ⟨45, by decide⟩).energy) (xi := (346669699379957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12250 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12250]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12250])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12250) (a := (16505381108647 / 20000000000000 : ℝ)) (b := (16822475233 / 10000000000000 : ℝ)) (q := (231154794797 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12250])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12250])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12250]

theorem cert12250_46 : CellCertificate 12250 (35988224234511 / 400000000000000 : ℝ) (1714667950701239 / 1000000000000000000 : ℝ) (346669699379957 / 10000000000000000 : ℝ)
    (cell12250 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · have h := gap_lower (n := 12250) (a := (10311609991849 / 12500000000000 : ℝ)) (b := (16822475233 / 10000000000000 : ℝ)) (q := (92462078007 / 4000000000000 : ℝ))
      (E := (cell12250 ⟨46, by decide⟩).energy) (xi := (346669699379957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12250 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12250]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12250])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12250) (a := (10311609991849 / 12500000000000 : ℝ)) (b := (16822475233 / 10000000000000 : ℝ)) (q := (92462078007 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12250])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12250])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12250]

theorem cert12250_47 : CellCertificate 12250 (35988224234511 / 400000000000000 : ℝ) (1714667950701239 / 1000000000000000000 : ℝ) (346669699379957 / 10000000000000000 : ℝ)
    (cell12250 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · have h := gap_lower (n := 12250) (a := (82458877983951 / 100000000000000 : ℝ)) (b := (16822475233 / 10000000000000 : ℝ)) (q := (2311555929841 / 100000000000000 : ℝ))
      (E := (cell12250 ⟨47, by decide⟩).energy) (xi := (346669699379957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12250 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12250]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12250])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12250) (a := (82458877983951 / 100000000000000 : ℝ)) (b := (16822475233 / 10000000000000 : ℝ)) (q := (2311555929841 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12250])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12250])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12250]

theorem cert12250_48 : CellCertificate 12250 (35988224234511 / 400000000000000 : ℝ) (1714667950701239 / 1000000000000000000 : ℝ) (346669699379957 / 10000000000000000 : ℝ)
    (cell12250 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · have h := gap_lower (n := 12250) (a := (41212449830709 / 50000000000000 : ℝ)) (b := (16822475233 / 10000000000000 : ℝ)) (q := (1155779972327 / 50000000000000 : ℝ))
      (E := (cell12250 ⟨48, by decide⟩).energy) (xi := (346669699379957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12250 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12250]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12250])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12250) (a := (41212449830709 / 50000000000000 : ℝ)) (b := (16822475233 / 10000000000000 : ℝ)) (q := (1155779972327 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12250])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12250])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12250]

theorem cert12250_49 : CellCertificate 12250 (35988224234511 / 400000000000000 : ℝ) (1714667950701239 / 1000000000000000000 : ℝ) (346669699379957 / 10000000000000000 : ℝ)
    (cell12250 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · have h := gap_lower (n := 12250) (a := (1647818898761 / 2000000000000 : ℝ)) (b := (16822475233 / 10000000000000 : ℝ)) (q := (46231278687 / 2000000000000 : ℝ))
      (E := (cell12250 ⟨49, by decide⟩).energy) (xi := (346669699379957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12250 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12250]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12250])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12250) (a := (1647818898761 / 2000000000000 : ℝ)) (b := (16822475233 / 10000000000000 : ℝ)) (q := (46231278687 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12250])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12250])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12250]

theorem cert12250_50 : CellCertificate 12250 (35988224234511 / 400000000000000 : ℝ) (1714667950701239 / 1000000000000000000 : ℝ) (346669699379957 / 10000000000000000 : ℝ)
    (cell12250 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · have h := gap_lower (n := 12250) (a := (5147313361553 / 6250000000000 : ℝ)) (b := (16822475233 / 10000000000000 : ℝ)) (q := (231156795623 / 10000000000000 : ℝ))
      (E := (cell12250 ⟨50, by decide⟩).energy) (xi := (346669699379957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12250 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12250]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12250])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12250) (a := (5147313361553 / 6250000000000 : ℝ)) (b := (16822475233 / 10000000000000 : ℝ)) (q := (231156795623 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12250])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12250])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12250]

theorem cert12250_51 : CellCertificate 12250 (35988224234511 / 400000000000000 : ℝ) (1714667950701239 / 1000000000000000000 : ℝ) (346669699379957 / 10000000000000000 : ℝ)
    (cell12250 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · have h := gap_lower (n := 12250) (a := (82323106172959 / 100000000000000 : ℝ)) (b := (16822475233 / 10000000000000 : ℝ)) (q := (2311571949553 / 100000000000000 : ℝ))
      (E := (cell12250 ⟨51, by decide⟩).energy) (xi := (346669699379957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12250 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12250]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12250])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12250) (a := (82323106172959 / 100000000000000 : ℝ)) (b := (16822475233 / 10000000000000 : ℝ)) (q := (2311571949553 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12250])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12250])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12250]

theorem cert12250_52 : CellCertificate 12250 (35988224234511 / 400000000000000 : ℝ) (1714667950701239 / 1000000000000000000 : ℝ) (346669699379957 / 10000000000000000 : ℝ)
    (cell12250 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · have h := gap_lower (n := 12250) (a := (20572305518419 / 25000000000000 : ℝ)) (b := (16822475233 / 10000000000000 : ℝ)) (q := (36118373629 / 1562500000000 : ℝ))
      (E := (cell12250 ⟨52, by decide⟩).energy) (xi := (346669699379957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12250 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12250]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12250])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12250) (a := (20572305518419 / 25000000000000 : ℝ)) (b := (16822475233 / 10000000000000 : ℝ)) (q := (36118373629 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12250])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12250])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12250]

theorem cert12250_53 : CellCertificate 12250 (35988224234511 / 400000000000000 : ℝ) (1714667950701239 / 1000000000000000000 : ℝ) (346669699379957 / 10000000000000000 : ℝ)
    (cell12250 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · have h := gap_lower (n := 12250) (a := (20563840364609 / 25000000000000 : ℝ)) (b := (16822475233 / 10000000000000 : ℝ)) (q := (2311579901067 / 100000000000000 : ℝ))
      (E := (cell12250 ⟨53, by decide⟩).energy) (xi := (346669699379957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12250 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12250]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12250])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12250) (a := (20563840364609 / 25000000000000 : ℝ)) (b := (16822475233 / 10000000000000 : ℝ)) (q := (2311579901067 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12250])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12250])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12250]

theorem cert12250_54 : CellCertificate 12250 (35988224234511 / 400000000000000 : ℝ) (1714667950701239 / 1000000000000000000 : ℝ) (346669699379957 / 10000000000000000 : ℝ)
    (cell12250 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · have h := gap_lower (n := 12250) (a := (82221524298819 / 100000000000000 : ℝ)) (b := (16822475233 / 10000000000000 : ℝ)) (q := (72236997299 / 3125000000000 : ℝ))
      (E := (cell12250 ⟨54, by decide⟩).energy) (xi := (346669699379957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12250 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12250]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12250])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12250) (a := (82221524298819 / 100000000000000 : ℝ)) (b := (16822475233 / 10000000000000 : ℝ)) (q := (72236997299 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12250])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12250])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12250]

theorem cert12250_55 : CellCertificate 12250 (35988224234511 / 400000000000000 : ℝ) (1714667950701239 / 1000000000000000000 : ℝ) (346669699379957 / 10000000000000000 : ℝ)
    (cell12250 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · have h := gap_lower (n := 12250) (a := (20546927641637 / 25000000000000 : ℝ)) (b := (16822475233 / 10000000000000 : ℝ)) (q := (92463515523 / 4000000000000 : ℝ))
      (E := (cell12250 ⟨55, by decide⟩).energy) (xi := (346669699379957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12250 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12250]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12250])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12250) (a := (20546927641637 / 25000000000000 : ℝ)) (b := (16822475233 / 10000000000000 : ℝ)) (q := (92463515523 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12250])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12250])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12250]

theorem cert12250_56 : CellCertificate 12250 (35988224234511 / 400000000000000 : ℝ) (1714667950701239 / 1000000000000000000 : ℝ) (346669699379957 / 10000000000000000 : ℝ)
    (cell12250 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · have h := gap_lower (n := 12250) (a := (5134620014593 / 6250000000000 : ℝ)) (b := (16822475233 / 10000000000000 : ℝ)) (q := (2311591880753 / 100000000000000 : ℝ))
      (E := (cell12250 ⟨56, by decide⟩).energy) (xi := (346669699379957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12250 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12250]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12250])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12250) (a := (5134620014593 / 6250000000000 : ℝ)) (b := (16822475233 / 10000000000000 : ℝ)) (q := (2311591880753 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12250])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12250])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12250]

theorem cert12250_57 : CellCertificate 12250 (35988224234511 / 400000000000000 : ℝ) (1714667950701239 / 1000000000000000000 : ℝ) (346669699379957 / 10000000000000000 : ℝ)
    (cell12250 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · have h := gap_lower (n := 12250) (a := (20530038317911 / 25000000000000 : ℝ)) (b := (16822475233 / 10000000000000 : ℝ)) (q := (2311595888551 / 100000000000000 : ℝ))
      (E := (cell12250 ⟨57, by decide⟩).energy) (xi := (346669699379957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12250 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12250]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12250])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12250) (a := (20530038317911 / 25000000000000 : ℝ)) (b := (16822475233 / 10000000000000 : ℝ)) (q := (2311595888551 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12250])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12250])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12250]

theorem cert12250_58 : CellCertificate 12250 (35988224234511 / 400000000000000 : ℝ) (1714667950701239 / 1000000000000000000 : ℝ) (346669699379957 / 10000000000000000 : ℝ)
    (cell12250 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · have h := gap_lower (n := 12250) (a := (82086409653161 / 100000000000000 : ℝ)) (b := (16822475233 / 10000000000000 : ℝ)) (q := (2311599908211 / 100000000000000 : ℝ))
      (E := (cell12250 ⟨58, by decide⟩).energy) (xi := (346669699379957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12250 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12250]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12250])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12250) (a := (82086409653161 / 100000000000000 : ℝ)) (b := (16822475233 / 10000000000000 : ℝ)) (q := (2311599908211 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12250])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12250])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12250]

theorem cert12250_59 : CellCertificate 12250 (35988224234511 / 400000000000000 : ℝ) (1714667950701239 / 1000000000000000000 : ℝ) (346669699379957 / 10000000000000000 : ℝ)
    (cell12250 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · have h := gap_lower (n := 12250) (a := (3282107574013 / 4000000000000 : ℝ)) (b := (16822475233 / 10000000000000 : ℝ)) (q := (1155801938557 / 50000000000000 : ℝ))
      (E := (cell12250 ⟨59, by decide⟩).energy) (xi := (346669699379957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12250 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12250]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12250])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12250) (a := (3282107574013 / 4000000000000 : ℝ)) (b := (16822475233 / 10000000000000 : ℝ)) (q := (1155801938557 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12250])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12250])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12250]

theorem cert12251_40 : CellCertificate 12251 (224918915939031 / 2500000000000000 : ℝ) (214315992691063 / 125000000000000000 : ℝ) (173320321781477 / 5000000000000000 : ℝ)
    (cell12251 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · have h := gap_lower (n := 12251) (a := (41348693197449 / 50000000000000 : ℝ)) (b := (168210836769 / 100000000000000 : ℝ)) (q := (462276147547 / 20000000000000 : ℝ))
      (E := (cell12251 ⟨40, by decide⟩).energy) (xi := (173320321781477 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12251 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12251]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12251])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12251) (a := (41348693197449 / 50000000000000 : ℝ)) (b := (168210836769 / 100000000000000 : ℝ)) (q := (462276147547 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12251])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12251])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12251]

theorem cert12251_41 : CellCertificate 12251 (224918915939031 / 2500000000000000 : ℝ) (214315992691063 / 125000000000000000 : ℝ) (173320321781477 / 5000000000000000 : ℝ)
    (cell12251 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · have h := gap_lower (n := 12251) (a := (20665810593443 / 25000000000000 : ℝ)) (b := (168210836769 / 100000000000000 : ℝ)) (q := (2311384750147 / 100000000000000 : ℝ))
      (E := (cell12251 ⟨41, by decide⟩).energy) (xi := (173320321781477 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12251 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12251]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12251])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12251) (a := (20665810593443 / 25000000000000 : ℝ)) (b := (168210836769 / 100000000000000 : ℝ)) (q := (2311384750147 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12251])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12251])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12251]

theorem cert12251_42 : CellCertificate 12251 (224918915939031 / 2500000000000000 : ℝ) (214315992691063 / 125000000000000000 : ℝ) (173320321781477 / 5000000000000000 : ℝ)
    (cell12251 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · have h := gap_lower (n := 12251) (a := (82629122158513 / 100000000000000 : ℝ)) (b := (168210836769 / 100000000000000 : ℝ)) (q := (577847185861 / 25000000000000 : ℝ))
      (E := (cell12251 ⟨42, by decide⟩).energy) (xi := (173320321781477 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12251 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12251]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12251])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12251) (a := (82629122158513 / 100000000000000 : ℝ)) (b := (168210836769 / 100000000000000 : ℝ)) (q := (577847185861 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12251])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12251])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12251]

theorem cert12251_43 : CellCertificate 12251 (224918915939031 / 2500000000000000 : ℝ) (214315992691063 / 125000000000000000 : ℝ) (173320321781477 / 5000000000000000 : ℝ)
    (cell12251 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · have h := gap_lower (n := 12251) (a := (82595025719077 / 100000000000000 : ℝ)) (b := (168210836769 / 100000000000000 : ℝ)) (q := (72231024259 / 3125000000000 : ℝ))
      (E := (cell12251 ⟨43, by decide⟩).energy) (xi := (173320321781477 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12251 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12251]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12251])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12251) (a := (82595025719077 / 100000000000000 : ℝ)) (b := (168210836769 / 100000000000000 : ℝ)) (q := (72231024259 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12251])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12251])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12251]

theorem cert12251_44 : CellCertificate 12251 (224918915939031 / 2500000000000000 : ℝ) (214315992691063 / 125000000000000000 : ℝ) (173320321781477 / 5000000000000000 : ℝ)
    (cell12251 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · have h := gap_lower (n := 12251) (a := (3302438121023 / 4000000000000 : ℝ)) (b := (168210836769 / 100000000000000 : ℝ)) (q := (1155698365411 / 50000000000000 : ℝ))
      (E := (cell12251 ⟨44, by decide⟩).energy) (xi := (173320321781477 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12251 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12251]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12251])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12251) (a := (3302438121023 / 4000000000000 : ℝ)) (b := (168210836769 / 100000000000000 : ℝ)) (q := (1155698365411 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12251])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12251])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12251]

theorem cert12251_45 : CellCertificate 12251 (224918915939031 / 2500000000000000 : ℝ) (214315992691063 / 125000000000000000 : ℝ) (173320321781477 / 5000000000000000 : ℝ)
    (cell12251 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · have h := gap_lower (n := 12251) (a := (16505380809653 / 20000000000000 : ℝ)) (b := (168210836769 / 100000000000000 : ℝ)) (q := (462280144813 / 20000000000000 : ℝ))
      (E := (cell12251 ⟨45, by decide⟩).energy) (xi := (173320321781477 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12251 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12251]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12251])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12251) (a := (16505380809653 / 20000000000000 : ℝ)) (b := (168210836769 / 100000000000000 : ℝ)) (q := (462280144813 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12251])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12251])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12251]

theorem cert12251_46 : CellCertificate 12251 (224918915939031 / 2500000000000000 : ℝ) (214315992691063 / 125000000000000000 : ℝ) (173320321781477 / 5000000000000000 : ℝ)
    (cell12251 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · have h := gap_lower (n := 12251) (a := (82492878757557 / 100000000000000 : ℝ)) (b := (168210836769 / 100000000000000 : ℝ)) (q := (577851188829 / 25000000000000 : ℝ))
      (E := (cell12251 ⟨46, by decide⟩).energy) (xi := (173320321781477 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12251 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12251]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12251])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12251) (a := (82492878757557 / 100000000000000 : ℝ)) (b := (168210836769 / 100000000000000 : ℝ)) (q := (577851188829 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12251])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12251])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12251]

theorem cert12251_47 : CellCertificate 12251 (224918915939031 / 2500000000000000 : ℝ) (214315992691063 / 125000000000000000 : ℝ) (173320321781477 / 5000000000000000 : ℝ)
    (cell12251 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · have h := gap_lower (n := 12251) (a := (82458877124013 / 100000000000000 : ℝ)) (b := (168210836769 / 100000000000000 : ℝ)) (q := (2311408705923 / 100000000000000 : ℝ))
      (E := (cell12251 ⟨47, by decide⟩).energy) (xi := (173320321781477 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12251 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12251]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12251])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12251) (a := (82458877124013 / 100000000000000 : ℝ)) (b := (168210836769 / 100000000000000 : ℝ)) (q := (2311408705923 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12251])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12251])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12251]

theorem cert12251_48 : CellCertificate 12251 (224918915939031 / 2500000000000000 : ℝ) (214315992691063 / 125000000000000000 : ℝ) (173320321781477 / 5000000000000000 : ℝ)
    (cell12251 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · have h := gap_lower (n := 12251) (a := (82424899118339 / 100000000000000 : ℝ)) (b := (168210836769 / 100000000000000 : ℝ)) (q := (1155706375641 / 50000000000000 : ℝ))
      (E := (cell12251 ⟨48, by decide⟩).energy) (xi := (173320321781477 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12251 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12251]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12251])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12251) (a := (82424899118339 / 100000000000000 : ℝ)) (b := (168210836769 / 100000000000000 : ℝ)) (q := (1155706375641 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12251])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12251])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12251]

theorem cert12251_49 : CellCertificate 12251 (224918915939031 / 2500000000000000 : ℝ) (214315992691063 / 125000000000000000 : ℝ) (173320321781477 / 5000000000000000 : ℝ)
    (cell12251 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · have h := gap_lower (n := 12251) (a := (82390944711391 / 100000000000000 : ℝ)) (b := (168210836769 / 100000000000000 : ℝ)) (q := (577854178343 / 25000000000000 : ℝ))
      (E := (cell12251 ⟨49, by decide⟩).energy) (xi := (173320321781477 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12251 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12251]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12251])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12251) (a := (82390944711391 / 100000000000000 : ℝ)) (b := (168210836769 / 100000000000000 : ℝ)) (q := (577854178343 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12251])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12251])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12251]

theorem cert12251_50 : CellCertificate 12251 (224918915939031 / 2500000000000000 : ℝ) (214315992691063 / 125000000000000000 : ℝ) (173320321781477 / 5000000000000000 : ℝ)
    (cell12251 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · have h := gap_lower (n := 12251) (a := (82357013874173 / 100000000000000 : ℝ)) (b := (168210836769 / 100000000000000 : ℝ)) (q := (2311420708357 / 100000000000000 : ℝ))
      (E := (cell12251 ⟨50, by decide⟩).energy) (xi := (173320321781477 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12251 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12251]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12251])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12251) (a := (82357013874173 / 100000000000000 : ℝ)) (b := (168210836769 / 100000000000000 : ℝ)) (q := (2311420708357 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12251])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12251])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12251]

theorem cert12251_51 : CellCertificate 12251 (224918915939031 / 2500000000000000 : ℝ) (214315992691063 / 125000000000000000 : ℝ) (173320321781477 / 5000000000000000 : ℝ)
    (cell12251 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · have h := gap_lower (n := 12251) (a := (10290388322229 / 12500000000000 : ℝ)) (b := (168210836769 / 100000000000000 : ℝ)) (q := (2311424734459 / 100000000000000 : ℝ))
      (E := (cell12251 ⟨51, by decide⟩).energy) (xi := (173320321781477 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12251 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12251]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12251])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12251) (a := (10290388322229 / 12500000000000 : ℝ)) (b := (168210836769 / 100000000000000 : ℝ)) (q := (2311424734459 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12251])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12251])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12251]

theorem cert12251_52 : CellCertificate 12251 (224918915939031 / 2500000000000000 : ℝ) (214315992691063 / 125000000000000000 : ℝ) (173320321781477 / 5000000000000000 : ℝ)
    (cell12251 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · have h := gap_lower (n := 12251) (a := (82289222793661 / 100000000000000 : ℝ)) (b := (168210836769 / 100000000000000 : ℝ)) (q := (1155714365349 / 50000000000000 : ℝ))
      (E := (cell12251 ⟨52, by decide⟩).energy) (xi := (173320321781477 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12251 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12251]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12251])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12251) (a := (82289222793661 / 100000000000000 : ℝ)) (b := (168210836769 / 100000000000000 : ℝ)) (q := (1155714365349 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12251])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12251])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12251]

theorem cert12251_53 : CellCertificate 12251 (224918915939031 / 2500000000000000 : ℝ) (214315992691063 / 125000000000000000 : ℝ) (173320321781477 / 5000000000000000 : ℝ)
    (cell12251 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · have h := gap_lower (n := 12251) (a := (82255362493099 / 100000000000000 : ℝ)) (b := (168210836769 / 100000000000000 : ℝ)) (q := (577858173699 / 25000000000000 : ℝ))
      (E := (cell12251 ⟨53, by decide⟩).energy) (xi := (173320321781477 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12251 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12251]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12251])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12251) (a := (82255362493099 / 100000000000000 : ℝ)) (b := (168210836769 / 100000000000000 : ℝ)) (q := (577858173699 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12251])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12251])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12251]

theorem cert12251_54 : CellCertificate 12251 (224918915939031 / 2500000000000000 : ℝ) (214315992691063 / 125000000000000000 : ℝ) (173320321781477 / 5000000000000000 : ℝ)
    (cell12251 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · have h := gap_lower (n := 12251) (a := (41110762823863 / 50000000000000 : ℝ)) (b := (168210836769 / 100000000000000 : ℝ)) (q := (462287336659 / 20000000000000 : ℝ))
      (E := (cell12251 ⟨54, by decide⟩).energy) (xi := (173320321781477 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12251 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12251]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12251])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12251) (a := (41110762823863 / 50000000000000 : ℝ)) (b := (168210836769 / 100000000000000 : ℝ)) (q := (462287336659 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12251])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12251])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12251]

theorem cert12251_55 : CellCertificate 12251 (224918915939031 / 2500000000000000 : ℝ) (214315992691063 / 125000000000000000 : ℝ) (173320321781477 / 5000000000000000 : ℝ)
    (cell12251 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · have h := gap_lower (n := 12251) (a := (41093856114633 / 50000000000000 : ℝ)) (b := (168210836769 / 100000000000000 : ℝ)) (q := (1155720346781 / 50000000000000 : ℝ))
      (E := (cell12251 ⟨55, by decide⟩).energy) (xi := (173320321781477 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12251 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12251]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12251])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12251) (a := (41093856114633 / 50000000000000 : ℝ)) (b := (168210836769 / 100000000000000 : ℝ)) (q := (1155720346781 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12251])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12251])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12251]

theorem cert12251_56 : CellCertificate 12251 (224918915939031 / 2500000000000000 : ℝ) (214315992691063 / 125000000000000000 : ℝ) (173320321781477 / 5000000000000000 : ℝ)
    (cell12251 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · have h := gap_lower (n := 12251) (a := (16430784441917 / 20000000000000 : ℝ)) (b := (168210836769 / 100000000000000 : ℝ)) (q := (577861180689 / 25000000000000 : ℝ))
      (E := (cell12251 ⟨56, by decide⟩).energy) (xi := (173320321781477 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12251 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12251]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12251])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12251) (a := (16430784441917 / 20000000000000 : ℝ)) (b := (168210836769 / 100000000000000 : ℝ)) (q := (577861180689 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12251])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12251])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12251]

theorem cert12251_57 : CellCertificate 12251 (224918915939031 / 2500000000000000 : ℝ) (214315992691063 / 125000000000000000 : ℝ) (173320321781477 / 5000000000000000 : ℝ)
    (cell12251 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · have h := gap_lower (n := 12251) (a := (82120155560687 / 100000000000000 : ℝ)) (b := (168210836769 / 100000000000000 : ℝ)) (q := (577862177181 / 25000000000000 : ℝ))
      (E := (cell12251 ⟨57, by decide⟩).energy) (xi := (173320321781477 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12251 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12251]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12251])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12251) (a := (82120155560687 / 100000000000000 : ℝ)) (b := (168210836769 / 100000000000000 : ℝ)) (q := (577862177181 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12251])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12251])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12251]

theorem cert12251_58 : CellCertificate 12251 (224918915939031 / 2500000000000000 : ℝ) (214315992691063 / 125000000000000000 : ℝ) (173320321781477 / 5000000000000000 : ℝ)
    (cell12251 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · have h := gap_lower (n := 12251) (a := (82086412254721 / 100000000000000 : ℝ)) (b := (168210836769 / 100000000000000 : ℝ)) (q := (115572635363 / 5000000000000 : ℝ))
      (E := (cell12251 ⟨58, by decide⟩).energy) (xi := (173320321781477 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12251 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12251]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12251])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12251) (a := (82086412254721 / 100000000000000 : ℝ)) (b := (168210836769 / 100000000000000 : ℝ)) (q := (115572635363 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12251])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12251])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12251]

theorem cert12251_59 : CellCertificate 12251 (224918915939031 / 2500000000000000 : ℝ) (214315992691063 / 125000000000000000 : ℝ) (173320321781477 / 5000000000000000 : ℝ)
    (cell12251 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · have h := gap_lower (n := 12251) (a := (82052692263971 / 100000000000000 : ℝ)) (b := (168210836769 / 100000000000000 : ℝ)) (q := (462291342979 / 20000000000000 : ℝ))
      (E := (cell12251 ⟨59, by decide⟩).energy) (xi := (173320321781477 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12251 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12251]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12251])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12251) (a := (82052692263971 / 100000000000000 : ℝ)) (b := (168210836769 / 100000000000000 : ℝ)) (q := (462291342979 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12251])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12251])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12251]

theorem cert12252_40 : CellCertificate 12252 (449822863179663 / 5000000000000000 : ℝ) (53574623600577 / 31250000000000000 : ℝ) (173305796370777 / 5000000000000000 : ℝ)
    (cell12252 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · have h := gap_lower (n := 12252) (a := (82697383305631 / 100000000000000 : ℝ)) (b := (8409846177 / 5000000000000 : ℝ)) (q := (2311233669917 / 100000000000000 : ℝ))
      (E := (cell12252 ⟨40, by decide⟩).energy) (xi := (173305796370777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12252 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12252]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12252])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12252) (a := (82697383305631 / 100000000000000 : ℝ)) (b := (8409846177 / 5000000000000 : ℝ)) (q := (2311233669917 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12252])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12252])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12252]

theorem cert12252_41 : CellCertificate 12252 (449822863179663 / 5000000000000000 : ℝ) (53574623600577 / 31250000000000000 : ℝ) (173305796370777 / 5000000000000000 : ℝ)
    (cell12252 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · have h := gap_lower (n := 12252) (a := (82663239604409 / 100000000000000 : ℝ)) (b := (8409846177 / 5000000000000 : ℝ)) (q := (2311237648987 / 100000000000000 : ℝ))
      (E := (cell12252 ⟨41, by decide⟩).energy) (xi := (173305796370777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12252 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12252]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12252])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12252) (a := (82663239604409 / 100000000000000 : ℝ)) (b := (8409846177 / 5000000000000 : ℝ)) (q := (2311237648987 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12252])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12252])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12252]

theorem cert12252_42 : CellCertificate 12252 (449822863179663 / 5000000000000000 : ℝ) (53574623600577 / 31250000000000000 : ℝ) (173305796370777 / 5000000000000000 : ℝ)
    (cell12252 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · have h := gap_lower (n := 12252) (a := (8262911970861 / 10000000000000 : ℝ)) (b := (8409846177 / 5000000000000 : ℝ)) (q := (1155620804831 / 50000000000000 : ℝ))
      (E := (cell12252 ⟨42, by decide⟩).energy) (xi := (173305796370777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12252 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12252]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12252])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12252) (a := (8262911970861 / 10000000000000 : ℝ)) (b := (8409846177 / 5000000000000 : ℝ)) (q := (1155620804831 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12252])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12252])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12252]

theorem cert12252_43 : CellCertificate 12252 (449822863179663 / 5000000000000000 : ℝ) (53574623600577 / 31250000000000000 : ℝ) (173305796370777 / 5000000000000000 : ℝ)
    (cell12252 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · have h := gap_lower (n := 12252) (a := (82595023588193 / 100000000000000 : ℝ)) (b := (8409846177 / 5000000000000 : ℝ)) (q := (11556228053 / 500000000000 : ℝ))
      (E := (cell12252 ⟨43, by decide⟩).energy) (xi := (173305796370777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12252 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12252]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12252])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12252) (a := (82595023588193 / 100000000000000 : ℝ)) (b := (8409846177 / 5000000000000 : ℝ)) (q := (11556228053 / 500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12252])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12252])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12252]

theorem cert12252_44 : CellCertificate 12252 (449822863179663 / 5000000000000000 : ℝ) (53574623600577 / 31250000000000000 : ℝ) (173305796370777 / 5000000000000000 : ℝ)
    (cell12252 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · have h := gap_lower (n := 12252) (a := (82560951213267 / 100000000000000 : ℝ)) (b := (8409846177 / 5000000000000 : ℝ)) (q := (1155624796371 / 50000000000000 : ℝ))
      (E := (cell12252 ⟨44, by decide⟩).energy) (xi := (173305796370777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12252 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12252]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12252])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12252) (a := (82560951213267 / 100000000000000 : ℝ)) (b := (8409846177 / 5000000000000 : ℝ)) (q := (1155624796371 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12252])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12252])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12252]

theorem cert12252_45 : CellCertificate 12252 (449822863179663 / 5000000000000000 : ℝ) (53574623600577 / 31250000000000000 : ℝ) (173305796370777 / 5000000000000000 : ℝ)
    (cell12252 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · have h := gap_lower (n := 12252) (a := (82526902554093 / 100000000000000 : ℝ)) (b := (8409846177 / 5000000000000 : ℝ)) (q := (577813403589 / 25000000000000 : ℝ))
      (E := (cell12252 ⟨45, by decide⟩).energy) (xi := (173305796370777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12252 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12252]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12252])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12252) (a := (82526902554093 / 100000000000000 : ℝ)) (b := (8409846177 / 5000000000000 : ℝ)) (q := (577813403589 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12252])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12252])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12252]

theorem cert12252_46 : CellCertificate 12252 (449822863179663 / 5000000000000000 : ℝ) (53574623600577 / 31250000000000000 : ℝ) (173305796370777 / 5000000000000000 : ℝ)
    (cell12252 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · have h := gap_lower (n := 12252) (a := (41246438790541 / 50000000000000 : ℝ)) (b := (8409846177 / 5000000000000 : ℝ)) (q := (1155628807949 / 50000000000000 : ℝ))
      (E := (cell12252 ⟨46, by decide⟩).energy) (xi := (173305796370777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12252 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12252]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12252])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12252) (a := (41246438790541 / 50000000000000 : ℝ)) (b := (8409846177 / 5000000000000 : ℝ)) (q := (1155628807949 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12252])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12252])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12252]

theorem cert12252_47 : CellCertificate 12252 (449822863179663 / 5000000000000000 : ℝ) (53574623600577 / 31250000000000000 : ℝ) (173305796370777 / 5000000000000000 : ℝ)
    (cell12252 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · have h := gap_lower (n := 12252) (a := (41229438132397 / 50000000000000 : ℝ)) (b := (8409846177 / 5000000000000 : ℝ)) (q := (2311261596379 / 100000000000000 : ℝ))
      (E := (cell12252 ⟨47, by decide⟩).energy) (xi := (173305796370777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12252 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12252]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12252])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12252) (a := (41229438132397 / 50000000000000 : ℝ)) (b := (8409846177 / 5000000000000 : ℝ)) (q := (2311261596379 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12252])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12252])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12252]

theorem cert12252_48 : CellCertificate 12252 (449822863179663 / 5000000000000000 : ℝ) (53574623600577 / 31250000000000000 : ℝ) (173305796370777 / 5000000000000000 : ℝ)
    (cell12252 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · have h := gap_lower (n := 12252) (a := (82424898575939 / 100000000000000 : ℝ)) (b := (8409846177 / 5000000000000 : ℝ)) (q := (2311265613481 / 100000000000000 : ℝ))
      (E := (cell12252 ⟨48, by decide⟩).energy) (xi := (173305796370777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12252 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12252]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12252])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12252) (a := (82424898575939 / 100000000000000 : ℝ)) (b := (8409846177 / 5000000000000 : ℝ)) (q := (2311265613481 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12252])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12252])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12252]

theorem cert12252_49 : CellCertificate 12252 (449822863179663 / 5000000000000000 : ℝ) (53574623600577 / 31250000000000000 : ℝ) (173305796370777 / 5000000000000000 : ℝ)
    (cell12252 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · have h := gap_lower (n := 12252) (a := (20597736121343 / 25000000000000 : ℝ)) (b := (8409846177 / 5000000000000 : ℝ)) (q := (1155634803471 / 50000000000000 : ℝ))
      (E := (cell12252 ⟨49, by decide⟩).energy) (xi := (173305796370777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12252 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12252]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12252])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12252) (a := (20597736121343 / 25000000000000 : ℝ)) (b := (8409846177 / 5000000000000 : ℝ)) (q := (1155634803471 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12252])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12252])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12252]

theorem cert12252_50 : CellCertificate 12252 (449822863179663 / 5000000000000000 : ℝ) (53574623600577 / 31250000000000000 : ℝ) (173305796370777 / 5000000000000000 : ℝ)
    (cell12252 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · have h := gap_lower (n := 12252) (a := (41178506982049 / 50000000000000 : ℝ)) (b := (8409846177 / 5000000000000 : ℝ)) (q := (2311273575121 / 100000000000000 : ℝ))
      (E := (cell12252 ⟨50, by decide⟩).energy) (xi := (173305796370777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12252 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12252]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12252])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12252) (a := (41178506982049 / 50000000000000 : ℝ)) (b := (8409846177 / 5000000000000 : ℝ)) (q := (2311273575121 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12252])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12252])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12252]

theorem cert12252_51 : CellCertificate 12252 (449822863179663 / 5000000000000000 : ℝ) (53574623600577 / 31250000000000000 : ℝ) (173305796370777 / 5000000000000000 : ℝ)
    (cell12252 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · have h := gap_lower (n := 12252) (a := (2572597093227 / 3125000000000 : ℝ)) (b := (8409846177 / 5000000000000 : ℝ)) (q := (2311277575129 / 100000000000000 : ℝ))
      (E := (cell12252 ⟨51, by decide⟩).energy) (xi := (173305796370777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12252 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12252]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12252])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12252) (a := (2572597093227 / 3125000000000 : ℝ)) (b := (8409846177 / 5000000000000 : ℝ)) (q := (2311277575129 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12252])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12252])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12252]

theorem cert12252_52 : CellCertificate 12252 (449822863179663 / 5000000000000000 : ℝ) (53574623600577 / 31250000000000000 : ℝ) (173305796370777 / 5000000000000000 : ℝ)
    (cell12252 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · have h := gap_lower (n := 12252) (a := (82289223514167 / 100000000000000 : ℝ)) (b := (8409846177 / 5000000000000 : ℝ)) (q := (2311281604969 / 100000000000000 : ℝ))
      (E := (cell12252 ⟨52, by decide⟩).energy) (xi := (173305796370777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12252 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12252]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12252])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12252) (a := (82289223514167 / 100000000000000 : ℝ)) (b := (8409846177 / 5000000000000 : ℝ)) (q := (2311281604969 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12252])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12252])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12252]

theorem cert12252_53 : CellCertificate 12252 (449822863179663 / 5000000000000000 : ℝ) (53574623600577 / 31250000000000000 : ℝ) (173305796370777 / 5000000000000000 : ℝ)
    (cell12252 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · have h := gap_lower (n := 12252) (a := (82255363528243 / 100000000000000 : ℝ)) (b := (8409846177 / 5000000000000 : ℝ)) (q := (1155642801713 / 50000000000000 : ℝ))
      (E := (cell12252 ⟨53, by decide⟩).energy) (xi := (173305796370777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12252 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12252]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12252])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12252) (a := (82255363528243 / 100000000000000 : ℝ)) (b := (8409846177 / 5000000000000 : ℝ)) (q := (1155642801713 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12252])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12252])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12252]

theorem cert12252_54 : CellCertificate 12252 (449822863179663 / 5000000000000000 : ℝ) (53574623600577 / 31250000000000000 : ℝ) (173305796370777 / 5000000000000000 : ℝ)
    (cell12252 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · have h := gap_lower (n := 12252) (a := (3288861079883 / 4000000000000 : ℝ)) (b := (8409846177 / 5000000000000 : ℝ)) (q := (288911196001 / 12500000000000 : ℝ))
      (E := (cell12252 ⟨54, by decide⟩).energy) (xi := (173305796370777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12252 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12252]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12252])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12252) (a := (3288861079883 / 4000000000000 : ℝ)) (b := (8409846177 / 5000000000000 : ℝ)) (q := (288911196001 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12252])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12252])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12252]

theorem cert12252_55 : CellCertificate 12252 (449822863179663 / 5000000000000000 : ℝ) (53574623600577 / 31250000000000000 : ℝ) (173305796370777 / 5000000000000000 : ℝ)
    (cell12252 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · have h := gap_lower (n := 12252) (a := (41093856946193 / 50000000000000 : ℝ)) (b := (8409846177 / 5000000000000 : ℝ)) (q := (2311293555069 / 100000000000000 : ℝ))
      (E := (cell12252 ⟨55, by decide⟩).energy) (xi := (173305796370777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12252 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12252]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12252])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12252) (a := (41093856946193 / 50000000000000 : ℝ)) (b := (8409846177 / 5000000000000 : ℝ)) (q := (2311293555069 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12252])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12252])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12252]

theorem cert12252_56 : CellCertificate 12252 (449822863179663 / 5000000000000000 : ℝ) (53574623600577 / 31250000000000000 : ℝ) (173305796370777 / 5000000000000000 : ℝ)
    (cell12252 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · have h := gap_lower (n := 12252) (a := (20538481046511 / 25000000000000 : ℝ)) (b := (8409846177 / 5000000000000 : ℝ)) (q := (462259512353 / 20000000000000 : ℝ))
      (E := (cell12252 ⟨56, by decide⟩).energy) (xi := (173305796370777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12252 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12252]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12252])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12252) (a := (20538481046511 / 25000000000000 : ℝ)) (b := (8409846177 / 5000000000000 : ℝ)) (q := (462259512353 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12252])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12252])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12252]

theorem cert12252_57 : CellCertificate 12252 (449822863179663 / 5000000000000000 : ℝ) (53574623600577 / 31250000000000000 : ℝ) (173305796370777 / 5000000000000000 : ℝ)
    (cell12252 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · have h := gap_lower (n := 12252) (a := (16424031570011 / 20000000000000 : ℝ)) (b := (8409846177 / 5000000000000 : ℝ)) (q := (462260317009 / 20000000000000 : ℝ))
      (E := (cell12252 ⟨57, by decide⟩).energy) (xi := (173305796370777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12252 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12252]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12252])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12252) (a := (16424031570011 / 20000000000000 : ℝ)) (b := (8409846177 / 5000000000000 : ℝ)) (q := (462260317009 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12252])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12252])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12252]

theorem cert12252_58 : CellCertificate 12252 (449822863179663 / 5000000000000000 : ℝ) (53574623600577 / 31250000000000000 : ℝ) (173305796370777 / 5000000000000000 : ℝ)
    (cell12252 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · have h := gap_lower (n := 12252) (a := (16417282971313 / 20000000000000 : ℝ)) (b := (8409846177 / 5000000000000 : ℝ)) (q := (2311305562521 / 100000000000000 : ℝ))
      (E := (cell12252 ⟨58, by decide⟩).energy) (xi := (173305796370777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12252 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12252]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12252])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12252) (a := (16417282971313 / 20000000000000 : ℝ)) (b := (8409846177 / 5000000000000 : ℝ)) (q := (2311305562521 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12252])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12252])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12252]

theorem cert12252_59 : CellCertificate 12252 (449822863179663 / 5000000000000000 : ℝ) (53574623600577 / 31250000000000000 : ℝ) (173305796370777 / 5000000000000000 : ℝ)
    (cell12252 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · have h := gap_lower (n := 12252) (a := (41026347588931 / 50000000000000 : ℝ)) (b := (8409846177 / 5000000000000 : ℝ)) (q := (2311309549803 / 100000000000000 : ℝ))
      (E := (cell12252 ⟨59, by decide⟩).energy) (xi := (173305796370777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12252 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12252]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12252])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12252) (a := (41026347588931 / 50000000000000 : ℝ)) (b := (8409846177 / 5000000000000 : ℝ)) (q := (2311309549803 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12252])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12252])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12252]

theorem cert12253_40 : CellCertificate 12253 (56225987104451 / 625000000000000 : ℝ) (1714247991765521 / 1000000000000000000 : ℝ) (43322818364287 / 1250000000000000 : ℝ)
    (cell12253 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · have h := gap_lower (n := 12253) (a := (82697380217363 / 100000000000000 : ℝ)) (b := (42045753161 / 25000000000000 : ℝ)) (q := (577771649613 / 25000000000000 : ℝ))
      (E := (cell12253 ⟨40, by decide⟩).energy) (xi := (43322818364287 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12253 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12253]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12253])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12253) (a := (82697380217363 / 100000000000000 : ℝ)) (b := (42045753161 / 25000000000000 : ℝ)) (q := (577771649613 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12253])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12253])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12253]

theorem cert12253_41 : CellCertificate 12253 (56225987104451 / 625000000000000 : ℝ) (1714247991765521 / 1000000000000000000 : ℝ) (43322818364287 / 1250000000000000 : ℝ)
    (cell12253 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · have h := gap_lower (n := 12253) (a := (20665809209001 / 25000000000000 : ℝ)) (b := (42045753161 / 25000000000000 : ℝ)) (q := (2311090602947 / 100000000000000 : ℝ))
      (E := (cell12253 ⟨41, by decide⟩).energy) (xi := (43322818364287 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12253 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12253]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12253])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12253) (a := (20665809209001 / 25000000000000 : ℝ)) (b := (42045753161 / 25000000000000 : ℝ)) (q := (2311090602947 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12253])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12253])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12253]

theorem cert12253_42 : CellCertificate 12253 (56225987104451 / 625000000000000 : ℝ) (1714247991765521 / 1000000000000000000 : ℝ) (43322818364287 / 1250000000000000 : ℝ)
    (cell12253 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · have h := gap_lower (n := 12253) (a := (661032938077 / 800000000000 : ℝ)) (b := (42045753161 / 25000000000000 : ℝ)) (q := (577773647453 / 25000000000000 : ℝ))
      (E := (cell12253 ⟨42, by decide⟩).energy) (xi := (43322818364287 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12253 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12253]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12253])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12253) (a := (661032938077 / 800000000000 : ℝ)) (b := (42045753161 / 25000000000000 : ℝ)) (q := (577773647453 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12253])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12253])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12253]

theorem cert12253_43 : CellCertificate 12253 (56225987104451 / 625000000000000 : ℝ) (1714247991765521 / 1000000000000000000 : ℝ) (43322818364287 / 1250000000000000 : ℝ)
    (cell12253 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · have h := gap_lower (n := 12253) (a := (41297510729093 / 50000000000000 : ℝ)) (b := (42045753161 / 25000000000000 : ℝ)) (q := (462219723541 / 20000000000000 : ℝ))
      (E := (cell12253 ⟨43, by decide⟩).energy) (xi := (43322818364287 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12253 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12253]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12253])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12253) (a := (41297510729093 / 50000000000000 : ℝ)) (b := (42045753161 / 25000000000000 : ℝ)) (q := (462219723541 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12253])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12253])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12253]

theorem cert12253_44 : CellCertificate 12253 (56225987104451 / 625000000000000 : ℝ) (1714247991765521 / 1000000000000000000 : ℝ) (43322818364287 / 1250000000000000 : ℝ)
    (cell12253 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · have h := gap_lower (n := 12253) (a := (82560949401797 / 100000000000000 : ℝ)) (b := (42045753161 / 25000000000000 : ℝ)) (q := (2311102568771 / 100000000000000 : ℝ))
      (E := (cell12253 ⟨44, by decide⟩).energy) (xi := (43322818364287 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12253 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12253]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12253])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12253) (a := (82560949401797 / 100000000000000 : ℝ)) (b := (42045753161 / 25000000000000 : ℝ)) (q := (2311102568771 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12253])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12253])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12253]

theorem cert12253_45 : CellCertificate 12253 (56225987104451 / 625000000000000 : ℝ) (1714247991765521 / 1000000000000000000 : ℝ) (43322818364287 / 1250000000000000 : ℝ)
    (cell12253 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · have h := gap_lower (n := 12253) (a := (82526901060719 / 100000000000000 : ℝ)) (b := (42045753161 / 25000000000000 : ℝ)) (q := (92444262401 / 4000000000000 : ℝ))
      (E := (cell12253 ⟨45, by decide⟩).energy) (xi := (43322818364287 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12253 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12253]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12253])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12253) (a := (82526901060719 / 100000000000000 : ℝ)) (b := (42045753161 / 25000000000000 : ℝ)) (q := (92444262401 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12253])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12253])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12253]

theorem cert12253_46 : CellCertificate 12253 (56225987104451 / 625000000000000 : ℝ) (1714247991765521 / 1000000000000000000 : ℝ) (43322818364287 / 1250000000000000 : ℝ)
    (cell12253 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · have h := gap_lower (n := 12253) (a := (20623219101341 / 25000000000000 : ℝ)) (b := (42045753161 / 25000000000000 : ℝ)) (q := (1155555295383 / 50000000000000 : ℝ))
      (E := (cell12253 ⟨46, by decide⟩).energy) (xi := (43322818364287 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12253 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12253]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12253])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12253) (a := (20623219101341 / 25000000000000 : ℝ)) (b := (42045753161 / 25000000000000 : ℝ)) (q := (1155555295383 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12253])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12253])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12253]

theorem cert12253_47 : CellCertificate 12253 (56225987104451 / 625000000000000 : ℝ) (1714247991765521 / 1000000000000000000 : ℝ) (43322818364287 / 1250000000000000 : ℝ)
    (cell12253 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · have h := gap_lower (n := 12253) (a := (82458875406293 / 100000000000000 : ℝ)) (b := (42045753161 / 25000000000000 : ℝ)) (q := (2311114542341 / 100000000000000 : ℝ))
      (E := (cell12253 ⟨47, by decide⟩).energy) (xi := (43322818364287 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12253 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12253]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12253])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12253) (a := (82458875406293 / 100000000000000 : ℝ)) (b := (42045753161 / 25000000000000 : ℝ)) (q := (2311114542341 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12253])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12253])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12253]

theorem cert12253_48 : CellCertificate 12253 (56225987104451 / 625000000000000 : ℝ) (1714247991765521 / 1000000000000000000 : ℝ) (43322818364287 / 1250000000000000 : ℝ)
    (cell12253 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · have h := gap_lower (n := 12253) (a := (82424898034217 / 100000000000000 : ℝ)) (b := (42045753161 / 25000000000000 : ℝ)) (q := (2311118590141 / 100000000000000 : ℝ))
      (E := (cell12253 ⟨48, by decide⟩).energy) (xi := (43322818364287 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12253 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12253]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12253])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12253) (a := (82424898034217 / 100000000000000 : ℝ)) (b := (42045753161 / 25000000000000 : ℝ)) (q := (2311118590141 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12253])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12253])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12253]

theorem cert12253_49 : CellCertificate 12253 (56225987104451 / 625000000000000 : ℝ) (1714247991765521 / 1000000000000000000 : ℝ) (43322818364287 / 1250000000000000 : ℝ)
    (cell12253 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · have h := gap_lower (n := 12253) (a := (82390944259991 / 100000000000000 : ℝ)) (b := (42045753161 / 25000000000000 : ℝ)) (q := (2311122556147 / 100000000000000 : ℝ))
      (E := (cell12253 ⟨49, by decide⟩).energy) (xi := (43322818364287 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12253 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12253]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12253])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12253) (a := (82390944259991 / 100000000000000 : ℝ)) (b := (42045753161 / 25000000000000 : ℝ)) (q := (2311122556147 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12253])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12253])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12253]

theorem cert12253_50 : CellCertificate 12253 (56225987104451 / 625000000000000 : ℝ) (1714247991765521 / 1000000000000000000 : ℝ) (43322818364287 / 1250000000000000 : ℝ)
    (cell12253 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · have h := gap_lower (n := 12253) (a := (41178507027311 / 50000000000000 : ℝ)) (b := (42045753161 / 25000000000000 : ℝ)) (q := (2311126556521 / 100000000000000 : ℝ))
      (E := (cell12253 ⟨50, by decide⟩).energy) (xi := (43322818364287 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12253 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12253]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12253])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12253) (a := (41178507027311 / 50000000000000 : ℝ)) (b := (42045753161 / 25000000000000 : ℝ)) (q := (2311126556521 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12253])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12253])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12253]

theorem cert12253_51 : CellCertificate 12253 (56225987104451 / 625000000000000 : ℝ) (1714247991765521 / 1000000000000000000 : ℝ) (43322818364287 / 1250000000000000 : ℝ)
    (cell12253 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · have h := gap_lower (n := 12253) (a := (82323107389257 / 100000000000000 : ℝ)) (b := (42045753161 / 25000000000000 : ℝ)) (q := (1155565265261 / 50000000000000 : ℝ))
      (E := (cell12253 ⟨51, by decide⟩).energy) (xi := (43322818364287 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12253 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12253]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12253])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12253) (a := (82323107389257 / 100000000000000 : ℝ)) (b := (42045753161 / 25000000000000 : ℝ)) (q := (1155565265261 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12253])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12253])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12253]

theorem cert12253_52 : CellCertificate 12253 (56225987104451 / 625000000000000 : ℝ) (1714247991765521 / 1000000000000000000 : ℝ) (43322818364287 / 1250000000000000 : ℝ)
    (cell12253 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · have h := gap_lower (n := 12253) (a := (10286153029399 / 12500000000000 : ℝ)) (b := (42045753161 / 25000000000000 : ℝ)) (q := (577783633767 / 25000000000000 : ℝ))
      (E := (cell12253 ⟨52, by decide⟩).energy) (xi := (43322818364287 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12253 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12253]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12253])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12253) (a := (10286153029399 / 12500000000000 : ℝ)) (b := (42045753161 / 25000000000000 : ℝ)) (q := (577783633767 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12253])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12253])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12253]

theorem cert12253_53 : CellCertificate 12253 (56225987104451 / 625000000000000 : ℝ) (1714247991765521 / 1000000000000000000 : ℝ) (43322818364287 / 1250000000000000 : ℝ)
    (cell12253 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · have h := gap_lower (n := 12253) (a := (82255364563867 / 100000000000000 : ℝ)) (b := (42045753161 / 25000000000000 : ℝ)) (q := (577784641987 / 25000000000000 : ℝ))
      (E := (cell12253 ⟨53, by decide⟩).energy) (xi := (43322818364287 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12253 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12253]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12253])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12253) (a := (82255364563867 / 100000000000000 : ℝ)) (b := (42045753161 / 25000000000000 : ℝ)) (q := (577784641987 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12253])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12253])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12253]

theorem cert12253_54 : CellCertificate 12253 (56225987104451 / 625000000000000 : ℝ) (1714247991765521 / 1000000000000000000 : ℝ) (43322818364287 / 1250000000000000 : ℝ)
    (cell12253 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · have h := gap_lower (n := 12253) (a := (5138845521679 / 6250000000000 : ℝ)) (b := (42045753161 / 25000000000000 : ℝ)) (q := (231114256771 / 10000000000000 : ℝ))
      (E := (cell12253 ⟨54, by decide⟩).energy) (xi := (43322818364287 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12253 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12253]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12253])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12253) (a := (5138845521679 / 6250000000000 : ℝ)) (b := (42045753161 / 25000000000000 : ℝ)) (q := (231114256771 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12253])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12253])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12253]

theorem cert12253_55 : CellCertificate 12253 (56225987104451 / 625000000000000 : ℝ) (1714247991765521 / 1000000000000000000 : ℝ) (43322818364287 / 1250000000000000 : ℝ)
    (cell12253 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · have h := gap_lower (n := 12253) (a := (20546928888977 / 25000000000000 : ℝ)) (b := (42045753161 / 25000000000000 : ℝ)) (q := (577786632913 / 25000000000000 : ℝ))
      (E := (cell12253 ⟨55, by decide⟩).energy) (xi := (43322818364287 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12253 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12253]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12253])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12253) (a := (20546928888977 / 25000000000000 : ℝ)) (b := (42045753161 / 25000000000000 : ℝ)) (q := (577786632913 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12253])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12253])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12253]

theorem cert12253_56 : CellCertificate 12253 (56225987104451 / 625000000000000 : ℝ) (1714247991765521 / 1000000000000000000 : ℝ) (43322818364287 / 1250000000000000 : ℝ)
    (cell12253 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · have h := gap_lower (n := 12253) (a := (41076963081433 / 50000000000000 : ℝ)) (b := (42045753161 / 25000000000000 : ℝ)) (q := (2311150515937 / 100000000000000 : ℝ))
      (E := (cell12253 ⟨56, by decide⟩).energy) (xi := (43322818364287 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12253 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12253]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12253])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12253) (a := (41076963081433 / 50000000000000 : ℝ)) (b := (42045753161 / 25000000000000 : ℝ)) (q := (2311150515937 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12253])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12253])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12253]

theorem cert12253_57 : CellCertificate 12253 (56225987104451 / 625000000000000 : ℝ) (1714247991765521 / 1000000000000000000 : ℝ) (43322818364287 / 1250000000000000 : ℝ)
    (cell12253 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · have h := gap_lower (n := 12253) (a := (16424032027949 / 20000000000000 : ℝ)) (b := (42045753161 / 25000000000000 : ℝ)) (q := (1155577258757 / 50000000000000 : ℝ))
      (E := (cell12253 ⟨57, by decide⟩).energy) (xi := (43322818364287 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12253 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12253]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12253])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12253) (a := (16424032027949 / 20000000000000 : ℝ)) (b := (42045753161 / 25000000000000 : ℝ)) (q := (1155577258757 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12253])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12253])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12253]

theorem cert12253_58 : CellCertificate 12253 (56225987104451 / 625000000000000 : ℝ) (1714247991765521 / 1000000000000000000 : ℝ) (43322818364287 / 1250000000000000 : ℝ)
    (cell12253 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · have h := gap_lower (n := 12253) (a := (82086417458693 / 100000000000000 : ℝ)) (b := (42045753161 / 25000000000000 : ℝ)) (q := (451398151 / 19531250000 : ℝ))
      (E := (cell12253 ⟨58, by decide⟩).energy) (xi := (43322818364287 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12253 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12253]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12253])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12253) (a := (82086417458693 / 100000000000000 : ℝ)) (b := (42045753161 / 25000000000000 : ℝ)) (q := (451398151 / 19531250000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12253])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12253])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12253]

theorem cert12253_59 : CellCertificate 12253 (56225987104451 / 625000000000000 : ℝ) (1714247991765521 / 1000000000000000000 : ℝ) (43322818364287 / 1250000000000000 : ℝ)
    (cell12253 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · have h := gap_lower (n := 12253) (a := (41026349045999 / 50000000000000 : ℝ)) (b := (42045753161 / 25000000000000 : ℝ)) (q := (462232500027 / 20000000000000 : ℝ))
      (E := (cell12253 ⟨59, by decide⟩).energy) (xi := (43322818364287 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12253 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12253]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12253])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12253) (a := (41026349045999 / 50000000000000 : ℝ)) (b := (42045753161 / 25000000000000 : ℝ)) (q := (462232500027 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12253])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12253])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12253]

theorem cert12254_40 : CellCertificate 12254 (899585865690631 / 10000000000000000 : ℝ) (428527012791019 / 250000000000000000 : ℝ) (86638376519929 / 2500000000000000 : ℝ)
    (cell12254 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · have h := gap_lower (n := 12254) (a := (82697377130093 / 100000000000000 : ℝ)) (b := (168169104079 / 100000000000000 : ℝ)) (q := (462187928149 / 20000000000000 : ℝ))
      (E := (cell12254 ⟨40, by decide⟩).energy) (xi := (86638376519929 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12254 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12254]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12254])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12254) (a := (82697377130093 / 100000000000000 : ℝ)) (b := (168169104079 / 100000000000000 : ℝ)) (q := (462187928149 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12254])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12254])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12254]

theorem cert12254_41 : CellCertificate 12254 (899585865690631 / 10000000000000000 : ℝ) (428527012791019 / 250000000000000000 : ℝ) (86638376519929 / 2500000000000000 : ℝ)
    (cell12254 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · have h := gap_lower (n := 12254) (a := (82663234068557 / 100000000000000 : ℝ)) (b := (168169104079 / 100000000000000 : ℝ)) (q := (2310943670753 / 100000000000000 : ℝ))
      (E := (cell12254 ⟨41, by decide⟩).energy) (xi := (86638376519929 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12254 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12254]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12254])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12254) (a := (82663234068557 / 100000000000000 : ℝ)) (b := (168169104079 / 100000000000000 : ℝ)) (q := (2310943670753 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12254])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12254])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12254]

theorem cert12254_42 : CellCertificate 12254 (899585865690631 / 10000000000000000 : ℝ) (428527012791019 / 250000000000000000 : ℝ) (86638376519929 / 2500000000000000 : ℝ)
    (cell12254 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · have h := gap_lower (n := 12254) (a := (82629114811559 / 100000000000000 : ℝ)) (b := (168169104079 / 100000000000000 : ℝ)) (q := (2310947625147 / 100000000000000 : ℝ))
      (E := (cell12254 ⟨42, by decide⟩).energy) (xi := (86638376519929 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12254 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12254]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12254])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12254) (a := (82629114811559 / 100000000000000 : ℝ)) (b := (168169104079 / 100000000000000 : ℝ)) (q := (2310947625147 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12254])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12254])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12254]

theorem cert12254_43 : CellCertificate 12254 (899585865690631 / 10000000000000000 : ℝ) (428527012791019 / 250000000000000000 : ℝ) (86638376519929 / 2500000000000000 : ℝ)
    (cell12254 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · have h := gap_lower (n := 12254) (a := (41297509664529 / 50000000000000 : ℝ)) (b := (168169104079 / 100000000000000 : ℝ)) (q := (288868952661 / 12500000000000 : ℝ))
      (E := (cell12254 ⟨43, by decide⟩).energy) (xi := (86638376519929 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12254 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12254]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12254])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12254) (a := (41297509664529 / 50000000000000 : ℝ)) (b := (168169104079 / 100000000000000 : ℝ)) (q := (288868952661 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12254])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12254])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12254]

theorem cert12254_44 : CellCertificate 12254 (899585865690631 / 10000000000000000 : ℝ) (428527012791019 / 250000000000000000 : ℝ) (86638376519929 / 2500000000000000 : ℝ)
    (cell12254 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · have h := gap_lower (n := 12254) (a := (16512189518233 / 20000000000000 : ℝ)) (b := (168169104079 / 100000000000000 : ℝ)) (q := (2310955658911 / 100000000000000 : ℝ))
      (E := (cell12254 ⟨44, by decide⟩).energy) (xi := (86638376519929 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12254 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12254]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12254])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12254) (a := (16512189518233 / 20000000000000 : ℝ)) (b := (168169104079 / 100000000000000 : ℝ)) (q := (2310955658911 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12254])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12254])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12254]

theorem cert12254_45 : CellCertificate 12254 (899585865690631 / 10000000000000000 : ℝ) (428527012791019 / 250000000000000000 : ℝ) (86638376519929 / 2500000000000000 : ℝ)
    (cell12254 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · have h := gap_lower (n := 12254) (a := (82526899568143 / 100000000000000 : ℝ)) (b := (168169104079 / 100000000000000 : ℝ)) (q := (2310959619893 / 100000000000000 : ℝ))
      (E := (cell12254 ⟨45, by decide⟩).energy) (xi := (86638376519929 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12254 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12254]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12254])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12254) (a := (82526899568143 / 100000000000000 : ℝ)) (b := (168169104079 / 100000000000000 : ℝ)) (q := (2310959619893 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12254])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12254])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12254]

theorem cert12254_46 : CellCertificate 12254 (899585865690631 / 10000000000000000 : ℝ) (428527012791019 / 250000000000000000 : ℝ) (86638376519929 / 2500000000000000 : ℝ)
    (cell12254 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · have h := gap_lower (n := 12254) (a := (20623218807601 / 25000000000000 : ℝ)) (b := (168169104079 / 100000000000000 : ℝ)) (q := (1155481810539 / 50000000000000 : ℝ))
      (E := (cell12254 ⟨46, by decide⟩).energy) (xi := (86638376519929 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12254 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12254]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12254])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12254) (a := (20623218807601 / 25000000000000 : ℝ)) (b := (168169104079 / 100000000000000 : ℝ)) (q := (1155481810539 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12254])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12254])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12254]

theorem cert12254_47 : CellCertificate 12254 (899585865690631 / 10000000000000000 : ℝ) (428527012791019 / 250000000000000000 : ℝ) (86638376519929 / 2500000000000000 : ℝ)
    (cell12254 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · have h := gap_lower (n := 12254) (a := (82458874548511 / 100000000000000 : ℝ)) (b := (168169104079 / 100000000000000 : ℝ)) (q := (2310967602677 / 100000000000000 : ℝ))
      (E := (cell12254 ⟨47, by decide⟩).energy) (xi := (86638376519929 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12254 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12254]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12254])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12254) (a := (82458874548511 / 100000000000000 : ℝ)) (b := (168169104079 / 100000000000000 : ℝ)) (q := (2310967602677 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12254])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12254])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12254]

theorem cert12254_48 : CellCertificate 12254 (899585865690631 / 10000000000000000 : ℝ) (428527012791019 / 250000000000000000 : ℝ) (86638376519929 / 2500000000000000 : ℝ)
    (cell12254 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · have h := gap_lower (n := 12254) (a := (82424897493173 / 100000000000000 : ℝ)) (b := (168169104079 / 100000000000000 : ℝ)) (q := (18487772979 / 800000000000 : ℝ))
      (E := (cell12254 ⟨48, by decide⟩).energy) (xi := (86638376519929 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12254 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12254]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12254])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12254) (a := (82424897493173 / 100000000000000 : ℝ)) (b := (168169104079 / 100000000000000 : ℝ)) (q := (18487772979 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12254])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12254])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12254]

theorem cert12254_49 : CellCertificate 12254 (899585865690631 / 10000000000000000 : ℝ) (428527012791019 / 250000000000000000 : ℝ) (86638376519929 / 2500000000000000 : ℝ)
    (cell12254 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · have h := gap_lower (n := 12254) (a := (329563776141 / 400000000000 : ℝ)) (b := (168169104079 / 100000000000000 : ℝ)) (q := (2310975619903 / 100000000000000 : ℝ))
      (E := (cell12254 ⟨49, by decide⟩).energy) (xi := (86638376519929 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12254 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12254]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12254])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12254) (a := (329563776141 / 400000000000 : ℝ)) (b := (168169104079 / 100000000000000 : ℝ)) (q := (2310975619903 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12254])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12254])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12254]

theorem cert12254_50 : CellCertificate 12254 (899585865690631 / 10000000000000000 : ℝ) (428527012791019 / 250000000000000000 : ℝ) (86638376519929 / 2500000000000000 : ℝ)
    (cell12254 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · have h := gap_lower (n := 12254) (a := (5147313384109 / 6250000000000 : ℝ)) (b := (168169104079 / 100000000000000 : ℝ)) (q := (288872449203 / 12500000000000 : ℝ))
      (E := (cell12254 ⟨50, by decide⟩).energy) (xi := (86638376519929 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12254 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12254]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12254])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12254) (a := (5147313384109 / 6250000000000 : ℝ)) (b := (168169104079 / 100000000000000 : ℝ)) (q := (288872449203 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12254])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12254])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12254]

theorem cert12254_51 : CellCertificate 12254 (899585865690631 / 10000000000000000 : ℝ) (428527012791019 / 250000000000000000 : ℝ) (86638376519929 / 2500000000000000 : ℝ)
    (cell12254 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · have h := gap_lower (n := 12254) (a := (82323107795809 / 100000000000000 : ℝ)) (b := (168169104079 / 100000000000000 : ℝ)) (q := (2310983600643 / 100000000000000 : ℝ))
      (E := (cell12254 ⟨51, by decide⟩).energy) (xi := (86638376519929 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12254 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12254]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12254])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12254) (a := (82323107795809 / 100000000000000 : ℝ)) (b := (168169104079 / 100000000000000 : ℝ)) (q := (2310983600643 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12254])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12254])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12254]

theorem cert12254_52 : CellCertificate 12254 (899585865690631 / 10000000000000000 : ℝ) (428527012791019 / 250000000000000000 : ℝ) (86638376519929 / 2500000000000000 : ℝ)
    (cell12254 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · have h := gap_lower (n := 12254) (a := (41144612478369 / 50000000000000 : ℝ)) (b := (168169104079 / 100000000000000 : ℝ)) (q := (2310987579981 / 100000000000000 : ℝ))
      (E := (cell12254 ⟨52, by decide⟩).energy) (xi := (86638376519929 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12254 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12254]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12254])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12254) (a := (41144612478369 / 50000000000000 : ℝ)) (b := (168169104079 / 100000000000000 : ℝ)) (q := (2310987579981 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12254])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12254])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12254]

theorem cert12254_53 : CellCertificate 12254 (899585865690631 / 10000000000000000 : ℝ) (428527012791019 / 250000000000000000 : ℝ) (86638376519929 / 2500000000000000 : ℝ)
    (cell12254 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · have h := gap_lower (n := 12254) (a := (20563841399993 / 25000000000000 : ℝ)) (b := (168169104079 / 100000000000000 : ℝ)) (q := (577747897091 / 25000000000000 : ℝ))
      (E := (cell12254 ⟨53, by decide⟩).energy) (xi := (86638376519929 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12254 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12254]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12254])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12254) (a := (20563841399993 / 25000000000000 : ℝ)) (b := (168169104079 / 100000000000000 : ℝ)) (q := (577747897091 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12254])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12254])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12254]

theorem cert12254_54 : CellCertificate 12254 (899585865690631 / 10000000000000000 : ℝ) (428527012791019 / 250000000000000000 : ℝ) (86638376519929 / 2500000000000000 : ℝ)
    (cell12254 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · have h := gap_lower (n := 12254) (a := (16444305939419 / 20000000000000 : ℝ)) (b := (168169104079 / 100000000000000 : ℝ)) (q := (231099562337 / 10000000000000 : ℝ))
      (E := (cell12254 ⟨54, by decide⟩).energy) (xi := (86638376519929 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12254 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12254]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12254])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12254) (a := (16444305939419 / 20000000000000 : ℝ)) (b := (168169104079 / 100000000000000 : ℝ)) (q := (231099562337 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12254])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12254])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12254]

theorem cert12254_55 : CellCertificate 12254 (899585865690631 / 10000000000000000 : ℝ) (428527012791019 / 250000000000000000 : ℝ) (86638376519929 / 2500000000000000 : ℝ)
    (cell12254 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · have h := gap_lower (n := 12254) (a := (10273464652479 / 12500000000000 : ℝ)) (b := (168169104079 / 100000000000000 : ℝ)) (q := (72218736383 / 3125000000000 : ℝ))
      (E := (cell12254 ⟨55, by decide⟩).energy) (xi := (86638376519929 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12254 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12254]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12254])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12254) (a := (10273464652479 / 12500000000000 : ℝ)) (b := (168169104079 / 100000000000000 : ℝ)) (q := (72218736383 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12254])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12254])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12254]

theorem cert12254_56 : CellCertificate 12254 (899585865690631 / 10000000000000000 : ℝ) (428527012791019 / 250000000000000000 : ℝ) (86638376519929 / 2500000000000000 : ℝ)
    (cell12254 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · have h := gap_lower (n := 12254) (a := (1643078562801 / 2000000000000 : ℝ)) (b := (168169104079 / 100000000000000 : ℝ)) (q := (1155501792637 / 50000000000000 : ℝ))
      (E := (cell12254 ⟨56, by decide⟩).energy) (xi := (86638376519929 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12254 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12254]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12254])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12254) (a := (1643078562801 / 2000000000000 : ℝ)) (b := (168169104079 / 100000000000000 : ℝ)) (q := (1155501792637 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12254])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12254])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12254]

theorem cert12254_57 : CellCertificate 12254 (899585865690631 / 10000000000000000 : ℝ) (428527012791019 / 250000000000000000 : ℝ) (86638376519929 / 2500000000000000 : ℝ)
    (cell12254 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · have h := gap_lower (n := 12254) (a := (41060081214879 / 50000000000000 : ℝ)) (b := (168169104079 / 100000000000000 : ℝ)) (q := (577751891309 / 25000000000000 : ℝ))
      (E := (cell12254 ⟨57, by decide⟩).energy) (xi := (86638376519929 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12254 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12254]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12254])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12254) (a := (41060081214879 / 50000000000000 : ℝ)) (b := (168169104079 / 100000000000000 : ℝ)) (q := (577751891309 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12254])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12254])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12254]

theorem cert12254_58 : CellCertificate 12254 (899585865690631 / 10000000000000000 : ℝ) (428527012791019 / 250000000000000000 : ℝ) (86638376519929 / 2500000000000000 : ℝ)
    (cell12254 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · have h := gap_lower (n := 12254) (a := (16417284012221 / 20000000000000 : ℝ)) (b := (168169104079 / 100000000000000 : ℝ)) (q := (2311011559933 / 100000000000000 : ℝ))
      (E := (cell12254 ⟨58, by decide⟩).energy) (xi := (86638376519929 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12254 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12254]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12254])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12254) (a := (16417284012221 / 20000000000000 : ℝ)) (b := (168169104079 / 100000000000000 : ℝ)) (q := (2311011559933 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12254])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12254])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12254]

theorem cert12254_59 : CellCertificate 12254 (899585865690631 / 10000000000000000 : ℝ) (428527012791019 / 250000000000000000 : ℝ) (86638376519929 / 2500000000000000 : ℝ)
    (cell12254 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · have h := gap_lower (n := 12254) (a := (41026350503189 / 50000000000000 : ℝ)) (b := (168169104079 / 100000000000000 : ℝ)) (q := (462203113179 / 20000000000000 : ℝ))
      (E := (cell12254 ⟨59, by decide⟩).energy) (xi := (86638376519929 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12254 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12254]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12254])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12254) (a := (41026350503189 / 50000000000000 : ℝ)) (b := (168169104079 / 100000000000000 : ℝ)) (q := (462203113179 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12254])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12254])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12254]

theorem cert12255_40 : CellCertificate 12255 (112444492802051 / 1250000000000000 : ℝ) (342793626681707 / 200000000000000000 : ℝ) (173262235118177 / 5000000000000000 : ℝ)
    (cell12255 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · have h := gap_lower (n := 12255) (a := (82697374043821 / 100000000000000 : ℝ)) (b := (42038799461 / 25000000000000 : ℝ)) (q := (1155396398399 / 50000000000000 : ℝ))
      (E := (cell12255 ⟨40, by decide⟩).energy) (xi := (173262235118177 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12255 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12255]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12255])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12255) (a := (82697374043821 / 100000000000000 : ℝ)) (b := (42038799461 / 25000000000000 : ℝ)) (q := (1155396398399 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12255])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12255])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12255]

theorem cert12255_41 : CellCertificate 12255 (112444492802051 / 1250000000000000 : ℝ) (342793626681707 / 200000000000000000 : ℝ) (173262235118177 / 5000000000000000 : ℝ)
    (cell12255 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · have h := gap_lower (n := 12255) (a := (20665807825517 / 25000000000000 : ℝ)) (b := (42038799461 / 25000000000000 : ℝ)) (q := (1155398396841 / 50000000000000 : ℝ))
      (E := (cell12255 ⟨41, by decide⟩).energy) (xi := (173262235118177 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12255 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12255]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12255])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12255) (a := (20665807825517 / 25000000000000 : ℝ)) (b := (42038799461 / 25000000000000 : ℝ)) (q := (1155398396841 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12255])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12255])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12255]

theorem cert12255_42 : CellCertificate 12255 (112444492802051 / 1250000000000000 : ℝ) (342793626681707 / 200000000000000000 : ℝ) (173262235118177 / 5000000000000000 : ℝ)
    (cell12255 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · have h := gap_lower (n := 12255) (a := (8262911236441 / 10000000000000 : ℝ)) (b := (42038799461 / 25000000000000 : ℝ)) (q := (115540038721 / 5000000000000 : ℝ))
      (E := (cell12255 ⟨42, by decide⟩).energy) (xi := (173262235118177 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12255 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12255]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12255])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12255) (a := (8262911236441 / 10000000000000 : ℝ)) (b := (42038799461 / 25000000000000 : ℝ)) (q := (115540038721 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12255])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12255])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12255]

theorem cert12255_43 : CellCertificate 12255 (112444492802051 / 1250000000000000 : ℝ) (342793626681707 / 200000000000000000 : ℝ) (173262235118177 / 5000000000000000 : ℝ)
    (cell12255 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · have h := gap_lower (n := 12255) (a := (82595017200807 / 100000000000000 : ℝ)) (b := (42038799461 / 25000000000000 : ℝ)) (q := (2310804797669 / 100000000000000 : ℝ))
      (E := (cell12255 ⟨43, by decide⟩).energy) (xi := (173262235118177 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12255 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12255]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12255])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12255) (a := (82595017200807 / 100000000000000 : ℝ)) (b := (42038799461 / 25000000000000 : ℝ)) (q := (2310804797669 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12255])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12255])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12255]

theorem cert12255_44 : CellCertificate 12255 (112444492802051 / 1250000000000000 : ℝ) (342793626681707 / 200000000000000000 : ℝ) (173262235118177 / 5000000000000000 : ℝ)
    (cell12255 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · have h := gap_lower (n := 12255) (a := (82560945781371 / 100000000000000 : ℝ)) (b := (42038799461 / 25000000000000 : ℝ)) (q := (577702186393 / 25000000000000 : ℝ))
      (E := (cell12255 ⟨44, by decide⟩).energy) (xi := (173262235118177 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12255 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12255]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12255])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12255) (a := (82560945781371 / 100000000000000 : ℝ)) (b := (42038799461 / 25000000000000 : ℝ)) (q := (577702186393 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12255])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12255])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12255]

theorem cert12255_45 : CellCertificate 12255 (112444492802051 / 1250000000000000 : ℝ) (342793626681707 / 200000000000000000 : ℝ) (173262235118177 / 5000000000000000 : ℝ)
    (cell12255 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · have h := gap_lower (n := 12255) (a := (16505379615273 / 20000000000000 : ℝ)) (b := (42038799461 / 25000000000000 : ℝ)) (q := (2310812735143 / 100000000000000 : ℝ))
      (E := (cell12255 ⟨45, by decide⟩).energy) (xi := (173262235118177 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12255 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12255]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12255])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12255) (a := (16505379615273 / 20000000000000 : ℝ)) (b := (42038799461 / 25000000000000 : ℝ)) (q := (2310812735143 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12255])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12255])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12255]

theorem cert12255_46 : CellCertificate 12255 (112444492802051 / 1250000000000000 : ℝ) (342793626681707 / 200000000000000000 : ℝ) (173262235118177 / 5000000000000000 : ℝ)
    (cell12255 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · have h := gap_lower (n := 12255) (a := (82492874056203 / 100000000000000 : ℝ)) (b := (42038799461 / 25000000000000 : ℝ)) (q := (1155408382839 / 50000000000000 : ℝ))
      (E := (cell12255 ⟨46, by decide⟩).energy) (xi := (173262235118177 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12255 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12255]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12255])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12255) (a := (82492874056203 / 100000000000000 : ℝ)) (b := (42038799461 / 25000000000000 : ℝ)) (q := (1155408382839 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12255])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12255])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12255]

theorem cert12255_47 : CellCertificate 12255 (112444492802051 / 1250000000000000 : ℝ) (342793626681707 / 200000000000000000 : ℝ) (173262235118177 / 5000000000000000 : ℝ)
    (cell12255 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · have h := gap_lower (n := 12255) (a := (82458873691447 / 100000000000000 : ℝ)) (b := (42038799461 / 25000000000000 : ℝ)) (q := (2310820777391 / 100000000000000 : ℝ))
      (E := (cell12255 ⟨47, by decide⟩).energy) (xi := (173262235118177 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12255 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12255]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12255])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12255) (a := (82458873691447 / 100000000000000 : ℝ)) (b := (42038799461 / 25000000000000 : ℝ)) (q := (2310820777391 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12255])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12255])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12255]

theorem cert12255_48 : CellCertificate 12255 (112444492802051 / 1250000000000000 : ℝ) (342793626681707 / 200000000000000000 : ℝ) (173262235118177 / 5000000000000000 : ℝ)
    (cell12255 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · have h := gap_lower (n := 12255) (a := (10303112119101 / 12500000000000 : ℝ)) (b := (42038799461 / 25000000000000 : ℝ)) (q := (1155412384537 / 50000000000000 : ℝ))
      (E := (cell12255 ⟨48, by decide⟩).energy) (xi := (173262235118177 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12255 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12255]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12255])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12255) (a := (10303112119101 / 12500000000000 : ℝ)) (b := (42038799461 / 25000000000000 : ℝ)) (q := (1155412384537 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12255])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12255])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12255]

theorem cert12255_49 : CellCertificate 12255 (112444492802051 / 1250000000000000 : ℝ) (342793626681707 / 200000000000000000 : ℝ) (173262235118177 / 5000000000000000 : ℝ)
    (cell12255 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · have h := gap_lower (n := 12255) (a := (41195471905573 / 50000000000000 : ℝ)) (b := (42038799461 / 25000000000000 : ℝ)) (q := (23108287393 / 1000000000000 : ℝ))
      (E := (cell12255 ⟨49, by decide⟩).energy) (xi := (173262235118177 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12255 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12255]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12255])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12255) (a := (41195471905573 / 50000000000000 : ℝ)) (b := (42038799461 / 25000000000000 : ℝ)) (q := (23108287393 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12255])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12255])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12255]

theorem cert12255_50 : CellCertificate 12255 (112444492802051 / 1250000000000000 : ℝ) (342793626681707 / 200000000000000000 : ℝ) (173262235118177 / 5000000000000000 : ℝ)
    (cell12255 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · have h := gap_lower (n := 12255) (a := (41178507118733 / 50000000000000 : ℝ)) (b := (42038799461 / 25000000000000 : ℝ)) (q := (2310832745367 / 100000000000000 : ℝ))
      (E := (cell12255 ⟨50, by decide⟩).energy) (xi := (173262235118177 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12255 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12255]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12255])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12255) (a := (41178507118733 / 50000000000000 : ℝ)) (b := (42038799461 / 25000000000000 : ℝ)) (q := (2310832745367 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12255])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12255])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12255]

theorem cert12255_51 : CellCertificate 12255 (112444492802051 / 1250000000000000 : ℝ) (342793626681707 / 200000000000000000 : ℝ) (173262235118177 / 5000000000000000 : ℝ)
    (cell12255 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · have h := gap_lower (n := 12255) (a := (2058077705073 / 2500000000000 : ℝ)) (b := (42038799461 / 25000000000000 : ℝ)) (q := (577709181633 / 25000000000000 : ℝ))
      (E := (cell12255 ⟨51, by decide⟩).energy) (xi := (173262235118177 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12255 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12255]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12255])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12255) (a := (2058077705073 / 2500000000000 : ℝ)) (b := (42038799461 / 25000000000000 : ℝ)) (q := (577709181633 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12255])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12255])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12255]

theorem cert12255_52 : CellCertificate 12255 (112444492802051 / 1250000000000000 : ℝ) (342793626681707 / 200000000000000000 : ℝ) (173262235118177 / 5000000000000000 : ℝ)
    (cell12255 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · have h := gap_lower (n := 12255) (a := (82289225678803 / 100000000000000 : ℝ)) (b := (42038799461 / 25000000000000 : ℝ)) (q := (2310840739711 / 100000000000000 : ℝ))
      (E := (cell12255 ⟨52, by decide⟩).energy) (xi := (173262235118177 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12255 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12255]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12255])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12255) (a := (82289225678803 / 100000000000000 : ℝ)) (b := (42038799461 / 25000000000000 : ℝ)) (q := (2310840739711 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12255])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12255])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12255]

theorem cert12255_53 : CellCertificate 12255 (112444492802051 / 1250000000000000 : ℝ) (342793626681707 / 200000000000000000 : ℝ) (173262235118177 / 5000000000000000 : ℝ)
    (cell12255 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · have h := gap_lower (n := 12255) (a := (41127683318279 / 50000000000000 : ℝ)) (b := (42038799461 / 25000000000000 : ℝ)) (q := (2310844723683 / 100000000000000 : ℝ))
      (E := (cell12255 ⟨53, by decide⟩).energy) (xi := (173262235118177 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12255 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12255]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12255])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12255) (a := (41127683318279 / 50000000000000 : ℝ)) (b := (42038799461 / 25000000000000 : ℝ)) (q := (2310844723683 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12255])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12255])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12255]

theorem cert12255_54 : CellCertificate 12255 (112444492802051 / 1250000000000000 : ℝ) (342793626681707 / 200000000000000000 : ℝ) (173262235118177 / 5000000000000000 : ℝ)
    (cell12255 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · have h := gap_lower (n := 12255) (a := (41110765523883 / 50000000000000 : ℝ)) (b := (42038799461 / 25000000000000 : ℝ)) (q := (231084873499 / 10000000000000 : ℝ))
      (E := (cell12255 ⟨54, by decide⟩).energy) (xi := (173262235118177 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12255 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12255]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12255])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12255) (a := (41110765523883 / 50000000000000 : ℝ)) (b := (42038799461 / 25000000000000 : ℝ)) (q := (231084873499 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12255])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12255])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12255]

theorem cert12255_55 : CellCertificate 12255 (112444492802051 / 1250000000000000 : ℝ) (342793626681707 / 200000000000000000 : ℝ) (173262235118177 / 5000000000000000 : ℝ)
    (cell12255 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · have h := gap_lower (n := 12255) (a := (20546929721039 / 25000000000000 : ℝ)) (b := (42038799461 / 25000000000000 : ℝ)) (q := (2310852711941 / 100000000000000 : ℝ))
      (E := (cell12255 ⟨55, by decide⟩).energy) (xi := (173262235118177 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12255 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12255]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12255])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12255) (a := (20546929721039 / 25000000000000 : ℝ)) (b := (42038799461 / 25000000000000 : ℝ)) (q := (2310852711941 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12255])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12255])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12255]

theorem cert12255_56 : CellCertificate 12255 (112444492802051 / 1250000000000000 : ℝ) (342793626681707 / 200000000000000000 : ℝ) (173262235118177 / 5000000000000000 : ℝ)
    (cell12255 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · have h := gap_lower (n := 12255) (a := (20538482529399 / 25000000000000 : ℝ)) (b := (42038799461 / 25000000000000 : ℝ)) (q := (23108567107 / 1000000000000 : ℝ))
      (E := (cell12255 ⟨56, by decide⟩).energy) (xi := (173262235118177 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12255 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12255]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12255])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12255) (a := (20538482529399 / 25000000000000 : ℝ)) (b := (42038799461 / 25000000000000 : ℝ)) (q := (23108567107 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12255])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12255])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12255]

theorem cert12255_57 : CellCertificate 12255 (112444492802051 / 1250000000000000 : ℝ) (342793626681707 / 200000000000000000 : ℝ) (173262235118177 / 5000000000000000 : ℝ)
    (cell12255 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · have h := gap_lower (n := 12255) (a := (41060082360047 / 50000000000000 : ℝ)) (b := (42038799461 / 25000000000000 : ℝ)) (q := (577715182053 / 25000000000000 : ℝ))
      (E := (cell12255 ⟨57, by decide⟩).energy) (xi := (173262235118177 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12255 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12255]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12255])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12255) (a := (41060082360047 / 50000000000000 : ℝ)) (b := (42038799461 / 25000000000000 : ℝ)) (q := (577715182053 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12255])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12255])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12255]

theorem cert12255_58 : CellCertificate 12255 (112444492802051 / 1250000000000000 : ℝ) (342793626681707 / 200000000000000000 : ℝ) (173262235118177 / 5000000000000000 : ℝ)
    (cell12255 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · have h := gap_lower (n := 12255) (a := (410432113319 / 500000000000 : ℝ)) (b := (42038799461 / 25000000000000 : ℝ)) (q := (288858087761 / 12500000000000 : ℝ))
      (E := (cell12255 ⟨58, by decide⟩).energy) (xi := (173262235118177 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12255 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12255]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12255])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12255) (a := (410432113319 / 500000000000 : ℝ)) (b := (42038799461 / 25000000000000 : ℝ)) (q := (288858087761 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12255])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12255])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12255]

theorem cert12255_59 : CellCertificate 12255 (112444492802051 / 1250000000000000 : ℝ) (342793626681707 / 200000000000000000 : ℝ) (173262235118177 / 5000000000000000 : ℝ)
    (cell12255 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · have h := gap_lower (n := 12255) (a := (41026351960501 / 50000000000000 : ℝ)) (b := (42038799461 / 25000000000000 : ℝ)) (q := (36107323249 / 1562500000000 : ℝ))
      (E := (cell12255 ⟨59, by decide⟩).energy) (xi := (173262235118177 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12255 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12255]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12255])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12255) (a := (41026351960501 / 50000000000000 : ℝ)) (b := (42038799461 / 25000000000000 : ℝ)) (q := (36107323249 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12255])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12255])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12255]

theorem cert12256_40 : CellCertificate 12256 (179905204769477 / 2000000000000000 : ℝ) (1713828238493301 / 1000000000000000000 : ℝ) (346495439382749 / 10000000000000000 : ℝ)
    (cell12256 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · have h := gap_lower (n := 12256) (a := (82697370958547 / 100000000000000 : ℝ)) (b := (8407064697 / 5000000000000 : ℝ)) (q := (577661501977 / 25000000000000 : ℝ))
      (E := (cell12256 ⟨40, by decide⟩).energy) (xi := (346495439382749 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12256 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12256]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12256])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12256) (a := (82697370958547 / 100000000000000 : ℝ)) (b := (8407064697 / 5000000000000 : ℝ)) (q := (577661501977 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12256])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12256])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12256]

theorem cert12256_41 : CellCertificate 12256 (179905204769477 / 2000000000000000 : ℝ) (1713828238493301 / 1000000000000000000 : ℝ) (346495439382749 / 10000000000000000 : ℝ)
    (cell12256 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · have h := gap_lower (n := 12256) (a := (82663228536537 / 100000000000000 : ℝ)) (b := (8407064697 / 5000000000000 : ℝ)) (q := (1155325015229 / 50000000000000 : ℝ))
      (E := (cell12256 ⟨41, by decide⟩).energy) (xi := (346495439382749 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12256 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12256]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12256])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12256) (a := (82663228536537 / 100000000000000 : ℝ)) (b := (8407064697 / 5000000000000 : ℝ)) (q := (1155325015229 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12256])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12256])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12256]

theorem cert12256_42 : CellCertificate 12256 (179905204769477 / 2000000000000000 : ℝ) (1713828238493301 / 1000000000000000000 : ℝ) (346495439382749 / 10000000000000000 : ℝ)
    (cell12256 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · have h := gap_lower (n := 12256) (a := (82629109918179 / 100000000000000 : ℝ)) (b := (8407064697 / 5000000000000 : ℝ)) (q := (2310653978879 / 100000000000000 : ℝ))
      (E := (cell12256 ⟨42, by decide⟩).energy) (xi := (346495439382749 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12256 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12256]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12256])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12256) (a := (82629109918179 / 100000000000000 : ℝ)) (b := (8407064697 / 5000000000000 : ℝ)) (q := (2310653978879 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12256])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12256])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12256]

theorem cert12256_43 : CellCertificate 12256 (179905204769477 / 2000000000000000 : ℝ) (1713828238493301 / 1000000000000000000 : ℝ) (346495439382749 / 10000000000000000 : ℝ)
    (cell12256 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · have h := gap_lower (n := 12256) (a := (41297507536717 / 50000000000000 : ℝ)) (b := (8407064697 / 5000000000000 : ℝ)) (q := (2310657970529 / 100000000000000 : ℝ))
      (E := (cell12256 ⟨43, by decide⟩).energy) (xi := (346495439382749 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12256 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12256]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12256])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12256) (a := (41297507536717 / 50000000000000 : ℝ)) (b := (8407064697 / 5000000000000 : ℝ)) (q := (2310657970529 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12256])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12256])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12256]

theorem cert12256_44 : CellCertificate 12256 (179905204769477 / 2000000000000000 : ℝ) (1713828238493301 / 1000000000000000000 : ℝ) (346495439382749 / 10000000000000000 : ℝ)
    (cell12256 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · have h := gap_lower (n := 12256) (a := (41280471986207 / 50000000000000 : ℝ)) (b := (8407064697 / 5000000000000 : ℝ)) (q := (1155331002571 / 50000000000000 : ℝ))
      (E := (cell12256 ⟨44, by decide⟩).energy) (xi := (346495439382749 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12256 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12256]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12256])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12256) (a := (41280471986207 / 50000000000000 : ℝ)) (b := (8407064697 / 5000000000000 : ℝ)) (q := (1155331002571 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12256])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12256])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12256]

theorem cert12256_45 : CellCertificate 12256 (179905204769477 / 2000000000000000 : ℝ) (1713828238493301 / 1000000000000000000 : ℝ) (346495439382749 / 10000000000000000 : ℝ)
    (cell12256 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · have h := gap_lower (n := 12256) (a := (10315862073173 / 12500000000000 : ℝ)) (b := (8407064697 / 5000000000000 : ℝ)) (q := (1155332982297 / 50000000000000 : ℝ))
      (E := (cell12256 ⟨45, by decide⟩).energy) (xi := (346495439382749 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12256 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12256]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12256])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12256) (a := (10315862073173 / 12500000000000 : ℝ)) (b := (8407064697 / 5000000000000 : ℝ)) (q := (1155332982297 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12256])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12256])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12256]

theorem cert12256_46 : CellCertificate 12256 (179905204769477 / 2000000000000000 : ℝ) (1713828238493301 / 1000000000000000000 : ℝ) (346495439382749 / 10000000000000000 : ℝ)
    (cell12256 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · have h := gap_lower (n := 12256) (a := (41246436441379 / 50000000000000 : ℝ)) (b := (8407064697 / 5000000000000 : ℝ)) (q := (1155334982863 / 50000000000000 : ℝ))
      (E := (cell12256 ⟨46, by decide⟩).energy) (xi := (346495439382749 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12256 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12256]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12256])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12256) (a := (41246436441379 / 50000000000000 : ℝ)) (b := (8407064697 / 5000000000000 : ℝ)) (q := (1155334982863 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12256])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12256])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12256]

theorem cert12256_47 : CellCertificate 12256 (179905204769477 / 2000000000000000 : ℝ) (1713828238493301 / 1000000000000000000 : ℝ) (346495439382749 / 10000000000000000 : ℝ)
    (cell12256 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · have h := gap_lower (n := 12256) (a := (824588728351 / 1000000000000 : ℝ)) (b := (8407064697 / 5000000000000 : ℝ)) (q := (1848539159 / 80000000000 : ℝ))
      (E := (cell12256 ⟨47, by decide⟩).energy) (xi := (346495439382749 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12256 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12256]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12256])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12256) (a := (824588728351 / 1000000000000 : ℝ)) (b := (8407064697 / 5000000000000 : ℝ)) (q := (1848539159 / 80000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12256])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12256])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12256]

theorem cert12256_48 : CellCertificate 12256 (179905204769477 / 2000000000000000 : ℝ) (1713828238493301 / 1000000000000000000 : ℝ) (346495439382749 / 10000000000000000 : ℝ)
    (cell12256 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · have h := gap_lower (n := 12256) (a := (82424896413121 / 100000000000000 : ℝ)) (b := (8407064697 / 5000000000000 : ℝ)) (q := (2310677971347 / 100000000000000 : ℝ))
      (E := (cell12256 ⟨48, by decide⟩).energy) (xi := (346495439382749 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12256 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12256]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12256])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12256) (a := (82424896413121 / 100000000000000 : ℝ)) (b := (8407064697 / 5000000000000 : ℝ)) (q := (2310677971347 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12256])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12256])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12256]

theorem cert12256_49 : CellCertificate 12256 (179905204769477 / 2000000000000000 : ℝ) (1713828238493301 / 1000000000000000000 : ℝ) (346495439382749 / 10000000000000000 : ℝ)
    (cell12256 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · have h := gap_lower (n := 12256) (a := (82390943587681 / 100000000000000 : ℝ)) (b := (8407064697 / 5000000000000 : ℝ)) (q := (2310681973249 / 100000000000000 : ℝ))
      (E := (cell12256 ⟨49, by decide⟩).energy) (xi := (346495439382749 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12256 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12256]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12256])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12256) (a := (82390943587681 / 100000000000000 : ℝ)) (b := (8407064697 / 5000000000000 : ℝ)) (q := (2310681973249 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12256])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12256])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12256]

theorem cert12256_50 : CellCertificate 12256 (179905204769477 / 2000000000000000 : ℝ) (1713828238493301 / 1000000000000000000 : ℝ) (346495439382749 / 10000000000000000 : ℝ)
    (cell12256 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · have h := gap_lower (n := 12256) (a := (82357014329787 / 100000000000000 : ℝ)) (b := (8407064697 / 5000000000000 : ℝ)) (q := (1155342976407 / 50000000000000 : ℝ))
      (E := (cell12256 ⟨50, by decide⟩).energy) (xi := (346495439382749 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12256 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12256]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12256])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12256) (a := (82357014329787 / 100000000000000 : ℝ)) (b := (8407064697 / 5000000000000 : ℝ)) (q := (1155342976407 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12256])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12256])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12256]

theorem cert12256_51 : CellCertificate 12256 (179905204769477 / 2000000000000000 : ℝ) (1713828238493301 / 1000000000000000000 : ℝ) (346495439382749 / 10000000000000000 : ℝ)
    (cell12256 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · have h := gap_lower (n := 12256) (a := (8232310861059 / 10000000000000 : ℝ)) (b := (8407064697 / 5000000000000 : ℝ)) (q := (2310689967149 / 100000000000000 : ℝ))
      (E := (cell12256 ⟨51, by decide⟩).energy) (xi := (346495439382749 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12256 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12256]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12256])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12256) (a := (8232310861059 / 10000000000000 : ℝ)) (b := (8407064697 / 5000000000000 : ℝ)) (q := (2310689967149 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12256])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12256])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12256]

theorem cert12256_52 : CellCertificate 12256 (179905204769477 / 2000000000000000 : ℝ) (1713828238493301 / 1000000000000000000 : ℝ) (346495439382749 / 10000000000000000 : ℝ)
    (cell12256 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · have h := gap_lower (n := 12256) (a := (20572306600347 / 25000000000000 : ℝ)) (b := (8407064697 / 5000000000000 : ℝ)) (q := (288836744409 / 12500000000000 : ℝ))
      (E := (cell12256 ⟨52, by decide⟩).energy) (xi := (346495439382749 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12256 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12256]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12256])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12256) (a := (20572306600347 / 25000000000000 : ℝ)) (b := (8407064697 / 5000000000000 : ℝ)) (q := (288836744409 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12256])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12256])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12256]

theorem cert12256_53 : CellCertificate 12256 (179905204769477 / 2000000000000000 : ℝ) (1713828238493301 / 1000000000000000000 : ℝ) (346495439382749 / 10000000000000000 : ℝ)
    (cell12256 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · have h := gap_lower (n := 12256) (a := (82255367673623 / 100000000000000 : ℝ)) (b := (8407064697 / 5000000000000 : ℝ)) (q := (2310697973907 / 100000000000000 : ℝ))
      (E := (cell12256 ⟨53, by decide⟩).energy) (xi := (346495439382749 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12256 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12256]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12256])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12256) (a := (82255367673623 / 100000000000000 : ℝ)) (b := (8407064697 / 5000000000000 : ℝ)) (q := (2310697973907 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12256])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12256])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12256]

theorem cert12256_54 : CellCertificate 12256 (179905204769477 / 2000000000000000 : ℝ) (1713828238493301 / 1000000000000000000 : ℝ) (346495439382749 / 10000000000000000 : ℝ)
    (cell12256 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · have h := gap_lower (n := 12256) (a := (41110766199439 / 50000000000000 : ℝ)) (b := (8407064697 / 5000000000000 : ℝ)) (q := (1155350980801 / 50000000000000 : ℝ))
      (E := (cell12256 ⟨54, by decide⟩).energy) (xi := (346495439382749 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12256 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12256]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12256])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12256) (a := (41110766199439 / 50000000000000 : ℝ)) (b := (8407064697 / 5000000000000 : ℝ)) (q := (1155350980801 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12256])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12256])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12256]

theorem cert12256_55 : CellCertificate 12256 (179905204769477 / 2000000000000000 : ℝ) (1713828238493301 / 1000000000000000000 : ℝ) (346495439382749 / 10000000000000000 : ℝ)
    (cell12256 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · have h := gap_lower (n := 12256) (a := (41093860274441 / 50000000000000 : ℝ)) (b := (8407064697 / 5000000000000 : ℝ)) (q := (462141194941 / 20000000000000 : ℝ))
      (E := (cell12256 ⟨55, by decide⟩).energy) (xi := (346495439382749 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12256 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12256]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12256])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12256) (a := (41093860274441 / 50000000000000 : ℝ)) (b := (8407064697 / 5000000000000 : ℝ)) (q := (462141194941 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12256])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12256])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12256]

theorem cert12256_56 : CellCertificate 12256 (179905204769477 / 2000000000000000 : ℝ) (1713828238493301 / 1000000000000000000 : ℝ) (346495439382749 / 10000000000000000 : ℝ)
    (cell12256 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · have h := gap_lower (n := 12256) (a := (5134620755969 / 6250000000000 : ℝ)) (b := (8407064697 / 5000000000000 : ℝ)) (q := (577677487823 / 25000000000000 : ℝ))
      (E := (cell12256 ⟨56, by decide⟩).energy) (xi := (346495439382749 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12256 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12256]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12256])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12256) (a := (5134620755969 / 6250000000000 : ℝ)) (b := (8407064697 / 5000000000000 : ℝ)) (q := (577677487823 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12256])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12256])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12256]

theorem cert12256_57 : CellCertificate 12256 (179905204769477 / 2000000000000000 : ℝ) (1713828238493301 / 1000000000000000000 : ℝ) (346495439382749 / 10000000000000000 : ℝ)
    (cell12256 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · have h := gap_lower (n := 12256) (a := (82120167010753 / 100000000000000 : ℝ)) (b := (8407064697 / 5000000000000 : ℝ)) (q := (115535697367 / 5000000000000 : ℝ))
      (E := (cell12256 ⟨57, by decide⟩).energy) (xi := (346495439382749 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12256 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12256]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12256])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12256) (a := (82120167010753 / 100000000000000 : ℝ)) (b := (8407064697 / 5000000000000 : ℝ)) (q := (115535697367 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12256])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12256])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12256]

theorem cert12256_58 : CellCertificate 12256 (179905204769477 / 2000000000000000 : ℝ) (1713828238493301 / 1000000000000000000 : ℝ) (346495439382749 / 10000000000000000 : ℝ)
    (cell12256 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · have h := gap_lower (n := 12256) (a := (82086425266779 / 100000000000000 : ℝ)) (b := (8407064697 / 5000000000000 : ℝ)) (q := (462143591917 / 20000000000000 : ℝ))
      (E := (cell12256 ⟨58, by decide⟩).energy) (xi := (346495439382749 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12256 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12256]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12256])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12256) (a := (82086425266779 / 100000000000000 : ℝ)) (b := (8407064697 / 5000000000000 : ℝ)) (q := (462143591917 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12256])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12256])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12256]

theorem cert12256_59 : CellCertificate 12256 (179905204769477 / 2000000000000000 : ℝ) (1713828238493301 / 1000000000000000000 : ℝ) (346495439382749 / 10000000000000000 : ℝ)
    (cell12256 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · have h := gap_lower (n := 12256) (a := (82052706835871 / 100000000000000 : ℝ)) (b := (8407064697 / 5000000000000 : ℝ)) (q := (462144385081 / 20000000000000 : ℝ))
      (E := (cell12256 ⟨59, by decide⟩).energy) (xi := (346495439382749 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12256 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12256]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12256])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12256) (a := (82052706835871 / 100000000000000 : ℝ)) (b := (8407064697 / 5000000000000 : ℝ)) (q := (462144385081 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12256])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12256])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12256]

theorem cert12257_40 : CellCertificate 12257 (562185068739 / 6250000000000 : ℝ) (342737673282557 / 200000000000000000 : ℝ) (173233206758721 / 5000000000000000 : ℝ)
    (cell12257 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · have h := gap_lower (n := 12257) (a := (8269736787427 / 10000000000000 : ℝ)) (b := (33625478473 / 20000000000000 : ℝ)) (q := (1155249666391 / 50000000000000 : ℝ))
      (E := (cell12257 ⟨40, by decide⟩).energy) (xi := (173233206758721 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12257 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12257]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12257])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12257) (a := (8269736787427 / 10000000000000 : ℝ)) (b := (33625478473 / 20000000000000 : ℝ)) (q := (1155249666391 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12257])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12257])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12257]

theorem cert12257_41 : CellCertificate 12257 (562185068739 / 6250000000000 : ℝ) (342737673282557 / 200000000000000000 : ℝ) (173233206758721 / 5000000000000000 : ℝ)
    (cell12257 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · have h := gap_lower (n := 12257) (a := (82663225771963 / 100000000000000 : ℝ)) (b := (33625478473 / 20000000000000 : ℝ)) (q := (2310503322361 / 100000000000000 : ℝ))
      (E := (cell12257 ⟨41, by decide⟩).energy) (xi := (173233206758721 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12257 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12257]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12257])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12257) (a := (82663225771963 / 100000000000000 : ℝ)) (b := (33625478473 / 20000000000000 : ℝ)) (q := (2310503322361 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12257])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12257])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12257]

theorem cert12257_42 : CellCertificate 12257 (562185068739 / 6250000000000 : ℝ) (342737673282557 / 200000000000000000 : ℝ) (173233206758721 / 5000000000000000 : ℝ)
    (cell12257 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · have h := gap_lower (n := 12257) (a := (16525821494573 / 20000000000000 : ℝ)) (b := (33625478473 / 20000000000000 : ℝ)) (q := (1155253648639 / 50000000000000 : ℝ))
      (E := (cell12257 ⟨42, by decide⟩).energy) (xi := (173233206758721 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12257 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12257]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12257])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12257) (a := (16525821494573 / 20000000000000 : ℝ)) (b := (33625478473 / 20000000000000 : ℝ)) (q := (1155253648639 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12257])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12257])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12257]

theorem cert12257_43 : CellCertificate 12257 (562185068739 / 6250000000000 : ℝ) (342737673282557 / 200000000000000000 : ℝ) (173233206758721 / 5000000000000000 : ℝ)
    (cell12257 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · have h := gap_lower (n := 12257) (a := (82595012946937 / 100000000000000 : ℝ)) (b := (33625478473 / 20000000000000 : ℝ)) (q := (231051131619 / 10000000000000 : ℝ))
      (E := (cell12257 ⟨43, by decide⟩).energy) (xi := (173233206758721 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12257 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12257]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12257])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12257) (a := (82595012946937 / 100000000000000 : ℝ)) (b := (33625478473 / 20000000000000 : ℝ)) (q := (231051131619 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12257])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12257])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12257]

theorem cert12257_44 : CellCertificate 12257 (562185068739 / 6250000000000 : ℝ) (342737673282557 / 200000000000000000 : ℝ) (173233206758721 / 5000000000000000 : ℝ)
    (cell12257 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · have h := gap_lower (n := 12257) (a := (41280471082147 / 50000000000000 : ℝ)) (b := (33625478473 / 20000000000000 : ℝ)) (q := (72203603751 / 3125000000000 : ℝ))
      (E := (cell12257 ⟨44, by decide⟩).energy) (xi := (173233206758721 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12257 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12257]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12257])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12257) (a := (41280471082147 / 50000000000000 : ℝ)) (b := (33625478473 / 20000000000000 : ℝ)) (q := (72203603751 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12257])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12257])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12257]

theorem cert12257_45 : CellCertificate 12257 (562185068739 / 6250000000000 : ℝ) (342737673282557 / 200000000000000000 : ℝ) (173233206758721 / 5000000000000000 : ℝ)
    (cell12257 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · have h := gap_lower (n := 12257) (a := (82526895095201 / 100000000000000 : ℝ)) (b := (33625478473 / 20000000000000 : ℝ)) (q := (288814913531 / 12500000000000 : ℝ))
      (E := (cell12257 ⟨45, by decide⟩).energy) (xi := (173233206758721 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12257 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12257]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12257])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12257) (a := (82526895095201 / 100000000000000 : ℝ)) (b := (33625478473 / 20000000000000 : ℝ)) (q := (288814913531 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12257])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12257])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12257]

theorem cert12257_46 : CellCertificate 12257 (562185068739 / 6250000000000 : ℝ) (342737673282557 / 200000000000000000 : ℝ) (173233206758721 / 5000000000000000 : ℝ)
    (cell12257 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · have h := gap_lower (n := 12257) (a := (82492871710071 / 100000000000000 : ℝ)) (b := (33625478473 / 20000000000000 : ℝ)) (q := (462104656013 / 20000000000000 : ℝ))
      (E := (cell12257 ⟨46, by decide⟩).energy) (xi := (173233206758721 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12257 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12257]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12257])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12257) (a := (82492871710071 / 100000000000000 : ℝ)) (b := (33625478473 / 20000000000000 : ℝ)) (q := (462104656013 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12257])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12257])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12257]

theorem cert12257_47 : CellCertificate 12257 (562185068739 / 6250000000000 : ℝ) (342737673282557 / 200000000000000000 : ℝ) (173233206758721 / 5000000000000000 : ℝ)
    (cell12257 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · have h := gap_lower (n := 12257) (a := (82458871979471 / 100000000000000 : ℝ)) (b := (33625478473 / 20000000000000 : ℝ)) (q := (1155263646677 / 50000000000000 : ℝ))
      (E := (cell12257 ⟨47, by decide⟩).energy) (xi := (173233206758721 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12257 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12257]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12257])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12257) (a := (82458871979471 / 100000000000000 : ℝ)) (b := (33625478473 / 20000000000000 : ℝ)) (q := (1155263646677 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12257])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12257])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12257]

theorem cert12257_48 : CellCertificate 12257 (562185068739 / 6250000000000 : ℝ) (342737673282557 / 200000000000000000 : ℝ) (173233206758721 / 5000000000000000 : ℝ)
    (cell12257 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · have h := gap_lower (n := 12257) (a := (82424895874111 / 100000000000000 : ℝ)) (b := (33625478473 / 20000000000000 : ℝ)) (q := (2310531288089 / 100000000000000 : ℝ))
      (E := (cell12257 ⟨48, by decide⟩).energy) (xi := (173233206758721 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12257 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12257]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12257])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12257) (a := (82424895874111 / 100000000000000 : ℝ)) (b := (33625478473 / 20000000000000 : ℝ)) (q := (2310531288089 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12257])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12257])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12257]

theorem cert12257_49 : CellCertificate 12257 (562185068739 / 6250000000000 : ℝ) (342737673282557 / 200000000000000000 : ℝ) (173233206758721 / 5000000000000000 : ℝ)
    (cell12257 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · have h := gap_lower (n := 12257) (a := (41195471682427 / 50000000000000 : ℝ)) (b := (33625478473 / 20000000000000 : ℝ)) (q := (2310535262839 / 100000000000000 : ℝ))
      (E := (cell12257 ⟨49, by decide⟩).energy) (xi := (173233206758721 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12257 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12257]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12257])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12257) (a := (41195471682427 / 50000000000000 : ℝ)) (b := (33625478473 / 20000000000000 : ℝ)) (q := (2310535262839 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12257])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12257])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12257]

theorem cert12257_50 : CellCertificate 12257 (562185068739 / 6250000000000 : ℝ) (342737673282557 / 200000000000000000 : ℝ) (173233206758721 / 5000000000000000 : ℝ)
    (cell12257 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · have h := gap_lower (n := 12257) (a := (16471402884541 / 20000000000000 : ℝ)) (b := (33625478473 / 20000000000000 : ℝ)) (q := (462107854981 / 20000000000000 : ℝ))
      (E := (cell12257 ⟨50, by decide⟩).energy) (xi := (173233206758721 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12257 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12257]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12257])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12257) (a := (16471402884541 / 20000000000000 : ℝ)) (b := (33625478473 / 20000000000000 : ℝ)) (q := (462107854981 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12257])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12257])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12257]

theorem cert12257_51 : CellCertificate 12257 (562185068739 / 6250000000000 : ℝ) (342737673282557 / 200000000000000000 : ℝ) (173233206758721 / 5000000000000000 : ℝ)
    (cell12257 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · have h := gap_lower (n := 12257) (a := (82323109018819 / 100000000000000 : ℝ)) (b := (33625478473 / 20000000000000 : ℝ)) (q := (2310543263537 / 100000000000000 : ℝ))
      (E := (cell12257 ⟨51, by decide⟩).energy) (xi := (173233206758721 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12257 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12257]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12257])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12257) (a := (82323109018819 / 100000000000000 : ℝ)) (b := (33625478473 / 20000000000000 : ℝ)) (q := (2310543263537 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12257])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12257])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12257]

theorem cert12257_52 : CellCertificate 12257 (562185068739 / 6250000000000 : ℝ) (342737673282557 / 200000000000000000 : ℝ) (173233206758721 / 5000000000000000 : ℝ)
    (cell12257 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · have h := gap_lower (n := 12257) (a := (20572306781123 / 25000000000000 : ℝ)) (b := (33625478473 / 20000000000000 : ℝ)) (q := (2310547285653 / 100000000000000 : ℝ))
      (E := (cell12257 ⟨52, by decide⟩).energy) (xi := (173233206758721 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12257 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12257]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12257])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12257) (a := (20572306781123 / 25000000000000 : ℝ)) (b := (33625478473 / 20000000000000 : ℝ)) (q := (2310547285653 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12257])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12257])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12257]

theorem cert12257_53 : CellCertificate 12257 (562185068739 / 6250000000000 : ℝ) (342737673282557 / 200000000000000000 : ℝ) (173233206758721 / 5000000000000000 : ℝ)
    (cell12257 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · have h := gap_lower (n := 12257) (a := (82255368711167 / 100000000000000 : ℝ)) (b := (33625478473 / 20000000000000 : ℝ)) (q := (2310551280031 / 100000000000000 : ℝ))
      (E := (cell12257 ⟨53, by decide⟩).energy) (xi := (173233206758721 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12257 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12257]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12257])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12257) (a := (82255368711167 / 100000000000000 : ℝ)) (b := (33625478473 / 20000000000000 : ℝ)) (q := (2310551280031 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12257])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12257])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12257]

theorem cert12257_54 : CellCertificate 12257 (562185068739 / 6250000000000 : ℝ) (342737673282557 / 200000000000000000 : ℝ) (173233206758721 / 5000000000000000 : ℝ)
    (cell12257 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · have h := gap_lower (n := 12257) (a := (82221533750431 / 100000000000000 : ℝ)) (b := (33625478473 / 20000000000000 : ℝ)) (q := (144409702761 / 6250000000000 : ℝ))
      (E := (cell12257 ⟨54, by decide⟩).energy) (xi := (173233206758721 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12257 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12257]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12257])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12257) (a := (82221533750431 / 100000000000000 : ℝ)) (b := (33625478473 / 20000000000000 : ℝ)) (q := (144409702761 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12257])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12257])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12257]

theorem cert12257_55 : CellCertificate 12257 (562185068739 / 6250000000000 : ℝ) (342737673282557 / 200000000000000000 : ℝ) (173233206758721 / 5000000000000000 : ℝ)
    (cell12257 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · have h := gap_lower (n := 12257) (a := (82187722214009 / 100000000000000 : ℝ)) (b := (33625478473 / 20000000000000 : ℝ)) (q := (57763980861 / 2500000000000 : ℝ))
      (E := (cell12257 ⟨55, by decide⟩).energy) (xi := (173233206758721 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12257 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12257]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12257])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12257) (a := (82187722214009 / 100000000000000 : ℝ)) (b := (33625478473 / 20000000000000 : ℝ)) (q := (57763980861 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12257])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12257])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12257]

theorem cert12257_56 : CellCertificate 12257 (562185068739 / 6250000000000 : ℝ) (342737673282557 / 200000000000000000 : ℝ) (173233206758721 / 5000000000000000 : ℝ)
    (cell12257 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · have h := gap_lower (n := 12257) (a := (41076967036887 / 50000000000000 : ℝ)) (b := (33625478473 / 20000000000000 : ℝ)) (q := (1155281623987 / 50000000000000 : ℝ))
      (E := (cell12257 ⟨56, by decide⟩).energy) (xi := (173233206758721 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12257 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12257]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12257])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12257) (a := (41076967036887 / 50000000000000 : ℝ)) (b := (33625478473 / 20000000000000 : ℝ)) (q := (1155281623987 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12257])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12257])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12257]

theorem cert12257_57 : CellCertificate 12257 (562185068739 / 6250000000000 : ℝ) (342737673282557 / 200000000000000000 : ℝ) (173233206758721 / 5000000000000000 : ℝ)
    (cell12257 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · have h := gap_lower (n := 12257) (a := (41060084650867 / 50000000000000 : ℝ)) (b := (33625478473 / 20000000000000 : ℝ)) (q := (1155283611311 / 50000000000000 : ℝ))
      (E := (cell12257 ⟨57, by decide⟩).energy) (xi := (173233206758721 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12257 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12257]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12257])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12257) (a := (41060084650867 / 50000000000000 : ℝ)) (b := (33625478473 / 20000000000000 : ℝ)) (q := (1155283611311 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12257])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12257])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12257]

theorem cert12257_58 : CellCertificate 12257 (562185068739 / 6250000000000 : ℝ) (342737673282557 / 200000000000000000 : ℝ) (173233206758721 / 5000000000000000 : ℝ)
    (cell12257 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · have h := gap_lower (n := 12257) (a := (82086427870041 / 100000000000000 : ℝ)) (b := (33625478473 / 20000000000000 : ℝ)) (q := (23105712733 / 1000000000000 : ℝ))
      (E := (cell12257 ⟨58, by decide⟩).energy) (xi := (173233206758721 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12257 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12257]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12257])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12257) (a := (82086427870041 / 100000000000000 : ℝ)) (b := (33625478473 / 20000000000000 : ℝ)) (q := (23105712733 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12257])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12257])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12257]

theorem cert12257_59 : CellCertificate 12257 (562185068739 / 6250000000000 : ℝ) (342737673282557 / 200000000000000000 : ℝ) (173233206758721 / 5000000000000000 : ℝ)
    (cell12257 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · have h := gap_lower (n := 12257) (a := (16410541950197 / 20000000000000 : ℝ)) (b := (33625478473 / 20000000000000 : ℝ)) (q := (462115043831 / 20000000000000 : ℝ))
      (E := (cell12257 ⟨59, by decide⟩).energy) (xi := (173233206758721 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12257 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12257]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12257])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12257) (a := (16410541950197 / 20000000000000 : ℝ)) (b := (33625478473 / 20000000000000 : ℝ)) (q := (462115043831 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12257])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12257])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12257]

theorem cert12258_40 : CellCertificate 12258 (89946620082029 / 1000000000000000 : ℝ) (856774258580697 / 500000000000000000 : ℝ) (173218696319487 / 5000000000000000 : ℝ)
    (cell12258 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · have h := gap_lower (n := 12258) (a := (82697364790991 / 100000000000000 : ℝ)) (b := (262677333 / 156250000000 : ℝ)) (q := (462070542543 / 20000000000000 : ℝ))
      (E := (cell12258 ⟨40, by decide⟩).energy) (xi := (173218696319487 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12258 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12258]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12258])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12258) (a := (82697364790991 / 100000000000000 : ℝ)) (b := (262677333 / 156250000000 : ℝ)) (q := (462070542543 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12258])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12258])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12258]

theorem cert12258_41 : CellCertificate 12258 (89946620082029 / 1000000000000000 : ℝ) (856774258580697 / 500000000000000000 : ℝ) (173218696319487 / 5000000000000000 : ℝ)
    (cell12258 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · have h := gap_lower (n := 12258) (a := (41331611504173 / 50000000000000 : ℝ)) (b := (262677333 / 156250000000 : ℝ)) (q := (1155178364057 / 50000000000000 : ℝ))
      (E := (cell12258 ⟨41, by decide⟩).energy) (xi := (173218696319487 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12258 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12258]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12258])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12258) (a := (41331611504173 / 50000000000000 : ℝ)) (b := (262677333 / 156250000000 : ℝ)) (q := (1155178364057 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12258])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12258])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12258]

theorem cert12258_42 : CellCertificate 12258 (89946620082029 / 1000000000000000 : ℝ) (856774258580697 / 500000000000000000 : ℝ) (173218696319487 / 5000000000000000 : ℝ)
    (cell12258 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · have h := gap_lower (n := 12258) (a := (20657276257117 / 25000000000000 : ℝ)) (b := (262677333 / 156250000000 : ℝ)) (q := (2310360670867 / 100000000000000 : ℝ))
      (E := (cell12258 ⟨42, by decide⟩).energy) (xi := (173218696319487 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12258 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12258]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12258])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12258) (a := (20657276257117 / 25000000000000 : ℝ)) (b := (262677333 / 156250000000 : ℝ)) (q := (2310360670867 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12258])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12258])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12258]

theorem cert12258_43 : CellCertificate 12258 (89946620082029 / 1000000000000000 : ℝ) (856774258580697 / 500000000000000000 : ℝ) (173218696319487 / 5000000000000000 : ℝ)
    (cell12258 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · have h := gap_lower (n := 12258) (a := (41297505410659 / 50000000000000 : ℝ)) (b := (262677333 / 156250000000 : ℝ)) (q := (144397794819 / 6250000000000 : ℝ))
      (E := (cell12258 ⟨43, by decide⟩).energy) (xi := (173218696319487 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12258 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12258]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12258])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12258) (a := (41297505410659 / 50000000000000 : ℝ)) (b := (262677333 / 156250000000 : ℝ)) (q := (144397794819 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12258])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12258])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12258]

theorem cert12258_44 : CellCertificate 12258 (89946620082029 / 1000000000000000 : ℝ) (856774258580697 / 500000000000000000 : ℝ) (173218696319487 / 5000000000000000 : ℝ)
    (cell12258 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · have h := gap_lower (n := 12258) (a := (20640235089253 / 25000000000000 : ℝ)) (b := (262677333 / 156250000000 : ℝ)) (q := (7219902157 / 312500000000 : ℝ))
      (E := (cell12258 ⟨44, by decide⟩).energy) (xi := (173218696319487 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12258 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12258]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12258])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12258) (a := (20640235089253 / 25000000000000 : ℝ)) (b := (262677333 / 156250000000 : ℝ)) (q := (7219902157 / 312500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12258])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12258])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12258]

theorem cert12258_45 : CellCertificate 12258 (89946620082029 / 1000000000000000 : ℝ) (856774258580697 / 500000000000000000 : ℝ) (173218696319487 / 5000000000000000 : ℝ)
    (cell12258 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · have h := gap_lower (n := 12258) (a := (41263446802907 / 50000000000000 : ℝ)) (b := (262677333 / 156250000000 : ℝ)) (q := (2310372707287 / 100000000000000 : ℝ))
      (E := (cell12258 ⟨45, by decide⟩).energy) (xi := (173218696319487 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12258 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12258]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12258])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12258) (a := (41263446802907 / 50000000000000 : ℝ)) (b := (262677333 / 156250000000 : ℝ)) (q := (2310372707287 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12258])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12258])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12258]

theorem cert12258_46 : CellCertificate 12258 (89946620082029 / 1000000000000000 : ℝ) (856774258580697 / 500000000000000000 : ℝ) (173218696319487 / 5000000000000000 : ℝ)
    (cell12258 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · have h := gap_lower (n := 12258) (a := (82492870538141 / 100000000000000 : ℝ)) (b := (262677333 / 156250000000 : ℝ)) (q := (2310376649853 / 100000000000000 : ℝ))
      (E := (cell12258 ⟨46, by decide⟩).energy) (xi := (173218696319487 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12258 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12258]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12258])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12258) (a := (82492870538141 / 100000000000000 : ℝ)) (b := (262677333 / 156250000000 : ℝ)) (q := (2310376649853 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12258])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12258])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12258]

theorem cert12258_47 : CellCertificate 12258 (89946620082029 / 1000000000000000 : ℝ) (856774258580697 / 500000000000000000 : ℝ) (173218696319487 / 5000000000000000 : ℝ)
    (cell12258 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · have h := gap_lower (n := 12258) (a := (82458871124559 / 100000000000000 : ℝ)) (b := (262677333 / 156250000000 : ℝ)) (q := (72199396671 / 3125000000000 : ℝ))
      (E := (cell12258 ⟨47, by decide⟩).energy) (xi := (173218696319487 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12258 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12258]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12258])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12258) (a := (82458871124559 / 100000000000000 : ℝ)) (b := (262677333 / 156250000000 : ℝ)) (q := (72199396671 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12258])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12258])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12258]

theorem cert12258_48 : CellCertificate 12258 (89946620082029 / 1000000000000000 : ℝ) (856774258580697 / 500000000000000000 : ℝ) (173218696319487 / 5000000000000000 : ℝ)
    (cell12258 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · have h := gap_lower (n := 12258) (a := (82424895335779 / 100000000000000 : ℝ)) (b := (262677333 / 156250000000 : ℝ)) (q := (2310384660407 / 100000000000000 : ℝ))
      (E := (cell12258 ⟨48, by decide⟩).energy) (xi := (173218696319487 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12258 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12258]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12258])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12258) (a := (82424895335779 / 100000000000000 : ℝ)) (b := (262677333 / 156250000000 : ℝ)) (q := (2310384660407 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12258])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12258])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12258]

theorem cert12258_49 : CellCertificate 12258 (89946620082029 / 1000000000000000 : ℝ) (856774258580697 / 500000000000000000 : ℝ) (173218696319487 / 5000000000000000 : ℝ)
    (cell12258 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · have h := gap_lower (n := 12258) (a := (10298867892833 / 12500000000000 : ℝ)) (b := (262677333 / 156250000000 : ℝ)) (q := (1155194333493 / 50000000000000 : ℝ))
      (E := (cell12258 ⟨49, by decide⟩).energy) (xi := (173218696319487 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12258 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12258]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12258])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12258) (a := (10298867892833 / 12500000000000 : ℝ)) (b := (262677333 / 156250000000 : ℝ)) (q := (1155194333493 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12258])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12258])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12258]

theorem cert12258_50 : CellCertificate 12258 (89946620082029 / 1000000000000000 : ℝ) (856774258580697 / 500000000000000000 : ℝ) (173218696319487 / 5000000000000000 : ℝ)
    (cell12258 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · have h := gap_lower (n := 12258) (a := (41178507258111 / 50000000000000 : ℝ)) (b := (262677333 / 156250000000 : ℝ)) (q := (2310392652701 / 100000000000000 : ℝ))
      (E := (cell12258 ⟨50, by decide⟩).energy) (xi := (173218696319487 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12258 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12258]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12258])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12258) (a := (41178507258111 / 50000000000000 : ℝ)) (b := (262677333 / 156250000000 : ℝ)) (q := (2310392652701 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12258])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12258])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12258]

theorem cert12258_51 : CellCertificate 12258 (89946620082029 / 1000000000000000 : ℝ) (856774258580697 / 500000000000000000 : ℝ) (173218696319487 / 5000000000000000 : ℝ)
    (cell12258 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · have h := gap_lower (n := 12258) (a := (41161554713803 / 50000000000000 : ℝ)) (b := (262677333 / 156250000000 : ℝ)) (q := (72199896083 / 3125000000000 : ℝ))
      (E := (cell12258 ⟨51, by decide⟩).energy) (xi := (173218696319487 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12258 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12258]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12258])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12258) (a := (41161554713803 / 50000000000000 : ℝ)) (b := (262677333 / 156250000000 : ℝ)) (q := (72199896083 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12258])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12258])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12258]

theorem cert12258_52 : CellCertificate 12258 (89946620082029 / 1000000000000000 : ℝ) (856774258580697 / 500000000000000000 : ℝ) (173218696319487 / 5000000000000000 : ℝ)
    (cell12258 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · have h := gap_lower (n := 12258) (a := (16457845569623 / 20000000000000 : ℝ)) (b := (262677333 / 156250000000 : ℝ)) (q := (577600167967 / 25000000000000 : ℝ))
      (E := (cell12258 ⟨52, by decide⟩).energy) (xi := (173218696319487 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12258 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12258]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12258])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12258) (a := (16457845569623 / 20000000000000 : ℝ)) (b := (262677333 / 156250000000 : ℝ)) (q := (577600167967 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12258])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12258])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12258]

theorem cert12258_53 : CellCertificate 12258 (89946620082029 / 1000000000000000 : ℝ) (856774258580697 / 500000000000000000 : ℝ) (173218696319487 / 5000000000000000 : ℝ)
    (cell12258 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · have h := gap_lower (n := 12258) (a := (10281921218649 / 12500000000000 : ℝ)) (b := (262677333 / 156250000000 : ℝ)) (q := (577601160513 / 25000000000000 : ℝ))
      (E := (cell12258 ⟨53, by decide⟩).energy) (xi := (173218696319487 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12258 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12258]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12258])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12258) (a := (10281921218649 / 12500000000000 : ℝ)) (b := (262677333 / 156250000000 : ℝ)) (q := (577601160513 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12258])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12258])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12258]

theorem cert12258_54 : CellCertificate 12258 (89946620082029 / 1000000000000000 : ℝ) (856774258580697 / 500000000000000000 : ℝ) (173218696319487 / 5000000000000000 : ℝ)
    (cell12258 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · have h := gap_lower (n := 12258) (a := (82221535102423 / 100000000000000 : ℝ)) (b := (262677333 / 156250000000 : ℝ)) (q := (462081728349 / 20000000000000 : ℝ))
      (E := (cell12258 ⟨54, by decide⟩).energy) (xi := (173218696319487 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12258 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12258]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12258])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12258) (a := (82221535102423 / 100000000000000 : ℝ)) (b := (262677333 / 156250000000 : ℝ)) (q := (462081728349 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12258])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12258])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12258]

theorem cert12258_55 : CellCertificate 12258 (89946620082029 / 1000000000000000 : ℝ) (856774258580697 / 500000000000000000 : ℝ) (173218696319487 / 5000000000000000 : ℝ)
    (cell12258 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · have h := gap_lower (n := 12258) (a := (82187723879537 / 100000000000000 : ℝ)) (b := (262677333 / 156250000000 : ℝ)) (q := (288801583539 / 12500000000000 : ℝ))
      (E := (cell12258 ⟨55, by decide⟩).energy) (xi := (173218696319487 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12258 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12258]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12258])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12258) (a := (82187723879537 / 100000000000000 : ℝ)) (b := (262677333 / 156250000000 : ℝ)) (q := (288801583539 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12258])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12258])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12258]

theorem cert12258_56 : CellCertificate 12258 (89946620082029 / 1000000000000000 : ℝ) (856774258580697 / 500000000000000000 : ℝ) (173218696319487 / 5000000000000000 : ℝ)
    (cell12258 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · have h := gap_lower (n := 12258) (a := (16430787210481 / 20000000000000 : ℝ)) (b := (262677333 / 156250000000 : ℝ)) (q := (1155208329913 / 50000000000000 : ℝ))
      (E := (cell12258 ⟨56, by decide⟩).energy) (xi := (173218696319487 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12258 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12258]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12258])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12258) (a := (16430787210481 / 20000000000000 : ℝ)) (b := (262677333 / 156250000000 : ℝ)) (q := (1155208329913 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12258])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12258])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12258]

theorem cert12258_57 : CellCertificate 12258 (89946620082029 / 1000000000000000 : ℝ) (856774258580697 / 500000000000000000 : ℝ) (173218696319487 / 5000000000000000 : ℝ)
    (cell12258 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · have h := gap_lower (n := 12258) (a := (82120171593037 / 100000000000000 : ℝ)) (b := (262677333 / 156250000000 : ℝ)) (q := (1155210306581 / 50000000000000 : ℝ))
      (E := (cell12258 ⟨57, by decide⟩).energy) (xi := (173218696319487 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12258 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12258]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12258])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12258) (a := (82120171593037 / 100000000000000 : ℝ)) (b := (262677333 / 156250000000 : ℝ)) (q := (1155210306581 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12258])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12258])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12258]

theorem cert12258_58 : CellCertificate 12258 (89946620082029 / 1000000000000000 : ℝ) (856774258580697 / 500000000000000000 : ℝ) (173218696319487 / 5000000000000000 : ℝ)
    (cell12258 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · have h := gap_lower (n := 12258) (a := (41043215236793 / 50000000000000 : ℝ)) (b := (262677333 / 156250000000 : ℝ)) (q := (2310424643233 / 100000000000000 : ℝ))
      (E := (cell12258 ⟨58, by decide⟩).energy) (xi := (173218696319487 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12258 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12258]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12258])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12258) (a := (41043215236793 / 50000000000000 : ℝ)) (b := (262677333 / 156250000000 : ℝ)) (q := (2310424643233 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12258])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12258])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12258]

theorem cert12258_59 : CellCertificate 12258 (89946620082029 / 1000000000000000 : ℝ) (856774258580697 / 500000000000000000 : ℝ) (173218696319487 / 5000000000000000 : ℝ)
    (cell12258 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · have h := gap_lower (n := 12258) (a := (41026356333171 / 50000000000000 : ℝ)) (b := (262677333 / 156250000000 : ℝ)) (q := (1155214314169 / 50000000000000 : ℝ))
      (E := (cell12258 ⟨59, by decide⟩).energy) (xi := (173218696319487 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12258 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12258]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12258])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12258) (a := (41026356333171 / 50000000000000 : ℝ)) (b := (262677333 / 156250000000 : ℝ)) (q := (1155214314169 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12258])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12258])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12258]

theorem cert12259_40 : CellCertificate 12259 (179887259271979 / 2000000000000000 : ℝ) (1713408690733541 / 1000000000000000000 : ℝ) (346408376745887 / 10000000000000000 : ℝ)
    (cell12259 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · have h := gap_lower (n := 12259) (a := (20674340427177 / 25000000000000 : ℝ)) (b := (84049798101 / 50000000000000 : ℝ)) (q := (144387887901 / 6250000000000 : ℝ))
      (E := (cell12259 ⟨40, by decide⟩).energy) (xi := (346408376745887 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12259 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12259]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12259])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12259) (a := (20674340427177 / 25000000000000 : ℝ)) (b := (84049798101 / 50000000000000 : ℝ)) (q := (144387887901 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12259])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12259])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12259]

theorem cert12259_41 : CellCertificate 12259 (179887259271979 / 2000000000000000 : ℝ) (1713408690733541 / 1000000000000000000 : ℝ) (346408376745887 / 10000000000000000 : ℝ)
    (cell12259 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · have h := gap_lower (n := 12259) (a := (41331610122843 / 50000000000000 : ℝ)) (b := (84049798101 / 50000000000000 : ℝ)) (q := (577552547249 / 25000000000000 : ℝ))
      (E := (cell12259 ⟨41, by decide⟩).energy) (xi := (346408376745887 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12259 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12259]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12259])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12259) (a := (41331610122843 / 50000000000000 : ℝ)) (b := (84049798101 / 50000000000000 : ℝ)) (q := (577552547249 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12259])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12259])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12259]

theorem cert12259_42 : CellCertificate 12259 (179887259271979 / 2000000000000000 : ℝ) (1713408690733541 / 1000000000000000000 : ℝ) (346408376745887 / 10000000000000000 : ℝ)
    (cell12259 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · have h := gap_lower (n := 12259) (a := (82629102584987 / 100000000000000 : ℝ)) (b := (84049798101 / 50000000000000 : ℝ)) (q := (2310214158399 / 100000000000000 : ℝ))
      (E := (cell12259 ⟨42, by decide⟩).energy) (xi := (346408376745887 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12259 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12259]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12259])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12259) (a := (82629102584987 / 100000000000000 : ℝ)) (b := (84049798101 / 50000000000000 : ℝ)) (q := (2310214158399 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12259])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12259])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12259]

theorem cert12259_43 : CellCertificate 12259 (179887259271979 / 2000000000000000 : ℝ) (1713408690733541 / 1000000000000000000 : ℝ) (346408376745887 / 10000000000000000 : ℝ)
    (cell12259 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · have h := gap_lower (n := 12259) (a := (3303800347863 / 4000000000000 : ℝ)) (b := (84049798101 / 50000000000000 : ℝ)) (q := (1155109086639 / 50000000000000 : ℝ))
      (E := (cell12259 ⟨43, by decide⟩).energy) (xi := (346408376745887 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12259 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12259]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12259])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12259) (a := (3303800347863 / 4000000000000 : ℝ)) (b := (84049798101 / 50000000000000 : ℝ)) (q := (1155109086639 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12259])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12259])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12259]

theorem cert12259_44 : CellCertificate 12259 (179887259271979 / 2000000000000000 : ℝ) (1713408690733541 / 1000000000000000000 : ℝ) (346408376745887 / 10000000000000000 : ℝ)
    (cell12259 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · have h := gap_lower (n := 12259) (a := (16512187710113 / 20000000000000 : ℝ)) (b := (84049798101 / 50000000000000 : ℝ)) (q := (2310222174569 / 100000000000000 : ℝ))
      (E := (cell12259 ⟨44, by decide⟩).energy) (xi := (346408376745887 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12259 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12259]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12259])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12259) (a := (16512187710113 / 20000000000000 : ℝ)) (b := (84049798101 / 50000000000000 : ℝ)) (q := (2310222174569 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12259])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12259])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12259]

theorem cert12259_45 : CellCertificate 12259 (179887259271979 / 2000000000000000 : ℝ) (1713408690733541 / 1000000000000000000 : ℝ) (346408376745887 / 10000000000000000 : ℝ)
    (cell12259 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · have h := gap_lower (n := 12259) (a := (10315861514653 / 12500000000000 : ℝ)) (b := (84049798101 / 50000000000000 : ℝ)) (q := (2310226161713 / 100000000000000 : ℝ))
      (E := (cell12259 ⟨45, by decide⟩).energy) (xi := (346408376745887 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12259 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12259]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12259])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12259) (a := (10315861514653 / 12500000000000 : ℝ)) (b := (84049798101 / 50000000000000 : ℝ)) (q := (2310226161713 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12259])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12259])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12259]

theorem cert12259_46 : CellCertificate 12259 (179887259271979 / 2000000000000000 : ℝ) (1713408690733541 / 1000000000000000000 : ℝ) (346408376745887 / 10000000000000000 : ℝ)
    (cell12259 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · have h := gap_lower (n := 12259) (a := (10311608670871 / 12500000000000 : ℝ)) (b := (84049798101 / 50000000000000 : ℝ)) (q := (462046026787 / 20000000000000 : ℝ))
      (E := (cell12259 ⟨46, by decide⟩).energy) (xi := (346408376745887 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12259 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12259]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12259])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12259) (a := (10311608670871 / 12500000000000 : ℝ)) (b := (84049798101 / 50000000000000 : ℝ)) (q := (462046026787 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12259])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12259])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12259]

theorem cert12259_47 : CellCertificate 12259 (179887259271979 / 2000000000000000 : ℝ) (1713408690733541 / 1000000000000000000 : ℝ) (346408376745887 / 10000000000000000 : ℝ)
    (cell12259 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · have h := gap_lower (n := 12259) (a := (82458870270363 / 100000000000000 : ℝ)) (b := (84049798101 / 50000000000000 : ℝ)) (q := (2310234149107 / 100000000000000 : ℝ))
      (E := (cell12259 ⟨47, by decide⟩).energy) (xi := (346408376745887 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12259 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12259]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12259])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12259) (a := (82458870270363 / 100000000000000 : ℝ)) (b := (84049798101 / 50000000000000 : ℝ)) (q := (2310234149107 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12259])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12259])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12259]

theorem cert12259_48 : CellCertificate 12259 (179887259271979 / 2000000000000000 : ℝ) (1713408690733541 / 1000000000000000000 : ℝ) (346408376745887 / 10000000000000000 : ℝ)
    (cell12259 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · have h := gap_lower (n := 12259) (a := (20606223699531 / 25000000000000 : ℝ)) (b := (84049798101 / 50000000000000 : ℝ)) (q := (2310238147197 / 100000000000000 : ℝ))
      (E := (cell12259 ⟨48, by decide⟩).energy) (xi := (346408376745887 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12259 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12259]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12259])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12259) (a := (20606223699531 / 25000000000000 : ℝ)) (b := (84049798101 / 50000000000000 : ℝ)) (q := (2310238147197 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12259])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12259])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12259]

theorem cert12259_49 : CellCertificate 12259 (179887259271979 / 2000000000000000 : ℝ) (1713408690733541 / 1000000000000000000 : ℝ) (346408376745887 / 10000000000000000 : ℝ)
    (cell12259 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · have h := gap_lower (n := 12259) (a := (10298867865139 / 12500000000000 : ℝ)) (b := (84049798101 / 50000000000000 : ℝ)) (q := (1155121063389 / 50000000000000 : ℝ))
      (E := (cell12259 ⟨49, by decide⟩).energy) (xi := (346408376745887 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12259 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12259]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12259])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12259) (a := (10298867865139 / 12500000000000 : ℝ)) (b := (84049798101 / 50000000000000 : ℝ)) (q := (1155121063389 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12259])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12259])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12259]

theorem cert12259_50 : CellCertificate 12259 (179887259271979 / 2000000000000000 : ℝ) (1713408690733541 / 1000000000000000000 : ℝ) (346408376745887 / 10000000000000000 : ℝ)
    (cell12259 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · have h := gap_lower (n := 12259) (a := (82357014610337 / 100000000000000 : ℝ)) (b := (84049798101 / 50000000000000 : ℝ)) (q := (288780768143 / 12500000000000 : ℝ))
      (E := (cell12259 ⟨50, by decide⟩).energy) (xi := (346408376745887 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12259 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12259]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12259])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12259) (a := (82357014610337 / 100000000000000 : ℝ)) (b := (84049798101 / 50000000000000 : ℝ)) (q := (288780768143 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12259])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12259])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12259]

theorem cert12259_51 : CellCertificate 12259 (179887259271979 / 2000000000000000 : ℝ) (1713408690733541 / 1000000000000000000 : ℝ) (346408376745887 / 10000000000000000 : ℝ)
    (cell12259 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · have h := gap_lower (n := 12259) (a := (10290388729619 / 12500000000000 : ℝ)) (b := (84049798101 / 50000000000000 : ℝ)) (q := (2310250141549 / 100000000000000 : ℝ))
      (E := (cell12259 ⟨51, by decide⟩).energy) (xi := (346408376745887 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12259 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12259]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12259])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12259) (a := (10290388729619 / 12500000000000 : ℝ)) (b := (84049798101 / 50000000000000 : ℝ)) (q := (2310250141549 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12259])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12259])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12259]

theorem cert12259_52 : CellCertificate 12259 (179887259271979 / 2000000000000000 : ℝ) (1713408690733541 / 1000000000000000000 : ℝ) (346408376745887 / 10000000000000000 : ℝ)
    (cell12259 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · have h := gap_lower (n := 12259) (a := (82289228572257 / 100000000000000 : ℝ)) (b := (84049798101 / 50000000000000 : ℝ)) (q := (3609772053 / 156250000000 : ℝ))
      (E := (cell12259 ⟨52, by decide⟩).energy) (xi := (346408376745887 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12259 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12259]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12259])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12259) (a := (82289228572257 / 100000000000000 : ℝ)) (b := (84049798101 / 50000000000000 : ℝ)) (q := (3609772053 / 156250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12259])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12259])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12259]

theorem cert12259_53 : CellCertificate 12259 (179887259271979 / 2000000000000000 : ℝ) (1713408690733541 / 1000000000000000000 : ℝ) (346408376745887 / 10000000000000000 : ℝ)
    (cell12259 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · have h := gap_lower (n := 12259) (a := (5140960674231 / 6250000000000 : ℝ)) (b := (84049798101 / 50000000000000 : ℝ)) (q := (2310258118983 / 100000000000000 : ℝ))
      (E := (cell12259 ⟨53, by decide⟩).energy) (xi := (346408376745887 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12259 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12259]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12259])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12259) (a := (5140960674231 / 6250000000000 : ℝ)) (b := (84049798101 / 50000000000000 : ℝ)) (q := (2310258118983 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12259])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12259])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12259]

theorem cert12259_54 : CellCertificate 12259 (179887259271979 / 2000000000000000 : ℝ) (1713408690733541 / 1000000000000000000 : ℝ) (346408376745887 / 10000000000000000 : ℝ)
    (cell12259 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · have h := gap_lower (n := 12259) (a := (10277692056857 / 12500000000000 : ℝ)) (b := (84049798101 / 50000000000000 : ℝ)) (q := (2310262095279 / 100000000000000 : ℝ))
      (E := (cell12259 ⟨54, by decide⟩).energy) (xi := (346408376745887 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12259 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12259]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12259])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12259) (a := (10277692056857 / 12500000000000 : ℝ)) (b := (84049798101 / 50000000000000 : ℝ)) (q := (2310262095279 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12259])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12259])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12259]

theorem cert12259_55 : CellCertificate 12259 (179887259271979 / 2000000000000000 : ℝ) (1713408690733541 / 1000000000000000000 : ℝ) (346408376745887 / 10000000000000000 : ℝ)
    (cell12259 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · have h := gap_lower (n := 12259) (a := (41093862772733 / 50000000000000 : ℝ)) (b := (84049798101 / 50000000000000 : ℝ)) (q := (1155133049579 / 50000000000000 : ℝ))
      (E := (cell12259 ⟨55, by decide⟩).energy) (xi := (346408376745887 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12259 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12259]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12259])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12259) (a := (41093862772733 / 50000000000000 : ℝ)) (b := (84049798101 / 50000000000000 : ℝ)) (q := (1155133049579 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12259])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12259])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12259]

theorem cert12259_56 : CellCertificate 12259 (179887259271979 / 2000000000000000 : ℝ) (1713408690733541 / 1000000000000000000 : ℝ) (346408376745887 / 10000000000000000 : ℝ)
    (cell12259 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · have h := gap_lower (n := 12259) (a := (41076969015699 / 50000000000000 : ℝ)) (b := (84049798101 / 50000000000000 : ℝ)) (q := (577567531943 / 25000000000000 : ℝ))
      (E := (cell12259 ⟨56, by decide⟩).energy) (xi := (346408376745887 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12259 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12259]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12259])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12259) (a := (41076969015699 / 50000000000000 : ℝ)) (b := (84049798101 / 50000000000000 : ℝ)) (q := (577567531943 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12259])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12259])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12259]

theorem cert12259_57 : CellCertificate 12259 (179887259271979 / 2000000000000000 : ℝ) (1713408690733541 / 1000000000000000000 : ℝ) (346408376745887 / 10000000000000000 : ℝ)
    (cell12259 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · have h := gap_lower (n := 12259) (a := (82120173884663 / 100000000000000 : ℝ)) (b := (84049798101 / 50000000000000 : ℝ)) (q := (28878426487 / 1250000000000 : ℝ))
      (E := (cell12259 ⟨57, by decide⟩).energy) (xi := (346408376745887 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12259 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12259]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12259])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12259) (a := (82120173884663 / 100000000000000 : ℝ)) (b := (84049798101 / 50000000000000 : ℝ)) (q := (28878426487 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12259])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12259])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12259]

theorem cert12259_58 : CellCertificate 12259 (179887259271979 / 2000000000000000 : ℝ) (1713408690733541 / 1000000000000000000 : ℝ) (346408376745887 / 10000000000000000 : ℝ)
    (cell12259 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · have h := gap_lower (n := 12259) (a := (41043216538707 / 50000000000000 : ℝ)) (b := (84049798101 / 50000000000000 : ℝ)) (q := (2310278128513 / 100000000000000 : ℝ))
      (E := (cell12259 ⟨58, by decide⟩).energy) (xi := (346408376745887 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12259 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12259]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12259])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12259) (a := (41043216538707 / 50000000000000 : ℝ)) (b := (84049798101 / 50000000000000 : ℝ)) (q := (2310278128513 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12259])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12259])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12259]

theorem cert12259_59 : CellCertificate 12259 (179887259271979 / 2000000000000000 : ℝ) (1713408690733541 / 1000000000000000000 : ℝ) (346408376745887 / 10000000000000000 : ℝ)
    (cell12259 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · have h := gap_lower (n := 12259) (a := (82052715581943 / 100000000000000 : ℝ)) (b := (84049798101 / 50000000000000 : ℝ)) (q := (462056418761 / 20000000000000 : ℝ))
      (E := (cell12259 ⟨59, by decide⟩).energy) (xi := (346408376745887 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12259 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12259]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12259])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12259) (a := (82052715581943 / 100000000000000 : ℝ)) (b := (84049798101 / 50000000000000 : ℝ)) (q := (462056418761 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12259])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12259])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12259]

theorem cert12260_40 : CellCertificate 12260 (899406396600053 / 10000000000000000 : ℝ) (856634443561819 / 500000000000000000 : ℝ) (346379365836723 / 10000000000000000 : ℝ)
    (cell12260 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · have h := gap_lower (n := 12260) (a := (41348679313711 / 50000000000000 : ℝ)) (b := (42021425403 / 25000000000000 : ℝ)) (q := (115502987759 / 5000000000000 : ℝ))
      (E := (cell12260 ⟨40, by decide⟩).energy) (xi := (346379365836723 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12260 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12260]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12260])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12260) (a := (41348679313711 / 50000000000000 : ℝ)) (b := (42021425403 / 25000000000000 : ℝ)) (q := (115502987759 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12260])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12260])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12260]

theorem cert12260_41 : CellCertificate 12260 (899406396600053 / 10000000000000000 : ℝ) (856634443561819 / 500000000000000000 : ℝ) (346379365836723 / 10000000000000000 : ℝ)
    (cell12260 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · have h := gap_lower (n := 12260) (a := (41331608741991 / 50000000000000 : ℝ)) (b := (42021425403 / 25000000000000 : ℝ)) (q := (2310063763733 / 100000000000000 : ℝ))
      (E := (cell12260 ⟨41, by decide⟩).energy) (xi := (346379365836723 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12260 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12260]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12260])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12260) (a := (41331608741991 / 50000000000000 : ℝ)) (b := (42021425403 / 25000000000000 : ℝ)) (q := (2310063763733 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12260])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12260])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12260]

theorem cert12260_42 : CellCertificate 12260 (899406396600053 / 10000000000000000 : ℝ) (856634443561819 / 500000000000000000 : ℝ) (346379365836723 / 10000000000000000 : ℝ)
    (cell12260 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · have h := gap_lower (n := 12260) (a := (41314550071211 / 50000000000000 : ℝ)) (b := (42021425403 / 25000000000000 : ℝ)) (q := (1155033879937 / 50000000000000 : ℝ))
      (E := (cell12260 ⟨42, by decide⟩).energy) (xi := (346379365836723 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12260 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12260]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12260])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12260) (a := (41314550071211 / 50000000000000 : ℝ)) (b := (42021425403 / 25000000000000 : ℝ)) (q := (1155033879937 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12260])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12260])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12260]

theorem cert12260_43 : CellCertificate 12260 (899406396600053 / 10000000000000000 : ℝ) (856634443561819 / 500000000000000000 : ℝ) (346379365836723 / 10000000000000000 : ℝ)
    (cell12260 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · have h := gap_lower (n := 12260) (a := (20648751643177 / 25000000000000 : ℝ)) (b := (42021425403 / 25000000000000 : ℝ)) (q := (1155035871741 / 50000000000000 : ℝ))
      (E := (cell12260 ⟨43, by decide⟩).energy) (xi := (346379365836723 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12260 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12260]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12260])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12260) (a := (20648751643177 / 25000000000000 : ℝ)) (b := (42021425403 / 25000000000000 : ℝ)) (q := (1155035871741 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12260])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12260])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12260]

theorem cert12260_44 : CellCertificate 12260 (899406396600053 / 10000000000000000 : ℝ) (856634443561819 / 500000000000000000 : ℝ) (346379365836723 / 10000000000000000 : ℝ)
    (cell12260 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · have h := gap_lower (n := 12260) (a := (16512187348991 / 20000000000000 : ℝ)) (b := (42021425403 / 25000000000000 : ℝ)) (q := (115503785711 / 5000000000000 : ℝ))
      (E := (cell12260 ⟨44, by decide⟩).energy) (xi := (346379365836723 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12260 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12260]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12260])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12260) (a := (16512187348991 / 20000000000000 : ℝ)) (b := (42021425403 / 25000000000000 : ℝ)) (q := (115503785711 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12260])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12260])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12260]

theorem cert12260_45 : CellCertificate 12260 (899406396600053 / 10000000000000000 : ℝ) (856634443561819 / 500000000000000000 : ℝ) (346379365836723 / 10000000000000000 : ℝ)
    (cell12260 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · have h := gap_lower (n := 12260) (a := (82526890629431 / 100000000000000 : ℝ)) (b := (42021425403 / 25000000000000 : ℝ)) (q := (1155039865173 / 50000000000000 : ℝ))
      (E := (cell12260 ⟨45, by decide⟩).energy) (xi := (346379365836723 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12260 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12260]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12260])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12260) (a := (82526890629431 / 100000000000000 : ℝ)) (b := (42021425403 / 25000000000000 : ℝ)) (q := (1155039865173 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12260])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12260])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12260]

theorem cert12260_46 : CellCertificate 12260 (899406396600053 / 10000000000000000 : ℝ) (856634443561819 / 500000000000000000 : ℝ) (346379365836723 / 10000000000000000 : ℝ)
    (cell12260 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · have h := gap_lower (n := 12260) (a := (10311608524569 / 12500000000000 : ℝ)) (b := (42021425403 / 25000000000000 : ℝ)) (q := (2310083732313 / 100000000000000 : ℝ))
      (E := (cell12260 ⟨46, by decide⟩).energy) (xi := (346379365836723 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12260 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12260]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12260])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12260) (a := (10311608524569 / 12500000000000 : ℝ)) (b := (42021425403 / 25000000000000 : ℝ)) (q := (2310083732313 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12260])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12260])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12260]

theorem cert12260_47 : CellCertificate 12260 (899406396600053 / 10000000000000000 : ℝ) (856634443561819 / 500000000000000000 : ℝ) (346379365836723 / 10000000000000000 : ℝ)
    (cell12260 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · have h := gap_lower (n := 12260) (a := (16491773883377 / 20000000000000 : ℝ)) (b := (42021425403 / 25000000000000 : ℝ)) (q := (577521929781 / 25000000000000 : ℝ))
      (E := (cell12260 ⟨47, by decide⟩).energy) (xi := (346379365836723 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12260 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12260]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12260])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12260) (a := (16491773883377 / 20000000000000 : ℝ)) (b := (42021425403 / 25000000000000 : ℝ)) (q := (577521929781 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12260])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12260])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12260]

theorem cert12260_48 : CellCertificate 12260 (899406396600053 / 10000000000000000 : ℝ) (856634443561819 / 500000000000000000 : ℝ) (346379365836723 / 10000000000000000 : ℝ)
    (cell12260 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · have h := gap_lower (n := 12260) (a := (41212447130573 / 50000000000000 : ℝ)) (b := (42021425403 / 25000000000000 : ℝ)) (q := (2310091689567 / 100000000000000 : ℝ))
      (E := (cell12260 ⟨48, by decide⟩).energy) (xi := (346379365836723 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12260 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12260]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12260])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12260) (a := (41212447130573 / 50000000000000 : ℝ)) (b := (42021425403 / 25000000000000 : ℝ)) (q := (2310091689567 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12260])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12260])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12260]

theorem cert12260_49 : CellCertificate 12260 (899406396600053 / 10000000000000000 : ℝ) (856634443561819 / 500000000000000000 : ℝ) (346379365836723 / 10000000000000000 : ℝ)
    (cell12260 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · have h := gap_lower (n := 12260) (a := (41195471350099 / 50000000000000 : ℝ)) (b := (42021425403 / 25000000000000 : ℝ)) (q := (288761962641 / 12500000000000 : ℝ))
      (E := (cell12260 ⟨49, by decide⟩).energy) (xi := (346379365836723 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12260 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12260]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12260])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12260) (a := (41195471350099 / 50000000000000 : ℝ)) (b := (42021425403 / 25000000000000 : ℝ)) (q := (288761962641 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12260])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12260])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12260]

theorem cert12260_50 : CellCertificate 12260 (899406396600053 / 10000000000000000 : ℝ) (856634443561819 / 500000000000000000 : ℝ) (346379365836723 / 10000000000000000 : ℝ)
    (cell12260 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · have h := gap_lower (n := 12260) (a := (82357014705049 / 100000000000000 : ℝ)) (b := (42021425403 / 25000000000000 : ℝ)) (q := (2310099693297 / 100000000000000 : ℝ))
      (E := (cell12260 ⟨50, by decide⟩).energy) (xi := (346379365836723 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12260 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12260]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12260])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12260) (a := (82357014705049 / 100000000000000 : ℝ)) (b := (42021425403 / 25000000000000 : ℝ)) (q := (2310099693297 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12260])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12260])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12260]

theorem cert12260_51 : CellCertificate 12260 (899406396600053 / 10000000000000000 : ℝ) (856634443561819 / 500000000000000000 : ℝ) (346379365836723 / 10000000000000000 : ℝ)
    (cell12260 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · have h := gap_lower (n := 12260) (a := (10290388780857 / 12500000000000 : ℝ)) (b := (42021425403 / 25000000000000 : ℝ)) (q := (288762965397 / 12500000000000 : ℝ))
      (E := (cell12260 ⟨51, by decide⟩).energy) (xi := (346379365836723 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12260 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12260]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12260])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12260) (a := (10290388780857 / 12500000000000 : ℝ)) (b := (42021425403 / 25000000000000 : ℝ)) (q := (288762965397 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12260])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12260])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12260]

theorem cert12260_52 : CellCertificate 12260 (899406396600053 / 10000000000000000 : ℝ) (856634443561819 / 500000000000000000 : ℝ) (346379365836723 / 10000000000000000 : ℝ)
    (cell12260 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · have h := gap_lower (n := 12260) (a := (82289229296917 / 100000000000000 : ℝ)) (b := (42021425403 / 25000000000000 : ℝ)) (q := (577526917699 / 25000000000000 : ℝ))
      (E := (cell12260 ⟨52, by decide⟩).energy) (xi := (346379365836723 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12260 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12260]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12260])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12260) (a := (82289229296917 / 100000000000000 : ℝ)) (b := (42021425403 / 25000000000000 : ℝ)) (q := (577526917699 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12260])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12260])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12260]

theorem cert12260_53 : CellCertificate 12260 (899406396600053 / 10000000000000000 : ℝ) (856634443561819 / 500000000000000000 : ℝ) (346379365836723 / 10000000000000000 : ℝ)
    (cell12260 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · have h := gap_lower (n := 12260) (a := (82255371826679 / 100000000000000 : ℝ)) (b := (42021425403 / 25000000000000 : ℝ)) (q := (288763963853 / 12500000000000 : ℝ))
      (E := (cell12260 ⟨53, by decide⟩).energy) (xi := (346379365836723 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12260 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12260]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12260])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12260) (a := (82255371826679 / 100000000000000 : ℝ)) (b := (42021425403 / 25000000000000 : ℝ)) (q := (288763963853 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12260])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12260])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12260]

theorem cert12260_54 : CellCertificate 12260 (899406396600053 / 10000000000000000 : ℝ) (856634443561819 / 500000000000000000 : ℝ) (346379365836723 / 10000000000000000 : ℝ)
    (cell12260 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · have h := gap_lower (n := 12260) (a := (5138846112983 / 6250000000000 : ℝ)) (b := (42021425403 / 25000000000000 : ℝ)) (q := (577528915953 / 25000000000000 : ℝ))
      (E := (cell12260 ⟨54, by decide⟩).energy) (xi := (346379365836723 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12260 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12260]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12260])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12260) (a := (5138846112983 / 6250000000000 : ℝ)) (b := (42021425403 / 25000000000000 : ℝ)) (q := (577528915953 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12260])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12260])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12260]

theorem cert12260_55 : CellCertificate 12260 (899406396600053 / 10000000000000000 : ℝ) (856634443561819 / 500000000000000000 : ℝ) (346379365836723 / 10000000000000000 : ℝ)
    (cell12260 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · have h := gap_lower (n := 12260) (a := (16437545442359 / 20000000000000 : ℝ)) (b := (42021425403 / 25000000000000 : ℝ)) (q := (462023940829 / 20000000000000 : ℝ))
      (E := (cell12260 ⟨55, by decide⟩).energy) (xi := (346379365836723 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12260 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12260]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12260])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12260) (a := (16437545442359 / 20000000000000 : ℝ)) (b := (42021425403 / 25000000000000 : ℝ)) (q := (462023940829 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12260])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12260])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12260]

theorem cert12260_56 : CellCertificate 12260 (899406396600053 / 10000000000000000 : ℝ) (856634443561819 / 500000000000000000 : ℝ) (346379365836723 / 10000000000000000 : ℝ)
    (cell12260 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · have h := gap_lower (n := 12260) (a := (82153940010751 / 100000000000000 : ℝ)) (b := (42021425403 / 25000000000000 : ℝ)) (q := (2310123651811 / 100000000000000 : ℝ))
      (E := (cell12260 ⟨56, by decide⟩).energy) (xi := (346379365836723 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12260 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12260]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12260])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12260) (a := (82153940010751 / 100000000000000 : ℝ)) (b := (42021425403 / 25000000000000 : ℝ)) (q := (2310123651811 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12260])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12260])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12260]

theorem cert12260_57 : CellCertificate 12260 (899406396600053 / 10000000000000000 : ℝ) (856634443561819 / 500000000000000000 : ℝ) (346379365836723 / 10000000000000000 : ℝ)
    (cell12260 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · have h := gap_lower (n := 12260) (a := (82120176176611 / 100000000000000 : ℝ)) (b := (42021425403 / 25000000000000 : ℝ)) (q := (577531920229 / 25000000000000 : ℝ))
      (E := (cell12260 ⟨57, by decide⟩).energy) (xi := (346379365836723 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12260 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12260]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12260])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12260) (a := (82120176176611 / 100000000000000 : ℝ)) (b := (42021425403 / 25000000000000 : ℝ)) (q := (577531920229 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12260])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12260])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12260]

theorem cert12260_58 : CellCertificate 12260 (899406396600053 / 10000000000000000 : ℝ) (856634443561819 / 500000000000000000 : ℝ) (346379365836723 / 10000000000000000 : ℝ)
    (cell12260 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · have h := gap_lower (n := 12260) (a := (3283457427261 / 4000000000000 : ℝ)) (b := (42021425403 / 25000000000000 : ℝ)) (q := (462026334003 / 20000000000000 : ℝ))
      (E := (cell12260 ⟨58, by decide⟩).energy) (xi := (346379365836723 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12260 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12260]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12260])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12260) (a := (3283457427261 / 4000000000000 : ℝ)) (b := (42021425403 / 25000000000000 : ℝ)) (q := (462026334003 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12260])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12260])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12260]

theorem cert12260_59 : CellCertificate 12260 (899406396600053 / 10000000000000000 : ℝ) (856634443561819 / 500000000000000000 : ℝ) (346379365836723 / 10000000000000000 : ℝ)
    (cell12260 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · have h := gap_lower (n := 12260) (a := (20513179624447 / 25000000000000 : ℝ)) (b := (42021425403 / 25000000000000 : ℝ)) (q := (2310135674707 / 100000000000000 : ℝ))
      (E := (cell12260 ⟨59, by decide⟩).energy) (xi := (346379365836723 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12260 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12260]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12260])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12260) (a := (20513179624447 / 25000000000000 : ℝ)) (b := (42021425403 / 25000000000000 : ℝ)) (q := (2310135674707 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12260])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12260])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12260]

theorem cert12261_40 : CellCertificate 12261 (899376501539603 / 10000000000000000 : ℝ) (1713129106326101 / 1000000000000000000 : ℝ) (173175179955013 / 5000000000000000 : ℝ)
    (cell12261 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · have h := gap_lower (n := 12261) (a := (20674338886783 / 25000000000000 : ℝ)) (b := (168071809349 / 100000000000000 : ℝ)) (q := (230991335901 / 10000000000000 : ℝ))
      (E := (cell12261 ⟨40, by decide⟩).energy) (xi := (173175179955013 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12261 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12261]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12261])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12261) (a := (20674338886783 / 25000000000000 : ℝ)) (b := (168071809349 / 100000000000000 : ℝ)) (q := (230991335901 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12261])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12261])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12261]

theorem cert12261_41 : CellCertificate 12261 (899376501539603 / 10000000000000000 : ℝ) (1713129106326101 / 1000000000000000000 : ℝ) (173175179955013 / 5000000000000000 : ℝ)
    (cell12261 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · have h := gap_lower (n := 12261) (a := (41331607361617 / 50000000000000 : ℝ)) (b := (168071809349 / 100000000000000 : ℝ)) (q := (1443698371 / 62500000000 : ℝ))
      (E := (cell12261 ⟨41, by decide⟩).energy) (xi := (173175179955013 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12261 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12261]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12261])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12261) (a := (41331607361617 / 50000000000000 : ℝ)) (b := (168071809349 / 100000000000000 : ℝ)) (q := (1443698371 / 62500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12261])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12261])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12261]

theorem cert12261_42 : CellCertificate 12261 (899376501539603 / 10000000000000000 : ℝ) (1713129106326101 / 1000000000000000000 : ℝ) (173175179955013 / 5000000000000000 : ℝ)
    (cell12261 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · have h := gap_lower (n := 12261) (a := (41314548850387 / 50000000000000 : ℝ)) (b := (168071809349 / 100000000000000 : ℝ)) (q := (1154960678897 / 50000000000000 : ℝ))
      (E := (cell12261 ⟨42, by decide⟩).energy) (xi := (173175179955013 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12261 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12261]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12261])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12261) (a := (41314548850387 / 50000000000000 : ℝ)) (b := (168071809349 / 100000000000000 : ℝ)) (q := (1154960678897 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12261])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12261])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12261]

theorem cert12261_43 : CellCertificate 12261 (899376501539603 / 10000000000000000 : ℝ) (1713129106326101 / 1000000000000000000 : ℝ) (173175179955013 / 5000000000000000 : ℝ)
    (cell12261 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · have h := gap_lower (n := 12261) (a := (41297502224859 / 50000000000000 : ℝ)) (b := (168071809349 / 100000000000000 : ℝ)) (q := (1154962684473 / 50000000000000 : ℝ))
      (E := (cell12261 ⟨43, by decide⟩).energy) (xi := (173175179955013 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12261 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12261]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12261])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12261) (a := (41297502224859 / 50000000000000 : ℝ)) (b := (168071809349 / 100000000000000 : ℝ)) (q := (1154962684473 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12261])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12261])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12261]

theorem cert12261_44 : CellCertificate 12261 (899376501539603 / 10000000000000000 : ℝ) (1713129106326101 / 1000000000000000000 : ℝ) (173175179955013 / 5000000000000000 : ℝ)
    (cell12261 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · have h := gap_lower (n := 12261) (a := (82560934940181 / 100000000000000 : ℝ)) (b := (168071809349 / 100000000000000 : ℝ)) (q := (288741170999 / 12500000000000 : ℝ))
      (E := (cell12261 ⟨44, by decide⟩).energy) (xi := (173175179955013 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12261 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12261]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12261])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12261) (a := (82560934940181 / 100000000000000 : ℝ)) (b := (168071809349 / 100000000000000 : ℝ)) (q := (288741170999 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12261])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12261])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12261]

theorem cert12261_45 : CellCertificate 12261 (899376501539603 / 10000000000000000 : ℝ) (1713129106326101 / 1000000000000000000 : ℝ) (173175179955013 / 5000000000000000 : ℝ)
    (cell12261 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · have h := gap_lower (n := 12261) (a := (82526889142433 / 100000000000000 : ℝ)) (b := (168071809349 / 100000000000000 : ℝ)) (q := (2309933354369 / 100000000000000 : ℝ))
      (E := (cell12261 ⟨45, by decide⟩).energy) (xi := (173175179955013 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12261 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12261]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12261])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12261) (a := (82526889142433 / 100000000000000 : ℝ)) (b := (168071809349 / 100000000000000 : ℝ)) (q := (2309933354369 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12261])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12261])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12261]

theorem cert12261_46 : CellCertificate 12261 (899376501539603 / 10000000000000000 : ℝ) (1713129106326101 / 1000000000000000000 : ℝ) (173175179955013 / 5000000000000000 : ℝ)
    (cell12261 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · have h := gap_lower (n := 12261) (a := (82492867026891 / 100000000000000 : ℝ)) (b := (168071809349 / 100000000000000 : ℝ)) (q := (461987477229 / 20000000000000 : ℝ))
      (E := (cell12261 ⟨46, by decide⟩).energy) (xi := (173175179955013 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12261 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12261]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12261])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12261) (a := (82492867026891 / 100000000000000 : ℝ)) (b := (168071809349 / 100000000000000 : ℝ)) (q := (461987477229 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12261])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12261])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12261]

theorem cert12261_47 : CellCertificate 12261 (899376501539603 / 10000000000000000 : ℝ) (1713129106326101 / 1000000000000000000 : ℝ) (173175179955013 / 5000000000000000 : ℝ)
    (cell12261 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · have h := gap_lower (n := 12261) (a := (82458868564123 / 100000000000000 : ℝ)) (b := (168071809349 / 100000000000000 : ℝ)) (q := (115497067233 / 5000000000000 : ℝ))
      (E := (cell12261 ⟨47, by decide⟩).energy) (xi := (173175179955013 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12261 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12261]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12261])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12261) (a := (82458868564123 / 100000000000000 : ℝ)) (b := (168071809349 / 100000000000000 : ℝ)) (q := (115497067233 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12261])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12261])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12261]

theorem cert12261_48 : CellCertificate 12261 (899376501539603 / 10000000000000000 : ℝ) (1713129106326101 / 1000000000000000000 : ℝ) (173175179955013 / 5000000000000000 : ℝ)
    (cell12261 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · have h := gap_lower (n := 12261) (a := (16484978744969 / 20000000000000 : ℝ)) (b := (168071809349 / 100000000000000 : ℝ)) (q := (2309945346411 / 100000000000000 : ℝ))
      (E := (cell12261 ⟨48, by decide⟩).energy) (xi := (173175179955013 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12261 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12261]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12261])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12261) (a := (16484978744969 / 20000000000000 : ℝ)) (b := (168071809349 / 100000000000000 : ℝ)) (q := (2309945346411 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12261])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12261])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12261]

theorem cert12261_49 : CellCertificate 12261 (899376501539603 / 10000000000000000 : ℝ) (1713129106326101 / 1000000000000000000 : ℝ) (173175179955013 / 5000000000000000 : ℝ)
    (cell12261 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · have h := gap_lower (n := 12261) (a := (1029886780999 / 1250000000000 : ℝ)) (b := (168071809349 / 100000000000000 : ℝ)) (q := (1154974665563 / 50000000000000 : ℝ))
      (E := (cell12261 ⟨49, by decide⟩).energy) (xi := (173175179955013 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12261 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12261]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12261])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12261) (a := (1029886780999 / 1250000000000 : ℝ)) (b := (168071809349 / 100000000000000 : ℝ)) (q := (1154974665563 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12261])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12261])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12261]

theorem cert12261_50 : CellCertificate 12261 (899376501539603 / 10000000000000000 : ℝ) (1713129106326101 / 1000000000000000000 : ℝ) (173175179955013 / 5000000000000000 : ℝ)
    (cell12261 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · have h := gap_lower (n := 12261) (a := (82357014800359 / 100000000000000 : ℝ)) (b := (168071809349 / 100000000000000 : ℝ)) (q := (1154976678049 / 50000000000000 : ℝ))
      (E := (cell12261 ⟨50, by decide⟩).energy) (xi := (173175179955013 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12261 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12261]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12261])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12261) (a := (82357014800359 / 100000000000000 : ℝ)) (b := (168071809349 / 100000000000000 : ℝ)) (q := (1154976678049 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12261])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12261])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12261]

theorem cert12261_51 : CellCertificate 12261 (899376501539603 / 10000000000000000 : ℝ) (1713129106326101 / 1000000000000000000 : ℝ) (173175179955013 / 5000000000000000 : ℝ)
    (cell12261 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · have h := gap_lower (n := 12261) (a := (82323110657317 / 100000000000000 : ℝ)) (b := (168071809349 / 100000000000000 : ℝ)) (q := (2309957360579 / 100000000000000 : ℝ))
      (E := (cell12261 ⟨51, by decide⟩).energy) (xi := (173175179955013 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12261 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12261]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12261])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12261) (a := (82323110657317 / 100000000000000 : ℝ)) (b := (168071809349 / 100000000000000 : ℝ)) (q := (2309957360579 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12261])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12261])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12261]

theorem cert12261_52 : CellCertificate 12261 (899376501539603 / 10000000000000000 : ℝ) (1713129106326101 / 1000000000000000000 : ℝ) (173175179955013 / 5000000000000000 : ℝ)
    (cell12261 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · have h := gap_lower (n := 12261) (a := (5143076876381 / 6250000000000 : ℝ)) (b := (168071809349 / 100000000000000 : ℝ)) (q := (1154980671247 / 50000000000000 : ℝ))
      (E := (cell12261 ⟨52, by decide⟩).energy) (xi := (173175179955013 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12261 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12261]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12261])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12261) (a := (5143076876381 / 6250000000000 : ℝ)) (b := (168071809349 / 100000000000000 : ℝ)) (q := (1154980671247 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12261])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12261])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12261]

theorem cert12261_53 : CellCertificate 12261 (899376501539603 / 10000000000000000 : ℝ) (1713129106326101 / 1000000000000000000 : ℝ) (173175179955013 / 5000000000000000 : ℝ)
    (cell12261 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · have h := gap_lower (n := 12261) (a := (82255372866141 / 100000000000000 : ℝ)) (b := (168071809349 / 100000000000000 : ℝ)) (q := (2309965358569 / 100000000000000 : ℝ))
      (E := (cell12261 ⟨53, by decide⟩).energy) (xi := (173175179955013 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12261 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12261]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12261])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12261) (a := (82255372866141 / 100000000000000 : ℝ)) (b := (168071809349 / 100000000000000 : ℝ)) (q := (2309965358569 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12261])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12261])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12261]

theorem cert12261_54 : CellCertificate 12261 (899376501539603 / 10000000000000000 : ℝ) (1713129106326101 / 1000000000000000000 : ℝ) (173175179955013 / 5000000000000000 : ℝ)
    (cell12261 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · have h := gap_lower (n := 12261) (a := (1027769239513 / 1250000000000 : ℝ)) (b := (168071809349 / 100000000000000 : ℝ)) (q := (2309969347343 / 100000000000000 : ℝ))
      (E := (cell12261 ⟨54, by decide⟩).energy) (xi := (173175179955013 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12261 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12261]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12261])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12261) (a := (1027769239513 / 1250000000000 : ℝ)) (b := (168071809349 / 100000000000000 : ℝ)) (q := (2309969347343 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12261])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12261])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12261]

theorem cert12261_55 : CellCertificate 12261 (899376501539603 / 10000000000000000 : ℝ) (1713129106326101 / 1000000000000000000 : ℝ) (173175179955013 / 5000000000000000 : ℝ)
    (cell12261 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · have h := gap_lower (n := 12261) (a := (20546932219631 / 25000000000000 : ℝ)) (b := (168071809349 / 100000000000000 : ℝ)) (q := (577493326527 / 25000000000000 : ℝ))
      (E := (cell12261 ⟨55, by decide⟩).energy) (xi := (173175179955013 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12261 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12261]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12261])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12261) (a := (20546932219631 / 25000000000000 : ℝ)) (b := (168071809349 / 100000000000000 : ℝ)) (q := (577493326527 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12261])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12261])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12261]

theorem cert12261_56 : CellCertificate 12261 (899376501539603 / 10000000000000000 : ℝ) (1713129106326101 / 1000000000000000000 : ℝ) (173175179955013 / 5000000000000000 : ℝ)
    (cell12261 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · have h := gap_lower (n := 12261) (a := (41076970995233 / 50000000000000 : ℝ)) (b := (168071809349 / 100000000000000 : ℝ)) (q := (288747168763 / 12500000000000 : ℝ))
      (E := (cell12261 ⟨56, by decide⟩).energy) (xi := (173175179955013 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12261 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12261]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12261])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12261) (a := (41076970995233 / 50000000000000 : ℝ)) (b := (168071809349 / 100000000000000 : ℝ)) (q := (288747168763 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12261])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12261])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12261]

theorem cert12261_57 : CellCertificate 12261 (899376501539603 / 10000000000000000 : ℝ) (1713129106326101 / 1000000000000000000 : ℝ) (173175179955013 / 5000000000000000 : ℝ)
    (cell12261 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · have h := gap_lower (n := 12261) (a := (1026502230861 / 1250000000000 : ℝ)) (b := (168071809349 / 100000000000000 : ℝ)) (q := (288747662379 / 12500000000000 : ℝ))
      (E := (cell12261 ⟨57, by decide⟩).energy) (xi := (173175179955013 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12261 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12261]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12261])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12261) (a := (1026502230861 / 1250000000000 : ℝ)) (b := (168071809349 / 100000000000000 : ℝ)) (q := (288747662379 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12261])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12261])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12261]

theorem cert12261_58 : CellCertificate 12261 (899376501539603 / 10000000000000000 : ℝ) (1713129106326101 / 1000000000000000000 : ℝ) (173175179955013 / 5000000000000000 : ℝ)
    (cell12261 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · have h := gap_lower (n := 12261) (a := (82086438285919 / 100000000000000 : ℝ)) (b := (168071809349 / 100000000000000 : ℝ)) (q := (461997065373 / 20000000000000 : ℝ))
      (E := (cell12261 ⟨58, by decide⟩).energy) (xi := (173175179955013 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12261 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12261]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12261])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12261) (a := (82086438285919 / 100000000000000 : ℝ)) (b := (168071809349 / 100000000000000 : ℝ)) (q := (461997065373 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12261])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12261])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12261]

theorem cert12261_59 : CellCertificate 12261 (899376501539603 / 10000000000000000 : ℝ) (1713129106326101 / 1000000000000000000 : ℝ) (173175179955013 / 5000000000000000 : ℝ)
    (cell12261 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · have h := gap_lower (n := 12261) (a := (20513180353469 / 25000000000000 : ℝ)) (b := (168071809349 / 100000000000000 : ℝ)) (q := (288748663987 / 12500000000000 : ℝ))
      (E := (cell12261 ⟨59, by decide⟩).energy) (xi := (173175179955013 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12261 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12261]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12261])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12261) (a := (20513180353469 / 25000000000000 : ℝ)) (b := (168071809349 / 100000000000000 : ℝ)) (q := (288748663987 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12261])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12261])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12261]

theorem cert12262_40 : CellCertificate 12262 (449673305588693 / 5000000000000000 : ℝ) (856494674167673 / 500000000000000000 : ℝ) (346321358964341 / 10000000000000000 : ℝ)
    (cell12262 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · have h := gap_lower (n := 12262) (a := (41348676233919 / 50000000000000 : ℝ)) (b := (42014479853 / 25000000000000 : ℝ)) (q := (144360445957 / 6250000000000 : ℝ))
      (E := (cell12262 ⟨40, by decide⟩).energy) (xi := (346321358964341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12262 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12262]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12262])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12262) (a := (41348676233919 / 50000000000000 : ℝ)) (b := (42014479853 / 25000000000000 : ℝ)) (q := (144360445957 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12262])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12262])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12262]

theorem cert12262_41 : CellCertificate 12262 (449673305588693 / 5000000000000000 : ℝ) (856494674167673 / 500000000000000000 : ℝ) (346321358964341 / 10000000000000000 : ℝ)
    (cell12262 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · have h := gap_lower (n := 12262) (a := (41331605981721 / 50000000000000 : ℝ)) (b := (42014479853 / 25000000000000 : ℝ)) (q := (1154885568663 / 50000000000000 : ℝ))
      (E := (cell12262 ⟨41, by decide⟩).energy) (xi := (346321358964341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12262 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12262]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12262])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12262) (a := (41331605981721 / 50000000000000 : ℝ)) (b := (42014479853 / 25000000000000 : ℝ)) (q := (1154885568663 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12262])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12262])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12262]

theorem cert12262_42 : CellCertificate 12262 (449673305588693 / 5000000000000000 : ℝ) (856494674167673 / 500000000000000000 : ℝ) (346321358964341 / 10000000000000000 : ℝ)
    (cell12262 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · have h := gap_lower (n := 12262) (a := (82629095260041 / 100000000000000 : ℝ)) (b := (42014479853 / 25000000000000 : ℝ)) (q := (2309775128411 / 100000000000000 : ℝ))
      (E := (cell12262 ⟨42, by decide⟩).energy) (xi := (346321358964341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12262 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12262]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12262])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12262) (a := (82629095260041 / 100000000000000 : ℝ)) (b := (42014479853 / 25000000000000 : ℝ)) (q := (2309775128411 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12262])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12262])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12262]

theorem cert12262_43 : CellCertificate 12262 (449673305588693 / 5000000000000000 : ℝ) (856494674167673 / 500000000000000000 : ℝ) (346321358964341 / 10000000000000000 : ℝ)
    (cell12262 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · have h := gap_lower (n := 12262) (a := (82595002327603 / 100000000000000 : ℝ)) (b := (42014479853 / 25000000000000 : ℝ)) (q := (461955821689 / 20000000000000 : ℝ))
      (E := (cell12262 ⟨43, by decide⟩).energy) (xi := (346321358964341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12262 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12262]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12262])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12262) (a := (82595002327603 / 100000000000000 : ℝ)) (b := (42014479853 / 25000000000000 : ℝ)) (q := (461955821689 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12262])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12262])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12262]

theorem cert12262_44 : CellCertificate 12262 (449673305588693 / 5000000000000000 : ℝ) (856494674167673 / 500000000000000000 : ℝ) (346321358964341 / 10000000000000000 : ℝ)
    (cell12262 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · have h := gap_lower (n := 12262) (a := (82560933136243 / 100000000000000 : ℝ)) (b := (42014479853 / 25000000000000 : ℝ)) (q := (2309783077089 / 100000000000000 : ℝ))
      (E := (cell12262 ⟨44, by decide⟩).energy) (xi := (346321358964341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12262 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12262]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12262])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12262) (a := (82560933136243 / 100000000000000 : ℝ)) (b := (42014479853 / 25000000000000 : ℝ)) (q := (2309783077089 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12262])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12262])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12262]

theorem cert12262_45 : CellCertificate 12262 (449673305588693 / 5000000000000000 : ℝ) (856494674167673 / 500000000000000000 : ℝ) (346321358964341 / 10000000000000000 : ℝ)
    (cell12262 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · have h := gap_lower (n := 12262) (a := (82526887656231 / 100000000000000 : ℝ)) (b := (42014479853 / 25000000000000 : ℝ)) (q := (2309787092603 / 100000000000000 : ℝ))
      (E := (cell12262 ⟨45, by decide⟩).energy) (xi := (346321358964341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12262 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12262]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12262])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12262) (a := (82526887656231 / 100000000000000 : ℝ)) (b := (42014479853 / 25000000000000 : ℝ)) (q := (2309787092603 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12262])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12262])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12262]

theorem cert12262_46 : CellCertificate 12262 (449673305588693 / 5000000000000000 : ℝ) (856494674167673 / 500000000000000000 : ℝ) (346321358964341 / 10000000000000000 : ℝ)
    (cell12262 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · have h := gap_lower (n := 12262) (a := (82492865857987 / 100000000000000 : ℝ)) (b := (42014479853 / 25000000000000 : ℝ)) (q := (288723886929 / 12500000000000 : ℝ))
      (E := (cell12262 ⟨46, by decide⟩).energy) (xi := (346321358964341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12262 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12262]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12262])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12262) (a := (82492865857987 / 100000000000000 : ℝ)) (b := (42014479853 / 25000000000000 : ℝ)) (q := (288723886929 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12262])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12262])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12262]

theorem cert12262_47 : CellCertificate 12262 (449673305588693 / 5000000000000000 : ℝ) (856494674167673 / 500000000000000000 : ℝ) (346321358964341 / 10000000000000000 : ℝ)
    (cell12262 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · have h := gap_lower (n := 12262) (a := (41229433856039 / 50000000000000 : ℝ)) (b := (42014479853 / 25000000000000 : ℝ)) (q := (2309795084581 / 100000000000000 : ℝ))
      (E := (cell12262 ⟨47, by decide⟩).energy) (xi := (346321358964341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12262 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12262]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12262])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12262) (a := (41229433856039 / 50000000000000 : ℝ)) (b := (42014479853 / 25000000000000 : ℝ)) (q := (2309795084581 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12262])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12262])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12262]

theorem cert12262_48 : CellCertificate 12262 (449673305588693 / 5000000000000000 : ℝ) (856494674167673 / 500000000000000000 : ℝ) (346321358964341 / 10000000000000000 : ℝ)
    (cell12262 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · have h := gap_lower (n := 12262) (a := (4121244659461 / 5000000000000 : ℝ)) (b := (42014479853 / 25000000000000 : ℝ)) (q := (2309799058839 / 100000000000000 : ℝ))
      (E := (cell12262 ⟨48, by decide⟩).energy) (xi := (346321358964341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12262 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12262]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12262])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12262) (a := (4121244659461 / 5000000000000 : ℝ)) (b := (42014479853 / 25000000000000 : ℝ)) (q := (2309799058839 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12262])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12262])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12262]

theorem cert12262_49 : CellCertificate 12262 (449673305588693 / 5000000000000000 : ℝ) (856494674167673 / 500000000000000000 : ℝ) (346321358964341 / 10000000000000000 : ℝ)
    (cell12262 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · have h := gap_lower (n := 12262) (a := (2059773556507 / 2500000000000 : ℝ)) (b := (42014479853 / 25000000000000 : ℝ)) (q := (461960615137 / 20000000000000 : ℝ))
      (E := (cell12262 ⟨49, by decide⟩).energy) (xi := (346321358964341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12262 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12262]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12262])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12262) (a := (2059773556507 / 2500000000000 : ℝ)) (b := (42014479853 / 25000000000000 : ℝ)) (q := (461960615137 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12262])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12262])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12262]

theorem cert12262_50 : CellCertificate 12262 (449673305588693 / 5000000000000000 : ℝ) (856494674167673 / 500000000000000000 : ℝ) (346321358964341 / 10000000000000000 : ℝ)
    (cell12262 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · have h := gap_lower (n := 12262) (a := (41178507448133 / 50000000000000 : ℝ)) (b := (42014479853 / 25000000000000 : ℝ)) (q := (577451768653 / 25000000000000 : ℝ))
      (E := (cell12262 ⟨50, by decide⟩).energy) (xi := (346321358964341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12262 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12262]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12262])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12262) (a := (41178507448133 / 50000000000000 : ℝ)) (b := (42014479853 / 25000000000000 : ℝ)) (q := (577451768653 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12262])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12262])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12262]

theorem cert12262_51 : CellCertificate 12262 (449673305588693 / 5000000000000000 : ℝ) (856494674167673 / 500000000000000000 : ℝ) (346321358964341 / 10000000000000000 : ℝ)
    (cell12262 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · have h := gap_lower (n := 12262) (a := (82323111068337 / 100000000000000 : ℝ)) (b := (42014479853 / 25000000000000 : ℝ)) (q := (2309811053757 / 100000000000000 : ℝ))
      (E := (cell12262 ⟨51, by decide⟩).energy) (xi := (346321358964341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12262 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12262]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12262])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12262) (a := (82323111068337 / 100000000000000 : ℝ)) (b := (42014479853 / 25000000000000 : ℝ)) (q := (2309811053757 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12262])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12262])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12262]

theorem cert12262_52 : CellCertificate 12262 (449673305588693 / 5000000000000000 : ℝ) (856494674167673 / 500000000000000000 : ℝ) (346321358964341 / 10000000000000000 : ℝ)
    (cell12262 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · have h := gap_lower (n := 12262) (a := (82289230747793 / 100000000000000 : ℝ)) (b := (42014479853 / 25000000000000 : ℝ)) (q := (1154907535017 / 50000000000000 : ℝ))
      (E := (cell12262 ⟨52, by decide⟩).energy) (xi := (346321358964341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12262 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12262]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12262])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12262) (a := (82289230747793 / 100000000000000 : ℝ)) (b := (42014479853 / 25000000000000 : ℝ)) (q := (1154907535017 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12262])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12262])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12262]

theorem cert12262_53 : CellCertificate 12262 (449673305588693 / 5000000000000000 : ℝ) (856494674167673 / 500000000000000000 : ℝ) (346321358964341 / 10000000000000000 : ℝ)
    (cell12262 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · have h := gap_lower (n := 12262) (a := (82255373906081 / 100000000000000 : ℝ)) (b := (42014479853 / 25000000000000 : ℝ)) (q := (2309819062219 / 100000000000000 : ℝ))
      (E := (cell12262 ⟨53, by decide⟩).energy) (xi := (346321358964341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12262 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12262]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12262])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12262) (a := (82255373906081 / 100000000000000 : ℝ)) (b := (42014479853 / 25000000000000 : ℝ)) (q := (2309819062219 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12262])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12262])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12262]

theorem cert12262_54 : CellCertificate 12262 (449673305588693 / 5000000000000000 : ℝ) (856494674167673 / 500000000000000000 : ℝ) (346321358964341 / 10000000000000000 : ℝ)
    (cell12262 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · have h := gap_lower (n := 12262) (a := (82221540514791 / 100000000000000 : ℝ)) (b := (42014479853 / 25000000000000 : ℝ)) (q := (577455771711 / 25000000000000 : ℝ))
      (E := (cell12262 ⟨54, by decide⟩).energy) (xi := (346321358964341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12262 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12262]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12262])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12262) (a := (82221540514791 / 100000000000000 : ℝ)) (b := (42014479853 / 25000000000000 : ℝ)) (q := (577455771711 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12262])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12262])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12262]

theorem cert12262_55 : CellCertificate 12262 (449673305588693 / 5000000000000000 : ℝ) (856494674167673 / 500000000000000000 : ℝ) (346321358964341 / 10000000000000000 : ℝ)
    (cell12262 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · have h := gap_lower (n := 12262) (a := (82187730545653 / 100000000000000 : ℝ)) (b := (42014479853 / 25000000000000 : ℝ)) (q := (288728385277 / 12500000000000 : ℝ))
      (E := (cell12262 ⟨55, by decide⟩).energy) (xi := (346321358964341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12262 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12262]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12262])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12262) (a := (82187730545653 / 100000000000000 : ℝ)) (b := (42014479853 / 25000000000000 : ℝ)) (q := (288728385277 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12262])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12262])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12262]

theorem cert12262_56 : CellCertificate 12262 (449673305588693 / 5000000000000000 : ℝ) (856494674167673 / 500000000000000000 : ℝ) (346321358964341 / 10000000000000000 : ℝ)
    (cell12262 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · have h := gap_lower (n := 12262) (a := (41076971985271 / 50000000000000 : ℝ)) (b := (42014479853 / 25000000000000 : ℝ)) (q := (2309831045413 / 100000000000000 : ℝ))
      (E := (cell12262 ⟨56, by decide⟩).energy) (xi := (346321358964341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12262 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12262]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12262])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12262) (a := (41076971985271 / 50000000000000 : ℝ)) (b := (42014479853 / 25000000000000 : ℝ)) (q := (2309831045413 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12262])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12262])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12262]

theorem cert12262_57 : CellCertificate 12262 (449673305588693 / 5000000000000000 : ℝ) (856494674167673 / 500000000000000000 : ℝ) (346321358964341 / 10000000000000000 : ℝ)
    (cell12262 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · have h := gap_lower (n := 12262) (a := (82120180761471 / 100000000000000 : ℝ)) (b := (42014479853 / 25000000000000 : ℝ)) (q := (2309835032411 / 100000000000000 : ℝ))
      (E := (cell12262 ⟨57, by decide⟩).energy) (xi := (346321358964341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12262 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12262]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12262])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12262) (a := (82120180761471 / 100000000000000 : ℝ)) (b := (42014479853 / 25000000000000 : ℝ)) (q := (2309835032411 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12262])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12262])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12262]

theorem cert12262_58 : CellCertificate 12262 (449673305588693 / 5000000000000000 : ℝ) (856494674167673 / 500000000000000000 : ℝ) (346321358964341 / 10000000000000000 : ℝ)
    (cell12262 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · have h := gap_lower (n := 12262) (a := (16417288178119 / 20000000000000 : ℝ)) (b := (42014479853 / 25000000000000 : ℝ)) (q := (115491951997 / 5000000000000 : ℝ))
      (E := (cell12262 ⟨58, by decide⟩).energy) (xi := (346321358964341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12262 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12262]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12262])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12262) (a := (16417288178119 / 20000000000000 : ℝ)) (b := (42014479853 / 25000000000000 : ℝ)) (q := (115491951997 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12262])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12262])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12262]

theorem cert12262_59 : CellCertificate 12262 (449673305588693 / 5000000000000000 : ℝ) (856494674167673 / 500000000000000000 : ℝ) (346321358964341 / 10000000000000000 : ℝ)
    (cell12262 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · have h := gap_lower (n := 12262) (a := (2564147635319 / 3125000000000 : ℝ)) (b := (42014479853 / 25000000000000 : ℝ)) (q := (1154921532261 / 50000000000000 : ℝ))
      (E := (cell12262 ⟨59, by decide⟩).energy) (xi := (346321358964341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12262 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12262]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12262])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12262) (a := (2564147635319 / 3125000000000 : ℝ)) (b := (42014479853 / 25000000000000 : ℝ)) (q := (1154921532261 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12262])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12262])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12262]

theorem cert12263_40 : CellCertificate 12263 (449658362756121 / 5000000000000000 : ℝ) (1712849613145793 / 1000000000000000000 : ℝ) (346292362998211 / 10000000000000000 : ℝ)
    (cell12263 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · have h := gap_lower (n := 12263) (a := (4134867469477 / 5000000000000 : ℝ)) (b := (168044031801 / 100000000000000 : ℝ)) (q := (2309620907979 / 100000000000000 : ℝ))
      (E := (cell12263 ⟨40, by decide⟩).energy) (xi := (346292362998211 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12263 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12263]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12263])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12263) (a := (4134867469477 / 5000000000000 : ℝ)) (b := (168044031801 / 100000000000000 : ℝ)) (q := (2309620907979 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12263])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12263])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12263]

theorem cert12263_41 : CellCertificate 12263 (449658362756121 / 5000000000000000 : ℝ) (1712849613145793 / 1000000000000000000 : ℝ) (346292362998211 / 10000000000000000 : ℝ)
    (cell12263 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · have h := gap_lower (n := 12263) (a := (16532641840921 / 20000000000000 : ℝ)) (b := (168044031801 / 100000000000000 : ℝ)) (q := (461924987237 / 20000000000000 : ℝ))
      (E := (cell12263 ⟨41, by decide⟩).energy) (xi := (346292362998211 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12263 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12263]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12263])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12263) (a := (16532641840921 / 20000000000000 : ℝ)) (b := (168044031801 / 100000000000000 : ℝ)) (q := (461924987237 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12263])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12263])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12263]

theorem cert12263_42 : CellCertificate 12263 (449658362756121 / 5000000000000000 : ℝ) (1712849613145793 / 1000000000000000000 : ℝ) (346292362998211 / 10000000000000000 : ℝ)
    (cell12263 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · have h := gap_lower (n := 12263) (a := (322769893829 / 390625000000 : ℝ)) (b := (168044031801 / 100000000000000 : ℝ)) (q := (92385155819 / 4000000000000 : ℝ))
      (E := (cell12263 ⟨42, by decide⟩).energy) (xi := (346292362998211 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12263 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12263]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12263])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12263) (a := (322769893829 / 390625000000 : ℝ)) (b := (168044031801 / 100000000000000 : ℝ)) (q := (92385155819 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12263])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12263])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12263]

theorem cert12263_43 : CellCertificate 12263 (449658362756121 / 5000000000000000 : ℝ) (1712849613145793 / 1000000000000000000 : ℝ) (346292362998211 / 10000000000000000 : ℝ)
    (cell12263 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · have h := gap_lower (n := 12263) (a := (82595000206363 / 100000000000000 : ℝ)) (b := (168044031801 / 100000000000000 : ℝ)) (q := (2309632903207 / 100000000000000 : ℝ))
      (E := (cell12263 ⟨43, by decide⟩).energy) (xi := (346292362998211 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12263 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12263]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12263])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12263) (a := (82595000206363 / 100000000000000 : ℝ)) (b := (168044031801 / 100000000000000 : ℝ)) (q := (2309632903207 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12263])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12263])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12263]

theorem cert12263_44 : CellCertificate 12263 (449658362756121 / 5000000000000000 : ℝ) (1712849613145793 / 1000000000000000000 : ℝ) (346292362998211 / 10000000000000000 : ℝ)
    (cell12263 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · have h := gap_lower (n := 12263) (a := (4128046566657 / 5000000000000 : ℝ)) (b := (168044031801 / 100000000000000 : ℝ)) (q := (2309636900311 / 100000000000000 : ℝ))
      (E := (cell12263 ⟨44, by decide⟩).energy) (xi := (346292362998211 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12263 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12263]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12263])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12263) (a := (4128046566657 / 5000000000000 : ℝ)) (b := (168044031801 / 100000000000000 : ℝ)) (q := (2309636900311 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12263])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12263])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12263]

theorem cert12263_45 : CellCertificate 12263 (449658362756121 / 5000000000000000 : ℝ) (1712849613145793 / 1000000000000000000 : ℝ) (346292362998211 / 10000000000000000 : ℝ)
    (cell12263 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · have h := gap_lower (n := 12263) (a := (3301075446833 / 4000000000000 : ℝ)) (b := (168044031801 / 100000000000000 : ℝ)) (q := (2309640886227 / 100000000000000 : ℝ))
      (E := (cell12263 ⟨45, by decide⟩).energy) (xi := (346292362998211 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12263 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12263]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12263])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12263) (a := (3301075446833 / 4000000000000 : ℝ)) (b := (168044031801 / 100000000000000 : ℝ)) (q := (2309640886227 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12263])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12263])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12263]

theorem cert12263_46 : CellCertificate 12263 (449658362756121 / 5000000000000000 : ℝ) (1712849613145793 / 1000000000000000000 : ℝ) (346292362998211 / 10000000000000000 : ℝ)
    (cell12263 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · have h := gap_lower (n := 12263) (a := (41246432344919 / 50000000000000 : ℝ)) (b := (168044031801 / 100000000000000 : ℝ)) (q := (2309644919019 / 100000000000000 : ℝ))
      (E := (cell12263 ⟨46, by decide⟩).energy) (xi := (346292362998211 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12263 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12263]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12263])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12263) (a := (41246432344919 / 50000000000000 : ℝ)) (b := (168044031801 / 100000000000000 : ℝ)) (q := (2309644919019 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12263])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12263])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12263]

theorem cert12263_47 : CellCertificate 12263 (449658362756121 / 5000000000000000 : ℝ) (1712849613145793 / 1000000000000000000 : ℝ) (346292362998211 / 10000000000000000 : ℝ)
    (cell12263 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · have h := gap_lower (n := 12263) (a := (20614716715187 / 25000000000000 : ℝ)) (b := (168044031801 / 100000000000000 : ℝ)) (q := (288706110003 / 12500000000000 : ℝ))
      (E := (cell12263 ⟨47, by decide⟩).energy) (xi := (346292362998211 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12263 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12263]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12263])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12263) (a := (20614716715187 / 25000000000000 : ℝ)) (b := (168044031801 / 100000000000000 : ℝ)) (q := (288706110003 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12263])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12263])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12263]

theorem cert12263_48 : CellCertificate 12263 (449658362756121 / 5000000000000000 : ℝ) (1712849613145793 / 1000000000000000000 : ℝ) (346292362998211 / 10000000000000000 : ℝ)
    (cell12263 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · have h := gap_lower (n := 12263) (a := (1287888947723 / 1562500000000 : ℝ)) (b := (168044031801 / 100000000000000 : ℝ)) (q := (2309652885741 / 100000000000000 : ℝ))
      (E := (cell12263 ⟨48, by decide⟩).energy) (xi := (346292362998211 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12263 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12263]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12263])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12263) (a := (1287888947723 / 1562500000000 : ℝ)) (b := (168044031801 / 100000000000000 : ℝ)) (q := (2309652885741 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12263])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12263])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12263]

theorem cert12263_49 : CellCertificate 12263 (449658362756121 / 5000000000000000 : ℝ) (1712849613145793 / 1000000000000000000 : ℝ) (346292362998211 / 10000000000000000 : ℝ)
    (cell12263 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · have h := gap_lower (n := 12263) (a := (20597735510319 / 25000000000000 : ℝ)) (b := (168044031801 / 100000000000000 : ℝ)) (q := (1154828437947 / 50000000000000 : ℝ))
      (E := (cell12263 ⟨49, by decide⟩).energy) (xi := (346292362998211 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12263 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12263]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12263])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12263) (a := (20597735510319 / 25000000000000 : ℝ)) (b := (168044031801 / 100000000000000 : ℝ)) (q := (1154828437947 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12263])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12263])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12263]

theorem cert12263_50 : CellCertificate 12263 (449658362756121 / 5000000000000000 : ℝ) (1712849613145793 / 1000000000000000000 : ℝ) (346292362998211 / 10000000000000000 : ℝ)
    (cell12263 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · have h := gap_lower (n := 12263) (a := (8235701499277 / 10000000000000 : ℝ)) (b := (168044031801 / 100000000000000 : ℝ)) (q := (2309660907777 / 100000000000000 : ℝ))
      (E := (cell12263 ⟨50, by decide⟩).energy) (xi := (346292362998211 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12263 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12263]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12263])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12263) (a := (8235701499277 / 10000000000000 : ℝ)) (b := (168044031801 / 100000000000000 : ℝ)) (q := (2309660907777 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12263])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12263])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12263]

theorem cert12263_51 : CellCertificate 12263 (449658362756121 / 5000000000000000 : ℝ) (1712849613145793 / 1000000000000000000 : ℝ) (346292362998211 / 10000000000000000 : ℝ)
    (cell12263 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · have h := gap_lower (n := 12263) (a := (41161555739957 / 50000000000000 : ℝ)) (b := (168044031801 / 100000000000000 : ℝ)) (q := (92386594467 / 4000000000000 : ℝ))
      (E := (cell12263 ⟨51, by decide⟩).energy) (xi := (346292362998211 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12263 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12263]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12263])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12263) (a := (41161555739957 / 50000000000000 : ℝ)) (b := (168044031801 / 100000000000000 : ℝ)) (q := (92386594467 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12263])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12263])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12263]

theorem cert12263_52 : CellCertificate 12263 (449658362756121 / 5000000000000000 : ℝ) (1712849613145793 / 1000000000000000000 : ℝ) (346292362998211 / 10000000000000000 : ℝ)
    (cell12263 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · have h := gap_lower (n := 12263) (a := (10286153934251 / 12500000000000 : ℝ)) (b := (168044031801 / 100000000000000 : ℝ)) (q := (288708606677 / 12500000000000 : ℝ))
      (E := (cell12263 ⟨52, by decide⟩).energy) (xi := (346292362998211 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12263 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12263]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12263])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12263) (a := (10286153934251 / 12500000000000 : ℝ)) (b := (168044031801 / 100000000000000 : ℝ)) (q := (288708606677 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12263])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12263])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12263]

theorem cert12263_53 : CellCertificate 12263 (449658362756121 / 5000000000000000 : ℝ) (1712849613145793 / 1000000000000000000 : ℝ) (346292362998211 / 10000000000000000 : ℝ)
    (cell12263 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · have h := gap_lower (n := 12263) (a := (82255374946501 / 100000000000000 : ℝ)) (b := (168044031801 / 100000000000000 : ℝ)) (q := (1154836440391 / 50000000000000 : ℝ))
      (E := (cell12263 ⟨53, by decide⟩).energy) (xi := (346292362998211 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12263 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12263]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12263])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12263) (a := (82255374946501 / 100000000000000 : ℝ)) (b := (168044031801 / 100000000000000 : ℝ)) (q := (1154836440391 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12263])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12263])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12263]

theorem cert12263_54 : CellCertificate 12263 (449658362756121 / 5000000000000000 : ℝ) (1712849613145793 / 1000000000000000000 : ℝ) (346292362998211 / 10000000000000000 : ℝ)
    (cell12263 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · have h := gap_lower (n := 12263) (a := (82221541868981 / 100000000000000 : ℝ)) (b := (168044031801 / 100000000000000 : ℝ)) (q := (1154838441157 / 50000000000000 : ℝ))
      (E := (cell12263 ⟨54, by decide⟩).energy) (xi := (346292362998211 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12263 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12263]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12263])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12263) (a := (82221541868981 / 100000000000000 : ℝ)) (b := (168044031801 / 100000000000000 : ℝ)) (q := (1154838441157 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12263])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12263])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12263]

theorem cert12263_55 : CellCertificate 12263 (449658362756121 / 5000000000000000 : ℝ) (1712849613145793 / 1000000000000000000 : ℝ) (346292362998211 / 10000000000000000 : ℝ)
    (cell12263 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · have h := gap_lower (n := 12263) (a := (41093866106591 / 50000000000000 : ℝ)) (b := (168044031801 / 100000000000000 : ℝ)) (q := (23096808553 / 1000000000000 : ℝ))
      (E := (cell12263 ⟨55, by decide⟩).energy) (xi := (346292362998211 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12263 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12263]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12263])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12263) (a := (41093866106591 / 50000000000000 : ℝ)) (b := (168044031801 / 100000000000000 : ℝ)) (q := (23096808553 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12263])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12263])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12263]

theorem cert12263_56 : CellCertificate 12263 (449658362756121 / 5000000000000000 : ℝ) (1712849613145793 / 1000000000000000000 : ℝ) (346292362998211 / 10000000000000000 : ℝ)
    (cell12263 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · have h := gap_lower (n := 12263) (a := (41076972975489 / 50000000000000 : ℝ)) (b := (168044031801 / 100000000000000 : ℝ)) (q := (23096848559 / 1000000000000 : ℝ))
      (E := (cell12263 ⟨56, by decide⟩).energy) (xi := (346292362998211 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12263 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12263]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12263])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12263) (a := (41076972975489 / 50000000000000 : ℝ)) (b := (168044031801 / 100000000000000 : ℝ)) (q := (23096848559 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12263])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12263])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12263]

theorem cert12263_57 : CellCertificate 12263 (449658362756121 / 5000000000000000 : ℝ) (1712849613145793 / 1000000000000000000 : ℝ) (346292362998211 / 10000000000000000 : ℝ)
    (cell12263 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · have h := gap_lower (n := 12263) (a := (5132511440899 / 6250000000000 : ℝ)) (b := (168044031801 / 100000000000000 : ℝ)) (q := (2309688881053 / 100000000000000 : ℝ))
      (E := (cell12263 ⟨57, by decide⟩).energy) (xi := (346292362998211 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12263 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12263]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12263])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12263) (a := (5132511440899 / 6250000000000 : ℝ)) (b := (168044031801 / 100000000000000 : ℝ)) (q := (2309688881053 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12263])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12263])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12263]

theorem cert12263_58 : CellCertificate 12263 (449658362756121 / 5000000000000000 : ℝ) (1712849613145793 / 1000000000000000000 : ℝ) (346292362998211 / 10000000000000000 : ℝ)
    (cell12263 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · have h := gap_lower (n := 12263) (a := (41043221747777 / 50000000000000 : ℝ)) (b := (168044031801 / 100000000000000 : ℝ)) (q := (461938573673 / 20000000000000 : ℝ))
      (E := (cell12263 ⟨58, by decide⟩).energy) (xi := (346292362998211 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12263 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12263]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12263])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12263) (a := (41043221747777 / 50000000000000 : ℝ)) (b := (168044031801 / 100000000000000 : ℝ)) (q := (461938573673 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12263])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12263])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12263]

theorem cert12263_59 : CellCertificate 12263 (449658362756121 / 5000000000000000 : ℝ) (1712849613145793 / 1000000000000000000 : ℝ) (346292362998211 / 10000000000000000 : ℝ)
    (cell12263 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · have h := gap_lower (n := 12263) (a := (82052727246783 / 100000000000000 : ℝ)) (b := (168044031801 / 100000000000000 : ℝ)) (q := (2309696873437 / 100000000000000 : ℝ))
      (E := (cell12263 ⟨59, by decide⟩).energy) (xi := (346292362998211 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12263 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12263]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12263])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12263) (a := (82052727246783 / 100000000000000 : ℝ)) (b := (168044031801 / 100000000000000 : ℝ)) (q := (2309696873437 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12263])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12263])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12263]

theorem cert12264_40 : CellCertificate 12264 (899286844543011 / 10000000000000000 : ℝ) (1712709900751861 / 1000000000000000000 : ℝ) (346263372010183 / 10000000000000000 : ℝ)
    (cell12264 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · have h := gap_lower (n := 12264) (a := (82697346312237 / 100000000000000 : ℝ)) (b := (33606029303 / 20000000000000 : ℝ)) (q := (1154737426561 / 50000000000000 : ℝ))
      (E := (cell12264 ⟨40, by decide⟩).energy) (xi := (346263372010183 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12264 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12264]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12264])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12264) (a := (82697346312237 / 100000000000000 : ℝ)) (b := (33606029303 / 20000000000000 : ℝ)) (q := (1154737426561 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12264])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12264])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12264]

theorem cert12264_41 : CellCertificate 12264 (899286844543011 / 10000000000000000 : ℝ) (1712709900751861 / 1000000000000000000 : ℝ) (346263372010183 / 10000000000000000 : ℝ)
    (cell12264 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · have h := gap_lower (n := 12264) (a := (20665801611681 / 25000000000000 : ℝ)) (b := (33606029303 / 20000000000000 : ℝ)) (q := (288684856113 / 12500000000000 : ℝ))
      (E := (cell12264 ⟨41, by decide⟩).energy) (xi := (346263372010183 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12264 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12264]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12264])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12264) (a := (20665801611681 / 25000000000000 : ℝ)) (b := (33606029303 / 20000000000000 : ℝ)) (q := (288684856113 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12264])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12264])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12264]

theorem cert12264_42 : CellCertificate 12264 (899286844543011 / 10000000000000000 : ℝ) (1712709900751861 / 1000000000000000000 : ℝ) (346263372010183 / 10000000000000000 : ℝ)
    (cell12264 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · have h := gap_lower (n := 12264) (a := (41314545190661 / 50000000000000 : ℝ)) (b := (33606029303 / 20000000000000 : ℝ)) (q := (2309482835239 / 100000000000000 : ℝ))
      (E := (cell12264 ⟨42, by decide⟩).energy) (xi := (346263372010183 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12264 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12264]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12264])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12264) (a := (41314545190661 / 50000000000000 : ℝ)) (b := (33606029303 / 20000000000000 : ℝ)) (q := (2309482835239 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12264])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12264])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12264]

theorem cert12264_43 : CellCertificate 12264 (899286844543011 / 10000000000000000 : ℝ) (1712709900751861 / 1000000000000000000 : ℝ) (346263372010183 / 10000000000000000 : ℝ)
    (cell12264 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · have h := gap_lower (n := 12264) (a := (41297499042999 / 50000000000000 : ℝ)) (b := (33606029303 / 20000000000000 : ℝ)) (q := (1154743406003 / 50000000000000 : ℝ))
      (E := (cell12264 ⟨43, by decide⟩).energy) (xi := (346263372010183 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12264 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12264]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12264])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12264) (a := (41297499042999 / 50000000000000 : ℝ)) (b := (33606029303 / 20000000000000 : ℝ)) (q := (1154743406003 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12264])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12264])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12264]

theorem cert12264_44 : CellCertificate 12264 (899286844543011 / 10000000000000000 : ℝ) (1712709900751861 / 1000000000000000000 : ℝ) (346263372010183 / 10000000000000000 : ℝ)
    (cell12264 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · have h := gap_lower (n := 12264) (a := (10320116191359 / 12500000000000 : ℝ)) (b := (33606029303 / 20000000000000 : ℝ)) (q := (2309490837659 / 100000000000000 : ℝ))
      (E := (cell12264 ⟨44, by decide⟩).energy) (xi := (346263372010183 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12264 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12264]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12264])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12264) (a := (10320116191359 / 12500000000000 : ℝ)) (b := (33606029303 / 20000000000000 : ℝ)) (q := (2309490837659 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12264])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12264])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12264]

theorem cert12264_45 : CellCertificate 12264 (899286844543011 / 10000000000000000 : ℝ) (1712709900751861 / 1000000000000000000 : ℝ) (346263372010183 / 10000000000000000 : ℝ)
    (cell12264 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · have h := gap_lower (n := 12264) (a := (41263442343107 / 50000000000000 : ℝ)) (b := (33606029303 / 20000000000000 : ℝ)) (q := (1154747397033 / 50000000000000 : ℝ))
      (E := (cell12264 ⟨45, by decide⟩).energy) (xi := (346263372010183 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12264 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12264]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12264])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12264) (a := (41263442343107 / 50000000000000 : ℝ)) (b := (33606029303 / 20000000000000 : ℝ)) (q := (1154747397033 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12264])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12264])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12264]

theorem cert12264_46 : CellCertificate 12264 (899286844543011 / 10000000000000000 : ℝ) (1712709900751861 / 1000000000000000000 : ℝ) (346263372010183 / 10000000000000000 : ℝ)
    (cell12264 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · have h := gap_lower (n := 12264) (a := (16498572704489 / 20000000000000 : ℝ)) (b := (33606029303 / 20000000000000 : ℝ)) (q := (2309498798063 / 100000000000000 : ℝ))
      (E := (cell12264 ⟨46, by decide⟩).energy) (xi := (346263372010183 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12264 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12264]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12264])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12264) (a := (16498572704489 / 20000000000000 : ℝ)) (b := (33606029303 / 20000000000000 : ℝ)) (q := (2309498798063 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12264])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12264])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12264]

theorem cert12264_47 : CellCertificate 12264 (899286844543011 / 10000000000000000 : ℝ) (1712709900751861 / 1000000000000000000 : ℝ) (346263372010183 / 10000000000000000 : ℝ)
    (cell12264 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · have h := gap_lower (n := 12264) (a := (41229433005067 / 50000000000000 : ℝ)) (b := (33606029303 / 20000000000000 : ℝ)) (q := (72171962183 / 3125000000000 : ℝ))
      (E := (cell12264 ⟨47, by decide⟩).energy) (xi := (346263372010183 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12264 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12264]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12264])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12264) (a := (41229433005067 / 50000000000000 : ℝ)) (b := (33606029303 / 20000000000000 : ℝ)) (q := (72171962183 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12264])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12264])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12264]

theorem cert12264_48 : CellCertificate 12264 (899286844543011 / 10000000000000000 : ℝ) (1712709900751861 / 1000000000000000000 : ℝ) (346263372010183 / 10000000000000000 : ℝ)
    (cell12264 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · have h := gap_lower (n := 12264) (a := (2060622303 / 2500000000 : ℝ)) (b := (33606029303 / 20000000000000 : ℝ)) (q := (230950676823 / 10000000000000 : ℝ))
      (E := (cell12264 ⟨48, by decide⟩).energy) (xi := (346263372010183 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12264 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12264]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12264])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12264) (a := (2060622303 / 2500000000 : ℝ)) (b := (33606029303 / 20000000000000 : ℝ)) (q := (230950676823 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12264])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12264])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12264]

theorem cert12264_49 : CellCertificate 12264 (899286844543011 / 10000000000000000 : ℝ) (1712709900751861 / 1000000000000000000 : ℝ) (346263372010183 / 10000000000000000 : ℝ)
    (cell12264 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · have h := gap_lower (n := 12264) (a := (20597735455727 / 25000000000000 : ℝ)) (b := (33606029303 / 20000000000000 : ℝ)) (q := (577377697667 / 25000000000000 : ℝ))
      (E := (cell12264 ⟨49, by decide⟩).energy) (xi := (346263372010183 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12264 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12264]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12264])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12264) (a := (20597735455727 / 25000000000000 : ℝ)) (b := (33606029303 / 20000000000000 : ℝ)) (q := (577377697667 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12264])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12264])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12264]

theorem cert12264_50 : CellCertificate 12264 (899286844543011 / 10000000000000000 : ℝ) (1712709900751861 / 1000000000000000000 : ℝ) (346263372010183 / 10000000000000000 : ℝ)
    (cell12264 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · have h := gap_lower (n := 12264) (a := (82357015089871 / 100000000000000 : ℝ)) (b := (33606029303 / 20000000000000 : ℝ)) (q := (2309514796657 / 100000000000000 : ℝ))
      (E := (cell12264 ⟨50, by decide⟩).energy) (xi := (346263372010183 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12264 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12264]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12264])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12264) (a := (82357015089871 / 100000000000000 : ℝ)) (b := (33606029303 / 20000000000000 : ℝ)) (q := (2309514796657 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12264])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12264])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12264]

theorem cert12264_51 : CellCertificate 12264 (899286844543011 / 10000000000000000 : ℝ) (1712709900751861 / 1000000000000000000 : ℝ) (346263372010183 / 10000000000000000 : ℝ)
    (cell12264 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · have h := gap_lower (n := 12264) (a := (5145194493253 / 6250000000000 : ℝ)) (b := (33606029303 / 20000000000000 : ℝ)) (q := (2309518784333 / 100000000000000 : ℝ))
      (E := (cell12264 ⟨51, by decide⟩).energy) (xi := (346263372010183 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12264 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12264]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12264])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12264) (a := (5145194493253 / 6250000000000 : ℝ)) (b := (33606029303 / 20000000000000 : ℝ)) (q := (2309518784333 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12264])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12264])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12264]

theorem cert12264_52 : CellCertificate 12264 (899286844543011 / 10000000000000000 : ℝ) (1712709900751861 / 1000000000000000000 : ℝ) (346263372010183 / 10000000000000000 : ℝ)
    (cell12264 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · have h := gap_lower (n := 12264) (a := (82289232200741 / 100000000000000 : ℝ)) (b := (33606029303 / 20000000000000 : ℝ)) (q := (18476182013 / 800000000000 : ℝ))
      (E := (cell12264 ⟨52, by decide⟩).energy) (xi := (346263372010183 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12264 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12264]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12264])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12264) (a := (82289232200741 / 100000000000000 : ℝ)) (b := (33606029303 / 20000000000000 : ℝ)) (q := (18476182013 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12264])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12264])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12264]

theorem cert12264_53 : CellCertificate 12264 (899286844543011 / 10000000000000000 : ℝ) (1712709900751861 / 1000000000000000000 : ℝ) (346263372010183 / 10000000000000000 : ℝ)
    (cell12264 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · have h := gap_lower (n := 12264) (a := (82255375987399 / 100000000000000 : ℝ)) (b := (33606029303 / 20000000000000 : ℝ)) (q := (577381688813 / 25000000000000 : ℝ))
      (E := (cell12264 ⟨53, by decide⟩).energy) (xi := (346263372010183 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12264 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12264]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12264])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12264) (a := (82255375987399 / 100000000000000 : ℝ)) (b := (33606029303 / 20000000000000 : ℝ)) (q := (577381688813 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12264])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12264])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12264]

theorem cert12264_54 : CellCertificate 12264 (899286844543011 / 10000000000000000 : ℝ) (1712709900751861 / 1000000000000000000 : ℝ) (346263372010183 / 10000000000000000 : ℝ)
    (cell12264 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · have h := gap_lower (n := 12264) (a := (82221543223611 / 100000000000000 : ℝ)) (b := (33606029303 / 20000000000000 : ℝ)) (q := (2309530792787 / 100000000000000 : ℝ))
      (E := (cell12264 ⟨54, by decide⟩).energy) (xi := (346263372010183 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12264 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12264]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12264])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12264) (a := (82221543223611 / 100000000000000 : ℝ)) (b := (33606029303 / 20000000000000 : ℝ)) (q := (2309530792787 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12264])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12264])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12264]

theorem cert12264_55 : CellCertificate 12264 (899286844543011 / 10000000000000000 : ℝ) (1712709900751861 / 1000000000000000000 : ℝ) (346263372010183 / 10000000000000000 : ℝ)
    (cell12264 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · have h := gap_lower (n := 12264) (a := (82187733881111 / 100000000000000 : ℝ)) (b := (33606029303 / 20000000000000 : ℝ)) (q := (577383685869 / 25000000000000 : ℝ))
      (E := (cell12264 ⟨55, by decide⟩).energy) (xi := (346263372010183 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12264 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12264]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12264])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12264) (a := (82187733881111 / 100000000000000 : ℝ)) (b := (33606029303 / 20000000000000 : ℝ)) (q := (577383685869 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12264])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12264])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12264]

theorem cert12264_56 : CellCertificate 12264 (899286844543011 / 10000000000000000 : ℝ) (1712709900751861 / 1000000000000000000 : ℝ) (346263372010183 / 10000000000000000 : ℝ)
    (cell12264 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · have h := gap_lower (n := 12264) (a := (3286157917271 / 4000000000000 : ℝ)) (b := (33606029303 / 20000000000000 : ℝ)) (q := (461907756313 / 20000000000000 : ℝ))
      (E := (cell12264 ⟨56, by decide⟩).energy) (xi := (346263372010183 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12264 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12264]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12264])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12264) (a := (3286157917271 / 4000000000000 : ℝ)) (b := (33606029303 / 20000000000000 : ℝ)) (q := (461907756313 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12264])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12264])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12264]

theorem cert12264_57 : CellCertificate 12264 (899286844543011 / 10000000000000000 : ℝ) (1712709900751861 / 1000000000000000000 : ℝ) (346263372010183 / 10000000000000000 : ℝ)
    (cell12264 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · have h := gap_lower (n := 12264) (a := (82120185347617 / 100000000000000 : ℝ)) (b := (33606029303 / 20000000000000 : ℝ)) (q := (115477139293 / 5000000000000 : ℝ))
      (E := (cell12264 ⟨57, by decide⟩).energy) (xi := (346263372010183 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12264 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12264]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12264])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12264) (a := (82120185347617 / 100000000000000 : ℝ)) (b := (33606029303 / 20000000000000 : ℝ)) (q := (115477139293 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12264])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12264])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12264]

theorem cert12264_58 : CellCertificate 12264 (899286844543011 / 10000000000000000 : ℝ) (1712709900751861 / 1000000000000000000 : ℝ) (346263372010183 / 10000000000000000 : ℝ)
    (cell12264 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · have h := gap_lower (n := 12264) (a := (16417289220159 / 20000000000000 : ℝ)) (b := (33606029303 / 20000000000000 : ℝ)) (q := (2309546753017 / 100000000000000 : ℝ))
      (E := (cell12264 ⟨58, by decide⟩).energy) (xi := (346263372010183 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12264 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12264]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12264])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12264) (a := (16417289220159 / 20000000000000 : ℝ)) (b := (33606029303 / 20000000000000 : ℝ)) (q := (2309546753017 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12264])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12264])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12264]

theorem cert12264_59 : CellCertificate 12264 (899286844543011 / 10000000000000000 : ℝ) (1712709900751861 / 1000000000000000000 : ℝ) (346263372010183 / 10000000000000000 : ℝ)
    (cell12264 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · have h := gap_lower (n := 12264) (a := (82052730163601 / 100000000000000 : ℝ)) (b := (33606029303 / 20000000000000 : ℝ)) (q := (2309550738643 / 100000000000000 : ℝ))
      (E := (cell12264 ⟨59, by decide⟩).energy) (xi := (346263372010183 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12264 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12264]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12264])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12264) (a := (82052730163601 / 100000000000000 : ℝ)) (b := (33606029303 / 20000000000000 : ℝ)) (q := (2309550738643 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12264])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12264])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12264]

theorem cert12265_40 : CellCertificate 12265 (449628484134267 / 5000000000000000 : ℝ) (1712570211147973 / 1000000000000000000 : ℝ) (346234385998803 / 10000000000000000 : ℝ)
    (cell12265 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · have h := gap_lower (n := 12265) (a := (82697343235929 / 100000000000000 : ℝ)) (b := (84008131777 / 50000000000000 : ℝ)) (q := (1154664397317 / 50000000000000 : ℝ))
      (E := (cell12265 ⟨40, by decide⟩).energy) (xi := (346234385998803 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12265 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12265]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12265])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12265) (a := (82697343235929 / 100000000000000 : ℝ)) (b := (84008131777 / 50000000000000 : ℝ)) (q := (1154664397317 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12265])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12265])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12265]

theorem cert12265_41 : CellCertificate 12265 (449628484134267 / 5000000000000000 : ℝ) (1712570211147973 / 1000000000000000000 : ℝ) (346234385998803 / 10000000000000000 : ℝ)
    (cell12265 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · have h := gap_lower (n := 12265) (a := (41331601844899 / 50000000000000 : ℝ)) (b := (84008131777 / 50000000000000 : ℝ)) (q := (1154666408379 / 50000000000000 : ℝ))
      (E := (cell12265 ⟨41, by decide⟩).energy) (xi := (346234385998803 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12265 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12265]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12265])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12265) (a := (41331601844899 / 50000000000000 : ℝ)) (b := (84008131777 / 50000000000000 : ℝ)) (q := (1154666408379 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12265])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12265])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12265]

theorem cert12265_42 : CellCertificate 12265 (449628484134267 / 5000000000000000 : ℝ) (1712570211147973 / 1000000000000000000 : ℝ) (346234385998803 / 10000000000000000 : ℝ)
    (cell12265 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · have h := gap_lower (n := 12265) (a := (16525817588667 / 20000000000000 : ℝ)) (b := (84008131777 / 50000000000000 : ℝ)) (q := (577334192863 / 25000000000000 : ℝ))
      (E := (cell12265 ⟨42, by decide⟩).energy) (xi := (346234385998803 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12265 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12265]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12265])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12265) (a := (16525817588667 / 20000000000000 : ℝ)) (b := (84008131777 / 50000000000000 : ℝ)) (q := (577334192863 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12265])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12265])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12265]

theorem cert12265_43 : CellCertificate 12265 (449628484134267 / 5000000000000000 : ℝ) (1712570211147973 / 1000000000000000000 : ℝ) (346234385998803 / 10000000000000000 : ℝ)
    (cell12265 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · have h := gap_lower (n := 12265) (a := (82594995966509 / 100000000000000 : ℝ)) (b := (84008131777 / 50000000000000 : ℝ)) (q := (2309340776069 / 100000000000000 : ℝ))
      (E := (cell12265 ⟨43, by decide⟩).energy) (xi := (346234385998803 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12265 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12265]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12265])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12265) (a := (82594995966509 / 100000000000000 : ℝ)) (b := (84008131777 / 50000000000000 : ℝ)) (q := (2309340776069 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12265])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12265])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12265]

theorem cert12265_44 : CellCertificate 12265 (449628484134267 / 5000000000000000 : ℝ) (1712570211147973 / 1000000000000000000 : ℝ) (346234385998803 / 10000000000000000 : ℝ)
    (cell12265 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · have h := gap_lower (n := 12265) (a := (516005798309 / 625000000000 : ℝ)) (b := (84008131777 / 50000000000000 : ℝ)) (q := (1154672385769 / 50000000000000 : ℝ))
      (E := (cell12265 ⟨44, by decide⟩).energy) (xi := (346234385998803 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12265 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12265]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12265])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12265) (a := (516005798309 / 625000000000 : ℝ)) (b := (84008131777 / 50000000000000 : ℝ)) (q := (1154672385769 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12265])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12265])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12265]

theorem cert12265_45 : CellCertificate 12265 (449628484134267 / 5000000000000000 : ℝ) (1712570211147973 / 1000000000000000000 : ℝ) (346234385998803 / 10000000000000000 : ℝ)
    (cell12265 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · have h := gap_lower (n := 12265) (a := (82526883202399 / 100000000000000 : ℝ)) (b := (84008131777 / 50000000000000 : ℝ)) (q := (2309348757297 / 100000000000000 : ℝ))
      (E := (cell12265 ⟨45, by decide⟩).energy) (xi := (346234385998803 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12265 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12265]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12265])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12265) (a := (82526883202399 / 100000000000000 : ℝ)) (b := (84008131777 / 50000000000000 : ℝ)) (q := (2309348757297 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12265])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12265])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12265]

theorem cert12265_46 : CellCertificate 12265 (449628484134267 / 5000000000000000 : ℝ) (1712570211147973 / 1000000000000000000 : ℝ) (346234385998803 / 10000000000000000 : ℝ)
    (cell12265 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · have h := gap_lower (n := 12265) (a := (82492862355807 / 100000000000000 : ℝ)) (b := (84008131777 / 50000000000000 : ℝ)) (q := (230935279141 / 10000000000000 : ℝ))
      (E := (cell12265 ⟨46, by decide⟩).energy) (xi := (346234385998803 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12265 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12265]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12265])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12265) (a := (82492862355807 / 100000000000000 : ℝ)) (b := (84008131777 / 50000000000000 : ℝ)) (q := (230935279141 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12265])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12265])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12265]

theorem cert12265_47 : CellCertificate 12265 (449628484134267 / 5000000000000000 : ℝ) (1712570211147973 / 1000000000000000000 : ℝ) (346234385998803 / 10000000000000000 : ℝ)
    (cell12265 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · have h := gap_lower (n := 12265) (a := (20614716290059 / 25000000000000 : ℝ)) (b := (84008131777 / 50000000000000 : ℝ)) (q := (2309356755211 / 100000000000000 : ℝ))
      (E := (cell12265 ⟨47, by decide⟩).energy) (xi := (346234385998803 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12265 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12265]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12265])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12265) (a := (20614716290059 / 25000000000000 : ℝ)) (b := (84008131777 / 50000000000000 : ℝ)) (q := (2309356755211 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12265])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12265])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12265]

theorem cert12265_48 : CellCertificate 12265 (449628484134267 / 5000000000000000 : ℝ) (1712570211147973 / 1000000000000000000 : ℝ) (346234385998803 / 10000000000000000 : ℝ)
    (cell12265 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · have h := gap_lower (n := 12265) (a := (82424891586403 / 100000000000000 : ℝ)) (b := (84008131777 / 50000000000000 : ℝ)) (q := (1154680382599 / 50000000000000 : ℝ))
      (E := (cell12265 ⟨48, by decide⟩).energy) (xi := (346234385998803 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12265 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12265]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12265])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12265) (a := (82424891586403 / 100000000000000 : ℝ)) (b := (84008131777 / 50000000000000 : ℝ)) (q := (1154680382599 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12265])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12265])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12265]

theorem cert12265_49 : CellCertificate 12265 (449628484134267 / 5000000000000000 : ℝ) (1712570211147973 / 1000000000000000000 : ℝ) (346234385998803 / 10000000000000000 : ℝ)
    (cell12265 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · have h := gap_lower (n := 12265) (a := (10298867700647 / 12500000000000 : ℝ)) (b := (84008131777 / 50000000000000 : ℝ)) (q := (1154682380547 / 50000000000000 : ℝ))
      (E := (cell12265 ⟨49, by decide⟩).energy) (xi := (346234385998803 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12265 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12265]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12265])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12265) (a := (10298867700647 / 12500000000000 : ℝ)) (b := (84008131777 / 50000000000000 : ℝ)) (q := (1154682380547 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12265])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12265])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12265]

theorem cert12265_50 : CellCertificate 12265 (449628484134267 / 5000000000000000 : ℝ) (1712570211147973 / 1000000000000000000 : ℝ) (346234385998803 / 10000000000000000 : ℝ)
    (cell12265 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · have h := gap_lower (n := 12265) (a := (82357015187569 / 100000000000000 : ℝ)) (b := (84008131777 / 50000000000000 : ℝ)) (q := (2309368741251 / 100000000000000 : ℝ))
      (E := (cell12265 ⟨50, by decide⟩).energy) (xi := (346234385998803 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12265 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12265]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12265])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12265) (a := (82357015187569 / 100000000000000 : ℝ)) (b := (84008131777 / 50000000000000 : ℝ)) (q := (2309368741251 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12265])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12265])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12265]

theorem cert12265_51 : CellCertificate 12265 (449628484134267 / 5000000000000000 : ℝ) (1712570211147973 / 1000000000000000000 : ℝ) (346234385998803 / 10000000000000000 : ℝ)
    (cell12265 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · have h := gap_lower (n := 12265) (a := (82323112304739 / 100000000000000 : ℝ)) (b := (84008131777 / 50000000000000 : ℝ)) (q := (577343190693 / 25000000000000 : ℝ))
      (E := (cell12265 ⟨51, by decide⟩).energy) (xi := (346234385998803 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12265 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12265]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12265])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12265) (a := (82323112304739 / 100000000000000 : ℝ)) (b := (84008131777 / 50000000000000 : ℝ)) (q := (577343190693 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12265])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12265])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12265]

theorem cert12265_52 : CellCertificate 12265 (449628484134267 / 5000000000000000 : ℝ) (1712570211147973 / 1000000000000000000 : ℝ) (346234385998803 / 10000000000000000 : ℝ)
    (cell12265 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · have h := gap_lower (n := 12265) (a := (10286154115999 / 12500000000000 : ℝ)) (b := (84008131777 / 50000000000000 : ℝ)) (q := (2309376764663 / 100000000000000 : ℝ))
      (E := (cell12265 ⟨52, by decide⟩).energy) (xi := (346234385998803 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12265 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12265]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12265])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12265) (a := (10286154115999 / 12500000000000 : ℝ)) (b := (84008131777 / 50000000000000 : ℝ)) (q := (2309376764663 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12265])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12265])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12265]

theorem cert12265_53 : CellCertificate 12265 (449628484134267 / 5000000000000000 : ℝ) (1712570211147973 / 1000000000000000000 : ℝ) (346234385998803 / 10000000000000000 : ℝ)
    (cell12265 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · have h := gap_lower (n := 12265) (a := (41127688514387 / 50000000000000 : ℝ)) (b := (84008131777 / 50000000000000 : ℝ)) (q := (7216814827 / 312500000000 : ℝ))
      (E := (cell12265 ⟨53, by decide⟩).energy) (xi := (346234385998803 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12265 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12265]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12265])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12265) (a := (41127688514387 / 50000000000000 : ℝ)) (b := (84008131777 / 50000000000000 : ℝ)) (q := (7216814827 / 312500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12265])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12265])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12265]

theorem cert12265_54 : CellCertificate 12265 (449628484134267 / 5000000000000000 : ℝ) (1712570211147973 / 1000000000000000000 : ℝ) (346234385998803 / 10000000000000000 : ℝ)
    (cell12265 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · have h := gap_lower (n := 12265) (a := (82221544578679 / 100000000000000 : ℝ)) (b := (84008131777 / 50000000000000 : ℝ)) (q := (36084136863 / 1562500000000 : ℝ))
      (E := (cell12265 ⟨54, by decide⟩).energy) (xi := (346234385998803 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12265 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12265]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12265])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12265) (a := (82221544578679 / 100000000000000 : ℝ)) (b := (84008131777 / 50000000000000 : ℝ)) (q := (36084136863 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12265])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12265])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12265]

theorem cert12265_55 : CellCertificate 12265 (449628484134267 / 5000000000000000 : ℝ) (1712570211147973 / 1000000000000000000 : ℝ) (346234385998803 / 10000000000000000 : ℝ)
    (cell12265 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · have h := gap_lower (n := 12265) (a := (32104584199 / 39062500000 : ℝ)) (b := (84008131777 / 50000000000000 : ℝ)) (q := (1154694373371 / 50000000000000 : ℝ))
      (E := (cell12265 ⟨55, by decide⟩).energy) (xi := (346234385998803 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12265 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12265]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12265])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12265) (a := (32104584199 / 39062500000 : ℝ)) (b := (84008131777 / 50000000000000 : ℝ)) (q := (1154694373371 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12265])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12265])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12265]

theorem cert12265_56 : CellCertificate 12265 (449628484134267 / 5000000000000000 : ℝ) (1712570211147973 / 1000000000000000000 : ℝ) (346234385998803 / 10000000000000000 : ℝ)
    (cell12265 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · have h := gap_lower (n := 12265) (a := (20538487478233 / 25000000000000 : ℝ)) (b := (84008131777 / 50000000000000 : ℝ)) (q := (230939276333 / 10000000000000 : ℝ))
      (E := (cell12265 ⟨56, by decide⟩).energy) (xi := (346234385998803 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12265 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12265]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12265])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12265) (a := (20538487478233 / 25000000000000 : ℝ)) (b := (84008131777 / 50000000000000 : ℝ)) (q := (230939276333 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12265])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12265])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12265]

theorem cert12265_57 : CellCertificate 12265 (449628484134267 / 5000000000000000 : ℝ) (1712570211147973 / 1000000000000000000 : ℝ) (346234385998803 / 10000000000000000 : ℝ)
    (cell12265 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · have h := gap_lower (n := 12265) (a := (82120187641173 / 100000000000000 : ℝ)) (b := (84008131777 / 50000000000000 : ℝ)) (q := (577349186707 / 25000000000000 : ℝ))
      (E := (cell12265 ⟨57, by decide⟩).energy) (xi := (346234385998803 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12265 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12265]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12265])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12265) (a := (82120187641173 / 100000000000000 : ℝ)) (b := (84008131777 / 50000000000000 : ℝ)) (q := (577349186707 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12265])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12265])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12265]

theorem cert12265_58 : CellCertificate 12265 (449628484134267 / 5000000000000000 : ℝ) (1712570211147973 / 1000000000000000000 : ℝ) (346234385998803 / 10000000000000000 : ℝ)
    (cell12265 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · have h := gap_lower (n := 12265) (a := (82086448706317 / 100000000000000 : ℝ)) (b := (84008131777 / 50000000000000 : ℝ)) (q := (92376030121 / 4000000000000 : ℝ))
      (E := (cell12265 ⟨58, by decide⟩).energy) (xi := (346234385998803 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12265 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12265]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12265])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12265) (a := (82086448706317 / 100000000000000 : ℝ)) (b := (84008131777 / 50000000000000 : ℝ)) (q := (92376030121 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12265])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12265])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12265]

theorem cert12265_59 : CellCertificate 12265 (449628484134267 / 5000000000000000 : ℝ) (1712570211147973 / 1000000000000000000 : ℝ) (346234385998803 / 10000000000000000 : ℝ)
    (cell12265 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · have h := gap_lower (n := 12265) (a := (82052733080663 / 100000000000000 : ℝ)) (b := (84008131777 / 50000000000000 : ℝ)) (q := (288675589911 / 12500000000000 : ℝ))
      (E := (cell12265 ⟨59, by decide⟩).energy) (xi := (346234385998803 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12265 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12265]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12265])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12265) (a := (82052733080663 / 100000000000000 : ℝ)) (b := (84008131777 / 50000000000000 : ℝ)) (q := (288675589911 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12265])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12265])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12265]

theorem cert12266_40 : CellCertificate 12266 (224806774171913 / 2500000000000000 : ℝ) (856215272164277 / 500000000000000000 : ℝ) (346205404962619 / 10000000000000000 : ℝ)
    (cell12266 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · have h := gap_lower (n := 12266) (a := (10337167520077 / 12500000000000 : ℝ)) (b := (168002382917 / 100000000000000 : ℝ)) (q := (3608098203 / 156250000000 : ℝ))
      (E := (cell12266 ⟨40, by decide⟩).energy) (xi := (346205404962619 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12266 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12266]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12266])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12266) (a := (10337167520077 / 12500000000000 : ℝ)) (b := (168002382917 / 100000000000000 : ℝ)) (q := (3608098203 / 156250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12266])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12266])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12266]

theorem cert12266_41 : CellCertificate 12266 (224806774171913 / 2500000000000000 : ℝ) (856215272164277 / 500000000000000000 : ℝ) (346205404962619 / 10000000000000000 : ℝ)
    (cell12266 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · have h := gap_lower (n := 12266) (a := (41331600466913 / 50000000000000 : ℝ)) (b := (168002382917 / 100000000000000 : ℝ)) (q := (9236747359 / 400000000000 : ℝ))
      (E := (cell12266 ⟨41, by decide⟩).energy) (xi := (346205404962619 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12266 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12266]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12266])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12266) (a := (41331600466913 / 50000000000000 : ℝ)) (b := (168002382917 / 100000000000000 : ℝ)) (q := (9236747359 / 400000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12266])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12266])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12266]

theorem cert12266_42 : CellCertificate 12266 (224806774171913 / 2500000000000000 : ℝ) (856215272164277 / 500000000000000000 : ℝ) (346205404962619 / 10000000000000000 : ℝ)
    (cell12266 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · have h := gap_lower (n := 12266) (a := (41314542753131 / 50000000000000 : ℝ)) (b := (168002382917 / 100000000000000 : ℝ)) (q := (144324430023 / 6250000000000 : ℝ))
      (E := (cell12266 ⟨42, by decide⟩).energy) (xi := (346205404962619 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12266 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12266]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12266])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12266) (a := (41314542753131 / 50000000000000 : ℝ)) (b := (168002382917 / 100000000000000 : ℝ)) (q := (144324430023 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12266])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12266])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12266]

theorem cert12266_43 : CellCertificate 12266 (224806774171913 / 2500000000000000 : ℝ) (856215272164277 / 500000000000000000 : ℝ) (346205404962619 / 10000000000000000 : ℝ)
    (cell12266 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · have h := gap_lower (n := 12266) (a := (41297496923947 / 50000000000000 : ℝ)) (b := (168002382917 / 100000000000000 : ℝ)) (q := (577298713543 / 25000000000000 : ℝ))
      (E := (cell12266 ⟨43, by decide⟩).energy) (xi := (346205404962619 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12266 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12266]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12266])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12266) (a := (41297496923947 / 50000000000000 : ℝ)) (b := (168002382917 / 100000000000000 : ℝ)) (q := (577298713543 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12266])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12266])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12266]

theorem cert12266_44 : CellCertificate 12266 (224806774171913 / 2500000000000000 : ℝ) (856215272164277 / 500000000000000000 : ℝ) (346205404962619 / 10000000000000000 : ℝ)
    (cell12266 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · have h := gap_lower (n := 12266) (a := (41280462964421 / 50000000000000 : ℝ)) (b := (168002382917 / 100000000000000 : ℝ)) (q := (2309198878343 / 100000000000000 : ℝ))
      (E := (cell12266 ⟨44, by decide⟩).energy) (xi := (346205404962619 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12266 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12266]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12266])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12266) (a := (41280462964421 / 50000000000000 : ℝ)) (b := (168002382917 / 100000000000000 : ℝ)) (q := (2309198878343 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12266])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12266])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12266]

theorem cert12266_45 : CellCertificate 12266 (224806774171913 / 2500000000000000 : ℝ) (856215272164277 / 500000000000000000 : ℝ) (346205404962619 / 10000000000000000 : ℝ)
    (cell12266 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · have h := gap_lower (n := 12266) (a := (41263440859689 / 50000000000000 : ℝ)) (b := (168002382917 / 100000000000000 : ℝ)) (q := (461840566949 / 20000000000000 : ℝ))
      (E := (cell12266 ⟨45, by decide⟩).energy) (xi := (346205404962619 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12266 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12266]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12266])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12266) (a := (41263440859689 / 50000000000000 : ℝ)) (b := (168002382917 / 100000000000000 : ℝ)) (q := (461840566949 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12266])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12266])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12266]

theorem cert12266_46 : CellCertificate 12266 (224806774171913 / 2500000000000000 : ℝ) (856215272164277 / 500000000000000000 : ℝ) (346205404962619 / 10000000000000000 : ℝ)
    (cell12266 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · have h := gap_lower (n := 12266) (a := (20623215297481 / 25000000000000 : ℝ)) (b := (168002382917 / 100000000000000 : ℝ)) (q := (288650855027 / 12500000000000 : ℝ))
      (E := (cell12266 ⟨46, by decide⟩).energy) (xi := (346205404962619 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12266 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12266]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12266])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12266) (a := (20623215297481 / 25000000000000 : ℝ)) (b := (168002382917 / 100000000000000 : ℝ)) (q := (288650855027 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12266])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12266])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12266]

theorem cert12266_47 : CellCertificate 12266 (224806774171913 / 2500000000000000 : ℝ) (856215272164277 / 500000000000000000 : ℝ) (346205404962619 / 10000000000000000 : ℝ)
    (cell12266 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · have h := gap_lower (n := 12266) (a := (20614716077763 / 25000000000000 : ℝ)) (b := (168002382917 / 100000000000000 : ℝ)) (q := (1154605417479 / 50000000000000 : ℝ))
      (E := (cell12266 ⟨47, by decide⟩).energy) (xi := (346205404962619 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12266 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12266]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12266])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12266) (a := (20614716077763 / 25000000000000 : ℝ)) (b := (168002382917 / 100000000000000 : ℝ)) (q := (1154605417479 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12266])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12266])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12266]

theorem cert12266_48 : CellCertificate 12266 (224806774171913 / 2500000000000000 : ℝ) (856215272164277 / 500000000000000000 : ℝ) (346205404962619 / 10000000000000000 : ℝ)
    (cell12266 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · have h := gap_lower (n := 12266) (a := (41212445526741 / 50000000000000 : ℝ)) (b := (168002382917 / 100000000000000 : ℝ)) (q := (1154607408877 / 50000000000000 : ℝ))
      (E := (cell12266 ⟨48, by decide⟩).energy) (xi := (346205404962619 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12266 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12266]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12266])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12266) (a := (41212445526741 / 50000000000000 : ℝ)) (b := (168002382917 / 100000000000000 : ℝ)) (q := (1154607408877 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12266])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12266])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12266]

theorem cert12266_49 : CellCertificate 12266 (224806774171913 / 2500000000000000 : ℝ) (856215272164277 / 500000000000000000 : ℝ) (346205404962619 / 10000000000000000 : ℝ)
    (cell12266 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · have h := gap_lower (n := 12266) (a := (82390941388081 / 100000000000000 : ℝ)) (b := (168002382917 / 100000000000000 : ℝ)) (q := (2309218846087 / 100000000000000 : ℝ))
      (E := (cell12266 ⟨49, by decide⟩).energy) (xi := (346205404962619 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12266 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12266]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12266])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12266) (a := (82390941388081 / 100000000000000 : ℝ)) (b := (168002382917 / 100000000000000 : ℝ)) (q := (2309218846087 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12266])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12266])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12266]

theorem cert12266_50 : CellCertificate 12266 (224806774171913 / 2500000000000000 : ℝ) (856215272164277 / 500000000000000000 : ℝ) (346205404962619 / 10000000000000000 : ℝ)
    (cell12266 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · have h := gap_lower (n := 12266) (a := (82357015285863 / 100000000000000 : ℝ)) (b := (168002382917 / 100000000000000 : ℝ)) (q := (28865285743 / 1250000000000 : ℝ))
      (E := (cell12266 ⟨50, by decide⟩).energy) (xi := (346205404962619 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12266 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12266]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12266])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12266) (a := (82357015285863 / 100000000000000 : ℝ)) (b := (168002382917 / 100000000000000 : ℝ)) (q := (28865285743 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12266])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12266])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12266]

theorem cert12266_51 : CellCertificate 12266 (224806774171913 / 2500000000000000 : ℝ) (856215272164277 / 500000000000000000 : ℝ) (346205404962619 / 10000000000000000 : ℝ)
    (cell12266 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · have h := gap_lower (n := 12266) (a := (82323112717987 / 100000000000000 : ℝ)) (b := (168002382917 / 100000000000000 : ℝ)) (q := (2309226855953 / 100000000000000 : ℝ))
      (E := (cell12266 ⟨51, by decide⟩).energy) (xi := (346205404962619 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12266 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12266]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12266])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12266) (a := (82323112717987 / 100000000000000 : ℝ)) (b := (168002382917 / 100000000000000 : ℝ)) (q := (2309226855953 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12266])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12266])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12266]

theorem cert12266_52 : CellCertificate 12266 (224806774171913 / 2500000000000000 : ℝ) (856215272164277 / 500000000000000000 : ℝ) (346205404962619 / 10000000000000000 : ℝ)
    (cell12266 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · have h := gap_lower (n := 12266) (a := (82289233655759 / 100000000000000 : ℝ)) (b := (168002382917 / 100000000000000 : ℝ)) (q := (577307708387 / 25000000000000 : ℝ))
      (E := (cell12266 ⟨52, by decide⟩).energy) (xi := (346205404962619 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12266 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12266]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12266])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12266) (a := (82289233655759 / 100000000000000 : ℝ)) (b := (168002382917 / 100000000000000 : ℝ)) (q := (577307708387 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12266])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12266])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12266]

theorem cert12266_53 : CellCertificate 12266 (224806774171913 / 2500000000000000 : ℝ) (856215272164277 / 500000000000000000 : ℝ) (346205404962619 / 10000000000000000 : ℝ)
    (cell12266 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · have h := gap_lower (n := 12266) (a := (20563844517657 / 25000000000000 : ℝ)) (b := (168002382917 / 100000000000000 : ℝ)) (q := (1154617424473 / 50000000000000 : ℝ))
      (E := (cell12266 ⟨53, by decide⟩).energy) (xi := (346205404962619 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12266 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12266]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12266])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12266) (a := (20563844517657 / 25000000000000 : ℝ)) (b := (168002382917 / 100000000000000 : ℝ)) (q := (1154617424473 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12266])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12266])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12266]

theorem cert12266_54 : CellCertificate 12266 (224806774171913 / 2500000000000000 : ℝ) (856215272164277 / 500000000000000000 : ℝ) (346205404962619 / 10000000000000000 : ℝ)
    (cell12266 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · have h := gap_lower (n := 12266) (a := (41110772967093 / 50000000000000 : ℝ)) (b := (168002382917 / 100000000000000 : ℝ)) (q := (2309238840683 / 100000000000000 : ℝ))
      (E := (cell12266 ⟨54, by decide⟩).energy) (xi := (346205404962619 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12266 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12266]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12266])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12266) (a := (41110772967093 / 50000000000000 : ℝ)) (b := (168002382917 / 100000000000000 : ℝ)) (q := (2309238840683 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12266])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12266])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12266]

theorem cert12266_55 : CellCertificate 12266 (224806774171913 / 2500000000000000 : ℝ) (856215272164277 / 500000000000000000 : ℝ) (346205404962619 / 10000000000000000 : ℝ)
    (cell12266 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · have h := gap_lower (n := 12266) (a := (10273467152271 / 12500000000000 : ℝ)) (b := (168002382917 / 100000000000000 : ℝ)) (q := (2309242806047 / 100000000000000 : ℝ))
      (E := (cell12266 ⟨55, by decide⟩).energy) (xi := (346205404962619 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12266 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12266]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12266])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12266) (a := (10273467152271 / 12500000000000 : ℝ)) (b := (168002382917 / 100000000000000 : ℝ)) (q := (2309242806047 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12266])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12266])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12266]

theorem cert12266_56 : CellCertificate 12266 (224806774171913 / 2500000000000000 : ℝ) (856215272164277 / 500000000000000000 : ℝ) (346205404962619 / 10000000000000000 : ℝ)
    (cell12266 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · have h := gap_lower (n := 12266) (a := (1643079037889 / 2000000000000 : ℝ)) (b := (168002382917 / 100000000000000 : ℝ)) (q := (461849360239 / 20000000000000 : ℝ))
      (E := (cell12266 ⟨56, by decide⟩).energy) (xi := (346205404962619 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12266 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12266]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12266])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12266) (a := (1643079037889 / 2000000000000 : ℝ)) (b := (168002382917 / 100000000000000 : ℝ)) (q := (461849360239 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12266])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12266])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12266]

theorem cert12266_57 : CellCertificate 12266 (224806774171913 / 2500000000000000 : ℝ) (856215272164277 / 500000000000000000 : ℝ) (346205404962619 / 10000000000000000 : ℝ)
    (cell12266 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · have h := gap_lower (n := 12266) (a := (82120189935049 / 100000000000000 : ℝ)) (b := (168002382917 / 100000000000000 : ℝ)) (q := (461850164613 / 20000000000000 : ℝ))
      (E := (cell12266 ⟨57, by decide⟩).energy) (xi := (346205404962619 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12266 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12266]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12266])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12266) (a := (82120189935049 / 100000000000000 : ℝ)) (b := (168002382917 / 100000000000000 : ℝ)) (q := (461850164613 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12266])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12266])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12266]

theorem cert12266_58 : CellCertificate 12266 (224806774171913 / 2500000000000000 : ℝ) (856215272164277 / 500000000000000000 : ℝ) (346205404962619 / 10000000000000000 : ℝ)
    (cell12266 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · have h := gap_lower (n := 12266) (a := (41043225656061 / 50000000000000 : ℝ)) (b := (168002382917 / 100000000000000 : ℝ)) (q := (2309254809259 / 100000000000000 : ℝ))
      (E := (cell12266 ⟨58, by decide⟩).energy) (xi := (346205404962619 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12266 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12266]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12266])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12266) (a := (41043225656061 / 50000000000000 : ℝ)) (b := (168002382917 / 100000000000000 : ℝ)) (q := (2309254809259 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12266])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12266])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12266]

theorem cert12266_59 : CellCertificate 12266 (224806774171913 / 2500000000000000 : ℝ) (856215272164277 / 500000000000000000 : ℝ) (346205404962619 / 10000000000000000 : ℝ)
    (cell12266 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · have h := gap_lower (n := 12266) (a := (82052735997967 / 100000000000000 : ℝ)) (b := (168002382917 / 100000000000000 : ℝ)) (q := (2309258815377 / 100000000000000 : ℝ))
      (E := (cell12266 ⟨59, by decide⟩).energy) (xi := (346205404962619 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12266 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12266]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12266])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12266) (a := (82052735997967 / 100000000000000 : ℝ)) (b := (168002382917 / 100000000000000 : ℝ)) (q := (2309258815377 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12266])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12266])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12266]

theorem cert12267_40 : CellCertificate 12267 (112399653724901 / 1250000000000000 : ℝ) (1712290900288029 / 1000000000000000000 : ℝ) (346176428900179 / 10000000000000000 : ℝ)
    (cell12267 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · have h := gap_lower (n := 12267) (a := (82697337086297 / 100000000000000 : ℝ)) (b := (83994252301 / 50000000000000 : ℝ)) (q := (288629627373 / 12500000000000 : ℝ))
      (E := (cell12267 ⟨40, by decide⟩).energy) (xi := (346176428900179 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12267 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12267]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12267])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12267) (a := (82697337086297 / 100000000000000 : ℝ)) (b := (83994252301 / 50000000000000 : ℝ)) (q := (288629627373 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12267])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12267])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12267]

theorem cert12267_41 : CellCertificate 12267 (112399653724901 / 1250000000000000 : ℝ) (1712290900288029 / 1000000000000000000 : ℝ) (346176428900179 / 10000000000000000 : ℝ)
    (cell12267 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · have h := gap_lower (n := 12267) (a := (10332899772351 / 12500000000000 : ℝ)) (b := (83994252301 / 50000000000000 : ℝ)) (q := (288630129417 / 12500000000000 : ℝ))
      (E := (cell12267 ⟨41, by decide⟩).energy) (xi := (346176428900179 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12267 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12267]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12267])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12267) (a := (10332899772351 / 12500000000000 : ℝ)) (b := (83994252301 / 50000000000000 : ℝ)) (q := (288630129417 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12267])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12267])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12267]

theorem cert12267_42 : CellCertificate 12267 (112399653724901 / 1250000000000000 : ℝ) (1712290900288029 / 1000000000000000000 : ℝ) (346176428900179 / 10000000000000000 : ℝ)
    (cell12267 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · have h := gap_lower (n := 12267) (a := (10328635383763 / 12500000000000 : ℝ)) (b := (83994252301 / 50000000000000 : ℝ)) (q := (1154522492869 / 50000000000000 : ℝ))
      (E := (cell12267 ⟨42, by decide⟩).energy) (xi := (346176428900179 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12267 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12267]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12267])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12267) (a := (10328635383763 / 12500000000000 : ℝ)) (b := (83994252301 / 50000000000000 : ℝ)) (q := (1154522492869 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12267])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12267])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12267]

theorem cert12267_43 : CellCertificate 12267 (112399653724901 / 1250000000000000 : ℝ) (1712290900288029 / 1000000000000000000 : ℝ) (346176428900179 / 10000000000000000 : ℝ)
    (cell12267 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · have h := gap_lower (n := 12267) (a := (82594991730153 / 100000000000000 : ℝ)) (b := (83994252301 / 50000000000000 : ℝ)) (q := (461809797509 / 20000000000000 : ℝ))
      (E := (cell12267 ⟨43, by decide⟩).energy) (xi := (346176428900179 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12267 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12267]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12267])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12267) (a := (82594991730153 / 100000000000000 : ℝ)) (b := (83994252301 / 50000000000000 : ℝ)) (q := (461809797509 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12267])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12267])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12267]

theorem cert12267_44 : CellCertificate 12267 (112399653724901 / 1250000000000000 : ℝ) (1712290900288029 / 1000000000000000000 : ℝ) (346176428900179 / 10000000000000000 : ℝ)
    (cell12267 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · have h := gap_lower (n := 12267) (a := (41280462064539 / 50000000000000 : ℝ)) (b := (83994252301 / 50000000000000 : ℝ)) (q := (577263245421 / 25000000000000 : ℝ))
      (E := (cell12267 ⟨44, by decide⟩).energy) (xi := (346176428900179 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12267 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12267]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12267])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12267) (a := (41280462064539 / 50000000000000 : ℝ)) (b := (83994252301 / 50000000000000 : ℝ)) (q := (577263245421 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12267])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12267])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12267]

theorem cert12267_45 : CellCertificate 12267 (112399653724901 / 1250000000000000 : ℝ) (1712290900288029 / 1000000000000000000 : ℝ) (346176428900179 / 10000000000000000 : ℝ)
    (cell12267 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · have h := gap_lower (n := 12267) (a := (2578965007411 / 3125000000000 : ℝ)) (b := (83994252301 / 50000000000000 : ℝ)) (q := (577264256603 / 25000000000000 : ℝ))
      (E := (cell12267 ⟨45, by decide⟩).energy) (xi := (346176428900179 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12267 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12267]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12267])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12267) (a := (2578965007411 / 3125000000000 : ℝ)) (b := (83994252301 / 50000000000000 : ℝ)) (q := (577264256603 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12267])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12267])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12267]

theorem cert12267_46 : CellCertificate 12267 (112399653724901 / 1250000000000000 : ℝ) (1712290900288029 / 1000000000000000000 : ℝ) (346176428900179 / 10000000000000000 : ℝ)
    (cell12267 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · have h := gap_lower (n := 12267) (a := (20623215006199 / 25000000000000 : ℝ)) (b := (83994252301 / 50000000000000 : ℝ)) (q := (230906100333 / 10000000000000 : ℝ))
      (E := (cell12267 ⟨46, by decide⟩).energy) (xi := (346176428900179 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12267 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12267]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12267])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12267) (a := (20623215006199 / 25000000000000 : ℝ)) (b := (83994252301 / 50000000000000 : ℝ)) (q := (230906100333 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12267])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12267])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12267]

theorem cert12267_47 : CellCertificate 12267 (112399653724901 / 1250000000000000 : ℝ) (1712290900288029 / 1000000000000000000 : ℝ) (346176428900179 / 10000000000000000 : ℝ)
    (cell12267 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · have h := gap_lower (n := 12267) (a := (10307357932823 / 12500000000000 : ℝ)) (b := (83994252301 / 50000000000000 : ℝ)) (q := (288633121279 / 12500000000000 : ℝ))
      (E := (cell12267 ⟨47, by decide⟩).energy) (xi := (346176428900179 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12267 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12267]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12267])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12267) (a := (10307357932823 / 12500000000000 : ℝ)) (b := (83994252301 / 50000000000000 : ℝ)) (q := (288633121279 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12267])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12267])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12267]

theorem cert12267_48 : CellCertificate 12267 (112399653724901 / 1250000000000000 : ℝ) (1712290900288029 / 1000000000000000000 : ℝ) (346176428900179 / 10000000000000000 : ℝ)
    (cell12267 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · have h := gap_lower (n := 12267) (a := (82424890521237 / 100000000000000 : ℝ)) (b := (83994252301 / 50000000000000 : ℝ)) (q := (288633623099 / 12500000000000 : ℝ))
      (E := (cell12267 ⟨48, by decide⟩).energy) (xi := (346176428900179 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12267 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12267]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12267])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12267) (a := (82424890521237 / 100000000000000 : ℝ)) (b := (83994252301 / 50000000000000 : ℝ)) (q := (288633623099 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12267])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12267])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12267]

theorem cert12267_49 : CellCertificate 12267 (112399653724901 / 1250000000000000 : ℝ) (1712290900288029 / 1000000000000000000 : ℝ) (346176428900179 / 10000000000000000 : ℝ)
    (cell12267 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · have h := gap_lower (n := 12267) (a := (82390941171621 / 100000000000000 : ℝ)) (b := (83994252301 / 50000000000000 : ℝ)) (q := (461814597347 / 20000000000000 : ℝ))
      (E := (cell12267 ⟨49, by decide⟩).energy) (xi := (346176428900179 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12267 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12267]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12267])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12267) (a := (82390941171621 / 100000000000000 : ℝ)) (b := (83994252301 / 50000000000000 : ℝ)) (q := (461814597347 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12267])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12267])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12267]

theorem cert12267_50 : CellCertificate 12267 (112399653724901 / 1250000000000000 : ℝ) (1712290900288029 / 1000000000000000000 : ℝ) (346176428900179 / 10000000000000000 : ℝ)
    (cell12267 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · have h := gap_lower (n := 12267) (a := (82357015384753 / 100000000000000 : ℝ)) (b := (83994252301 / 50000000000000 : ℝ)) (q := (2309076974411 / 100000000000000 : ℝ))
      (E := (cell12267 ⟨50, by decide⟩).energy) (xi := (346176428900179 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12267 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12267]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12267])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12267) (a := (82357015384753 / 100000000000000 : ℝ)) (b := (83994252301 / 50000000000000 : ℝ)) (q := (2309076974411 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12267])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12267])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12267]

theorem cert12267_51 : CellCertificate 12267 (112399653724901 / 1250000000000000 : ℝ) (1712290900288029 / 1000000000000000000 : ℝ) (346176428900179 / 10000000000000000 : ℝ)
    (cell12267 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · have h := gap_lower (n := 12267) (a := (5145194570737 / 6250000000000 : ℝ)) (b := (83994252301 / 50000000000000 : ℝ)) (q := (1154540502459 / 50000000000000 : ℝ))
      (E := (cell12267 ⟨51, by decide⟩).energy) (xi := (346176428900179 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12267 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12267]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12267])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12267) (a := (5145194570737 / 6250000000000 : ℝ)) (b := (83994252301 / 50000000000000 : ℝ)) (q := (1154540502459 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12267])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12267])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12267]

theorem cert12267_52 : CellCertificate 12267 (112399653724901 / 1250000000000000 : ℝ) (1712290900288029 / 1000000000000000000 : ℝ) (346176428900179 / 10000000000000000 : ℝ)
    (cell12267 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · have h := gap_lower (n := 12267) (a := (16457846876809 / 20000000000000 : ℝ)) (b := (83994252301 / 50000000000000 : ℝ)) (q := (57727123957 / 2500000000000 : ℝ))
      (E := (cell12267 ⟨52, by decide⟩).energy) (xi := (346176428900179 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12267 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12267]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12267])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12267) (a := (16457846876809 / 20000000000000 : ℝ)) (b := (83994252301 / 50000000000000 : ℝ)) (q := (57727123957 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12267])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12267])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12267]

theorem cert12267_53 : CellCertificate 12267 (112399653724901 / 1250000000000000 : ℝ) (1712290900288029 / 1000000000000000000 : ℝ) (346176428900179 / 10000000000000000 : ℝ)
    (cell12267 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · have h := gap_lower (n := 12267) (a := (16065503733 / 19531250000 : ℝ)) (b := (83994252301 / 50000000000000 : ℝ)) (q := (1154544475077 / 50000000000000 : ℝ))
      (E := (cell12267 ⟨53, by decide⟩).energy) (xi := (346176428900179 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12267 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12267]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12267])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12267) (a := (16065503733 / 19531250000 : ℝ)) (b := (83994252301 / 50000000000000 : ℝ)) (q := (1154544475077 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12267])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12267])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12267]

theorem cert12267_54 : CellCertificate 12267 (112399653724901 / 1250000000000000 : ℝ) (1712290900288029 / 1000000000000000000 : ℝ) (346176428900179 / 10000000000000000 : ℝ)
    (cell12267 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · have h := gap_lower (n := 12267) (a := (20555386822533 / 25000000000000 : ℝ)) (b := (83994252301 / 50000000000000 : ℝ)) (q := (2309092978109 / 100000000000000 : ℝ))
      (E := (cell12267 ⟨54, by decide⟩).energy) (xi := (346176428900179 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12267 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12267]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12267])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12267) (a := (20555386822533 / 25000000000000 : ℝ)) (b := (83994252301 / 50000000000000 : ℝ)) (q := (2309092978109 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12267])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12267])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12267]

theorem cert12267_55 : CellCertificate 12267 (112399653724901 / 1250000000000000 : ℝ) (1712290900288029 / 1000000000000000000 : ℝ) (346176428900179 / 10000000000000000 : ℝ)
    (cell12267 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · have h := gap_lower (n := 12267) (a := (16437547777459 / 20000000000000 : ℝ)) (b := (83994252301 / 50000000000000 : ℝ)) (q := (2309096980447 / 100000000000000 : ℝ))
      (E := (cell12267 ⟨55, by decide⟩).energy) (xi := (346176428900179 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12267 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12267]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12267])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12267) (a := (16437547777459 / 20000000000000 : ℝ)) (b := (83994252301 / 50000000000000 : ℝ)) (q := (2309096980447 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12267])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12267])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12267]

theorem cert12267_56 : CellCertificate 12267 (112399653724901 / 1250000000000000 : ℝ) (1712290900288029 / 1000000000000000000 : ℝ) (346176428900179 / 10000000000000000 : ℝ)
    (cell12267 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · have h := gap_lower (n := 12267) (a := (82153953876327 / 100000000000000 : ℝ)) (b := (83994252301 / 50000000000000 : ℝ)) (q := (577275238561 / 25000000000000 : ℝ))
      (E := (cell12267 ⟨56, by decide⟩).energy) (xi := (346176428900179 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12267 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12267]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12267])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12267) (a := (82153953876327 / 100000000000000 : ℝ)) (b := (83994252301 / 50000000000000 : ℝ)) (q := (577275238561 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12267])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12267])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12267]

theorem cert12267_57 : CellCertificate 12267 (112399653724901 / 1250000000000000 : ℝ) (1712290900288029 / 1000000000000000000 : ℝ) (346176428900179 / 10000000000000000 : ℝ)
    (cell12267 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · have h := gap_lower (n := 12267) (a := (16424038445849 / 20000000000000 : ℝ)) (b := (83994252301 / 50000000000000 : ℝ)) (q := (230910495547 / 10000000000000 : ℝ))
      (E := (cell12267 ⟨57, by decide⟩).energy) (xi := (346176428900179 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12267 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12267]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12267])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12267) (a := (16424038445849 / 20000000000000 : ℝ)) (b := (83994252301 / 50000000000000 : ℝ)) (q := (230910495547 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12267])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12267])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12267]

theorem cert12267_58 : CellCertificate 12267 (112399653724901 / 1250000000000000 : ℝ) (1712290900288029 / 1000000000000000000 : ℝ) (346176428900179 / 10000000000000000 : ℝ)
    (cell12267 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · have h := gap_lower (n := 12267) (a := (82086453918209 / 100000000000000 : ℝ)) (b := (83994252301 / 50000000000000 : ℝ)) (q := (577277245213 / 25000000000000 : ℝ))
      (E := (cell12267 ⟨58, by decide⟩).energy) (xi := (346176428900179 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12267 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12267]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12267])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12267) (a := (82086453918209 / 100000000000000 : ℝ)) (b := (83994252301 / 50000000000000 : ℝ)) (q := (577277245213 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12267])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12267])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12267]

theorem cert12267_59 : CellCertificate 12267 (112399653724901 / 1250000000000000 : ℝ) (1712290900288029 / 1000000000000000000 : ℝ) (346176428900179 / 10000000000000000 : ℝ)
    (cell12267 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · have h := gap_lower (n := 12267) (a := (82052738915513 / 100000000000000 : ℝ)) (b := (83994252301 / 50000000000000 : ℝ)) (q := (1154556483881 / 50000000000000 : ℝ))
      (E := (cell12267 ⟨59, by decide⟩).energy) (xi := (346176428900179 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12267 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12267]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12267])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12267) (a := (82052738915513 / 100000000000000 : ℝ)) (b := (83994252301 / 50000000000000 : ℝ)) (q := (1154556483881 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12267])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12267])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12267]

theorem cert12268_40 : CellCertificate 12268 (899167367602043 / 10000000000000000 : ℝ) (68486051160833 / 40000000000000000 : ℝ) (346147457810031 / 10000000000000000 : ℝ)
    (cell12268 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · have h := gap_lower (n := 12268) (a := (20674333503243 / 25000000000000 : ℝ)) (b := (167974628611 / 100000000000000 : ℝ)) (q := (2308891243123 / 100000000000000 : ℝ))
      (E := (cell12268 ⟨40, by decide⟩).energy) (xi := (346147457810031 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12268 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12268]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12268])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12268) (a := (20674333503243 / 25000000000000 : ℝ)) (b := (167974628611 / 100000000000000 : ℝ)) (q := (2308891243123 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12268])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12268])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12268]

theorem cert12268_41 : CellCertificate 12268 (899167367602043 / 10000000000000000 : ℝ) (68486051160833 / 40000000000000000 : ℝ) (346147457810031 / 10000000000000000 : ℝ)
    (cell12268 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · have h := gap_lower (n := 12268) (a := (16532639084949 / 20000000000000 : ℝ)) (b := (167974628611 / 100000000000000 : ℝ)) (q := (2308895227333 / 100000000000000 : ℝ))
      (E := (cell12268 ⟨41, by decide⟩).energy) (xi := (346147457810031 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12268 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12268]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12268])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12268) (a := (16532639084949 / 20000000000000 : ℝ)) (b := (167974628611 / 100000000000000 : ℝ)) (q := (2308895227333 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12268])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12268])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12268]

theorem cert12268_42 : CellCertificate 12268 (899167367602043 / 10000000000000000 : ℝ) (68486051160833 / 40000000000000000 : ℝ) (346147457810031 / 10000000000000000 : ℝ)
    (cell12268 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · have h := gap_lower (n := 12268) (a := (82629080634859 / 100000000000000 : ℝ)) (b := (167974628611 / 100000000000000 : ℝ)) (q := (2308899263813 / 100000000000000 : ℝ))
      (E := (cell12268 ⟨42, by decide⟩).energy) (xi := (346147457810031 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12268 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12268]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12268])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12268) (a := (82629080634859 / 100000000000000 : ℝ)) (b := (167974628611 / 100000000000000 : ℝ)) (q := (2308899263813 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12268])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12268])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12268]

theorem cert12268_43 : CellCertificate 12268 (899167367602043 / 10000000000000000 : ℝ) (68486051160833 / 40000000000000000 : ℝ) (346147457810031 / 10000000000000000 : ℝ)
    (cell12268 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · have h := gap_lower (n := 12268) (a := (82594989613287 / 100000000000000 : ℝ)) (b := (167974628611 / 100000000000000 : ℝ)) (q := (2308903234959 / 100000000000000 : ℝ))
      (E := (cell12268 ⟨43, by decide⟩).energy) (xi := (346147457810031 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12268 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12268]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12268])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12268) (a := (82594989613287 / 100000000000000 : ℝ)) (b := (167974628611 / 100000000000000 : ℝ)) (q := (2308903234959 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12268])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12268])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12268]

theorem cert12268_44 : CellCertificate 12268 (899167367602043 / 10000000000000000 : ℝ) (68486051160833 / 40000000000000000 : ℝ) (346147457810031 / 10000000000000000 : ℝ)
    (cell12268 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · have h := gap_lower (n := 12268) (a := (82560922330149 / 100000000000000 : ℝ)) (b := (167974628611 / 100000000000000 : ℝ)) (q := (72153351811 / 3125000000000 : ℝ))
      (E := (cell12268 ⟨44, by decide⟩).energy) (xi := (346147457810031 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12268 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12268]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12268])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12268) (a := (82560922330149 / 100000000000000 : ℝ)) (b := (167974628611 / 100000000000000 : ℝ)) (q := (72153351811 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12268])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12268])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12268]

theorem cert12268_45 : CellCertificate 12268 (899167367602043 / 10000000000000000 : ℝ) (68486051160833 / 40000000000000000 : ℝ) (346147457810031 / 10000000000000000 : ℝ)
    (cell12268 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · have h := gap_lower (n := 12268) (a := (82526878755719 / 100000000000000 : ℝ)) (b := (167974628611 / 100000000000000 : ℝ)) (q := (2308911214657 / 100000000000000 : ℝ))
      (E := (cell12268 ⟨45, by decide⟩).energy) (xi := (346147457810031 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12268 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12268]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12268])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12268) (a := (82526878755719 / 100000000000000 : ℝ)) (b := (167974628611 / 100000000000000 : ℝ)) (q := (2308911214657 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12268])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12268])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12268]

theorem cert12268_46 : CellCertificate 12268 (899167367602043 / 10000000000000000 : ℝ) (68486051160833 / 40000000000000000 : ℝ) (346147457810031 / 10000000000000000 : ℝ)
    (cell12268 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · have h := gap_lower (n := 12268) (a := (82492858860423 / 100000000000000 : ℝ)) (b := (167974628611 / 100000000000000 : ℝ)) (q := (144307201369 / 6250000000000 : ℝ))
      (E := (cell12268 ⟨46, by decide⟩).energy) (xi := (346147457810031 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12268 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12268]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12268])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12268) (a := (82492858860423 / 100000000000000 : ℝ)) (b := (167974628611 / 100000000000000 : ℝ)) (q := (144307201369 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12268])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12268])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12268]

theorem cert12268_47 : CellCertificate 12268 (899167367602043 / 10000000000000000 : ℝ) (68486051160833 / 40000000000000000 : ℝ) (346147457810031 / 10000000000000000 : ℝ)
    (cell12268 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · have h := gap_lower (n := 12268) (a := (82458862614831 / 100000000000000 : ℝ)) (b := (167974628611 / 100000000000000 : ℝ)) (q := (2308919219899 / 100000000000000 : ℝ))
      (E := (cell12268 ⟨47, by decide⟩).energy) (xi := (346147457810031 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12268 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12268]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12268])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12268) (a := (82458862614831 / 100000000000000 : ℝ)) (b := (167974628611 / 100000000000000 : ℝ)) (q := (2308919219899 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12268])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12268])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12268]

theorem cert12268_48 : CellCertificate 12268 (899167367602043 / 10000000000000000 : ℝ) (68486051160833 / 40000000000000000 : ℝ) (346147457810031 / 10000000000000000 : ℝ)
    (cell12268 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · have h := gap_lower (n := 12268) (a := (41212444994833 / 50000000000000 : ℝ)) (b := (167974628611 / 100000000000000 : ℝ)) (q := (2308923207421 / 100000000000000 : ℝ))
      (E := (cell12268 ⟨48, by decide⟩).energy) (xi := (346147457810031 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12268 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12268]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12268])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12268) (a := (41212444994833 / 50000000000000 : ℝ)) (b := (167974628611 / 100000000000000 : ℝ)) (q := (2308923207421 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12268])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12268])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12268]

theorem cert12268_49 : CellCertificate 12268 (899167367602043 / 10000000000000000 : ℝ) (68486051160833 / 40000000000000000 : ℝ) (346147457810031 / 10000000000000000 : ℝ)
    (cell12268 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · have h := gap_lower (n := 12268) (a := (82390940955797 / 100000000000000 : ℝ)) (b := (167974628611 / 100000000000000 : ℝ)) (q := (2308927241953 / 100000000000000 : ℝ))
      (E := (cell12268 ⟨49, by decide⟩).energy) (xi := (346147457810031 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12268 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12268]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12268])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12268) (a := (82390940955797 / 100000000000000 : ℝ)) (b := (167974628611 / 100000000000000 : ℝ)) (q := (2308927241953 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12268])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12268])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12268]

theorem cert12268_50 : CellCertificate 12268 (899167367602043 / 10000000000000000 : ℝ) (68486051160833 / 40000000000000000 : ℝ) (346147457810031 / 10000000000000000 : ℝ)
    (cell12268 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · have h := gap_lower (n := 12268) (a := (82357015484239 / 100000000000000 : ℝ)) (b := (167974628611 / 100000000000000 : ℝ)) (q := (1154465602019 / 50000000000000 : ℝ))
      (E := (cell12268 ⟨50, by decide⟩).energy) (xi := (346147457810031 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12268 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12268]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12268])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12268) (a := (82357015484239 / 100000000000000 : ℝ)) (b := (167974628611 / 100000000000000 : ℝ)) (q := (1154465602019 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12268])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12268])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12268]

theorem cert12268_51 : CellCertificate 12268 (899167367602043 / 10000000000000000 : ℝ) (68486051160833 / 40000000000000000 : ℝ) (346147457810031 / 10000000000000000 : ℝ)
    (cell12268 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · have h := gap_lower (n := 12268) (a := (82323113546153 / 100000000000000 : ℝ)) (b := (167974628611 / 100000000000000 : ℝ)) (q := (1154467604833 / 50000000000000 : ℝ))
      (E := (cell12268 ⟨51, by decide⟩).energy) (xi := (346147457810031 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12268 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12268]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12268])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12268) (a := (82323113546153 / 100000000000000 : ℝ)) (b := (167974628611 / 100000000000000 : ℝ)) (q := (1154467604833 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12268])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12268])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12268]

theorem cert12268_52 : CellCertificate 12268 (899167367602043 / 10000000000000000 : ℝ) (68486051160833 / 40000000000000000 : ℝ) (346147457810031 / 10000000000000000 : ℝ)
    (cell12268 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · have h := gap_lower (n := 12268) (a := (82289235112847 / 100000000000000 : ℝ)) (b := (167974628611 / 100000000000000 : ℝ)) (q := (577234799461 / 25000000000000 : ℝ))
      (E := (cell12268 ⟨52, by decide⟩).energy) (xi := (346147457810031 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12268 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12268]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12268])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12268) (a := (82289235112847 / 100000000000000 : ℝ)) (b := (167974628611 / 100000000000000 : ℝ)) (q := (577234799461 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12268])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12268])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12268]

theorem cert12268_53 : CellCertificate 12268 (899167367602043 / 10000000000000000 : ℝ) (68486051160833 / 40000000000000000 : ℝ) (346147457810031 / 10000000000000000 : ℝ)
    (cell12268 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · have h := gap_lower (n := 12268) (a := (8225538015577 / 10000000000000 : ℝ)) (b := (167974628611 / 100000000000000 : ℝ)) (q := (2308943225291 / 100000000000000 : ℝ))
      (E := (cell12268 ⟨53, by decide⟩).energy) (xi := (346147457810031 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12268 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12268]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12268])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12268) (a := (8225538015577 / 10000000000000 : ℝ)) (b := (167974628611 / 100000000000000 : ℝ)) (q := (2308943225291 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12268])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12268])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12268]

theorem cert12268_54 : CellCertificate 12268 (899167367602043 / 10000000000000000 : ℝ) (68486051160833 / 40000000000000000 : ℝ) (346147457810031 / 10000000000000000 : ℝ)
    (cell12268 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · have h := gap_lower (n := 12268) (a := (20555387161629 / 25000000000000 : ℝ)) (b := (167974628611 / 100000000000000 : ℝ)) (q := (230894717151 / 10000000000000 : ℝ))
      (E := (cell12268 ⟨54, by decide⟩).energy) (xi := (346147457810031 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12268 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12268]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12268])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12268) (a := (20555387161629 / 25000000000000 : ℝ)) (b := (167974628611 / 100000000000000 : ℝ)) (q := (230894717151 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12268])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12268])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12268]

theorem cert12268_55 : CellCertificate 12268 (899167367602043 / 10000000000000000 : ℝ) (68486051160833 / 40000000000000000 : ℝ) (346147457810031 / 10000000000000000 : ℝ)
    (cell12268 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · have h := gap_lower (n := 12268) (a := (82187740556821 / 100000000000000 : ℝ)) (b := (167974628611 / 100000000000000 : ℝ)) (q := (2308951210887 / 100000000000000 : ℝ))
      (E := (cell12268 ⟨55, by decide⟩).energy) (xi := (346147457810031 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12268 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12268]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12268])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12268) (a := (82187740556821 / 100000000000000 : ℝ)) (b := (167974628611 / 100000000000000 : ℝ)) (q := (2308951210887 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12268])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12268])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12268]

theorem cert12268_56 : CellCertificate 12268 (899167367602043 / 10000000000000000 : ℝ) (68486051160833 / 40000000000000000 : ℝ) (346147457810031 / 10000000000000000 : ℝ)
    (cell12268 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · have h := gap_lower (n := 12268) (a := (20538488964641 / 25000000000000 : ℝ)) (b := (167974628611 / 100000000000000 : ℝ)) (q := (461791032679 / 20000000000000 : ℝ))
      (E := (cell12268 ⟨56, by decide⟩).energy) (xi := (346147457810031 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12268 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12268]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12268])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12268) (a := (20538488964641 / 25000000000000 : ℝ)) (b := (167974628611 / 100000000000000 : ℝ)) (q := (461791032679 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12268])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12268])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12268]

theorem cert12268_57 : CellCertificate 12268 (899167367602043 / 10000000000000000 : ℝ) (68486051160833 / 40000000000000000 : ℝ) (346147457810031 / 10000000000000000 : ℝ)
    (cell12268 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · have h := gap_lower (n := 12268) (a := (82120194523763 / 100000000000000 : ℝ)) (b := (167974628611 / 100000000000000 : ℝ)) (q := (288619900393 / 12500000000000 : ℝ))
      (E := (cell12268 ⟨57, by decide⟩).energy) (xi := (346147457810031 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12268 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12268]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12268])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12268) (a := (82120194523763 / 100000000000000 : ℝ)) (b := (167974628611 / 100000000000000 : ℝ)) (q := (288619900393 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12268])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12268])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12268]

theorem cert12268_58 : CellCertificate 12268 (899167367602043 / 10000000000000000 : ℝ) (68486051160833 / 40000000000000000 : ℝ) (346147457810031 / 10000000000000000 : ℝ)
    (cell12268 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · have h := gap_lower (n := 12268) (a := (82086456524577 / 100000000000000 : ℝ)) (b := (167974628611 / 100000000000000 : ℝ)) (q := (92358528347 / 4000000000000 : ℝ))
      (E := (cell12268 ⟨58, by decide⟩).energy) (xi := (346147457810031 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12268 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12268]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12268])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12268) (a := (82086456524577 / 100000000000000 : ℝ)) (b := (167974628611 / 100000000000000 : ℝ)) (q := (92358528347 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12268])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12268])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12268]

theorem cert12268_59 : CellCertificate 12268 (899167367602043 / 10000000000000000 : ℝ) (68486051160833 / 40000000000000000 : ℝ) (346147457810031 / 10000000000000000 : ℝ)
    (cell12268 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · have h := gap_lower (n := 12268) (a := (82052741833303 / 100000000000000 : ℝ)) (b := (167974628611 / 100000000000000 : ℝ)) (q := (1154483588219 / 50000000000000 : ℝ))
      (E := (cell12268 ⟨59, by decide⟩).energy) (xi := (346147457810031 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12268 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12268]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12268])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12268) (a := (82052741833303 / 100000000000000 : ℝ)) (b := (167974628611 / 100000000000000 : ℝ)) (q := (1154483588219 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12268])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12268])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12268]

theorem cert12269_40 : CellCertificate 12269 (899137510094999 / 10000000000000000 : ℝ) (1712011680521373 / 1000000000000000000 : ℝ) (173059245845363 / 5000000000000000 : ℝ)
    (cell12269 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · have h := gap_lower (n := 12269) (a := (82697330940641 / 100000000000000 : ℝ)) (b := (167960754941 / 100000000000000 : ℝ)) (q := (2308745581043 / 100000000000000 : ℝ))
      (E := (cell12269 ⟨40, by decide⟩).energy) (xi := (173059245845363 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12269 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12269]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12269])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12269) (a := (82697330940641 / 100000000000000 : ℝ)) (b := (167960754941 / 100000000000000 : ℝ)) (q := (2308745581043 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12269])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12269])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12269]

theorem cert12269_41 : CellCertificate 12269 (899137510094999 / 10000000000000000 : ℝ) (1712011680521373 / 1000000000000000000 : ℝ) (173059245845363 / 5000000000000000 : ℝ)
    (cell12269 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · have h := gap_lower (n := 12269) (a := (16532638534327 / 20000000000000 : ℝ)) (b := (167960754941 / 100000000000000 : ℝ)) (q := (2308749533199 / 100000000000000 : ℝ))
      (E := (cell12269 ⟨41, by decide⟩).energy) (xi := (173059245845363 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12269 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12269]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12269])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12269) (a := (16532638534327 / 20000000000000 : ℝ)) (b := (167960754941 / 100000000000000 : ℝ)) (q := (2308749533199 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12269])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12269])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12269]

theorem cert12269_42 : CellCertificate 12269 (899137510094999 / 10000000000000000 : ℝ) (1712011680521373 / 1000000000000000000 : ℝ) (173059245845363 / 5000000000000000 : ℝ)
    (cell12269 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · have h := gap_lower (n := 12269) (a := (82629078200529 / 100000000000000 : ℝ)) (b := (167960754941 / 100000000000000 : ℝ)) (q := (2308753538343 / 100000000000000 : ℝ))
      (E := (cell12269 ⟨42, by decide⟩).energy) (xi := (173059245845363 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12269 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12269]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12269])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12269) (a := (82629078200529 / 100000000000000 : ℝ)) (b := (167960754941 / 100000000000000 : ℝ)) (q := (2308753538343 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12269])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12269])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12269]

theorem cert12269_43 : CellCertificate 12269 (899137510094999 / 10000000000000000 : ℝ) (1712011680521373 / 1000000000000000000 : ℝ) (173059245845363 / 5000000000000000 : ℝ)
    (cell12269 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · have h := gap_lower (n := 12269) (a := (41297493748647 / 50000000000000 : ℝ)) (b := (167960754941 / 100000000000000 : ℝ)) (q := (461751507529 / 20000000000000 : ℝ))
      (E := (cell12269 ⟨43, by decide⟩).energy) (xi := (173059245845363 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12269 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12269]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12269])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12269) (a := (41297493748647 / 50000000000000 : ℝ)) (b := (167960754941 / 100000000000000 : ℝ)) (q := (461751507529 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12269])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12269])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12269]

theorem cert12269_44 : CellCertificate 12269 (899137510094999 / 10000000000000000 : ℝ) (1712011680521373 / 1000000000000000000 : ℝ) (173059245845363 / 5000000000000000 : ℝ)
    (cell12269 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · have h := gap_lower (n := 12269) (a := (82560920532053 / 100000000000000 : ℝ)) (b := (167960754941 / 100000000000000 : ℝ)) (q := (57719038269 / 2500000000000 : ℝ))
      (E := (cell12269 ⟨44, by decide⟩).energy) (xi := (173059245845363 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12269 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12269]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12269])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12269) (a := (82560920532053 / 100000000000000 : ℝ)) (b := (167960754941 / 100000000000000 : ℝ)) (q := (57719038269 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12269])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12269])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12269]

theorem cert12269_45 : CellCertificate 12269 (899137510094999 / 10000000000000000 : ℝ) (1712011680521373 / 1000000000000000000 : ℝ) (173059245845363 / 5000000000000000 : ℝ)
    (cell12269 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · have h := gap_lower (n := 12269) (a := (82526877275081 / 100000000000000 : ℝ)) (b := (167960754941 / 100000000000000 : ℝ)) (q := (2308765517121 / 100000000000000 : ℝ))
      (E := (cell12269 ⟨45, by decide⟩).energy) (xi := (173059245845363 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12269 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12269]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12269])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12269) (a := (82526877275081 / 100000000000000 : ℝ)) (b := (167960754941 / 100000000000000 : ℝ)) (q := (2308765517121 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12269])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12269])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12269]

theorem cert12269_46 : CellCertificate 12269 (899137510094999 / 10000000000000000 : ℝ) (1712011680521373 / 1000000000000000000 : ℝ) (173059245845363 / 5000000000000000 : ℝ)
    (cell12269 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · have h := gap_lower (n := 12269) (a := (82492857696803 / 100000000000000 : ℝ)) (b := (167960754941 / 100000000000000 : ℝ)) (q := (2308769554789 / 100000000000000 : ℝ))
      (E := (cell12269 ⟨46, by decide⟩).energy) (xi := (173059245845363 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12269 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12269]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12269])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12269) (a := (82492857696803 / 100000000000000 : ℝ)) (b := (167960754941 / 100000000000000 : ℝ)) (q := (2308769554789 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12269])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12269])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12269]

theorem cert12269_47 : CellCertificate 12269 (899137510094999 / 10000000000000000 : ℝ) (1712011680521373 / 1000000000000000000 : ℝ) (173059245845363 / 5000000000000000 : ℝ)
    (cell12269 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · have h := gap_lower (n := 12269) (a := (5153678860487 / 6250000000000 : ℝ)) (b := (167960754941 / 100000000000000 : ℝ)) (q := (288596690637 / 12500000000000 : ℝ))
      (E := (cell12269 ⟨47, by decide⟩).energy) (xi := (173059245845363 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12269 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12269]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12269])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12269) (a := (5153678860487 / 6250000000000 : ℝ)) (b := (167960754941 / 100000000000000 : ℝ)) (q := (288596690637 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12269])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12269])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12269]

theorem cert12269_48 : CellCertificate 12269 (899137510094999 / 10000000000000000 : ℝ) (1712011680521373 / 1000000000000000000 : ℝ) (173059245845363 / 5000000000000000 : ℝ)
    (cell12269 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · have h := gap_lower (n := 12269) (a := (8242488945877 / 10000000000000 : ℝ)) (b := (167960754941 / 100000000000000 : ℝ)) (q := (288597193067 / 12500000000000 : ℝ))
      (E := (cell12269 ⟨48, by decide⟩).energy) (xi := (173059245845363 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12269 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12269]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12269])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12269) (a := (8242488945877 / 10000000000000 : ℝ)) (b := (167960754941 / 100000000000000 : ℝ)) (q := (288597193067 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12269])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12269])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12269]

theorem cert12269_49 : CellCertificate 12269 (899137510094999 / 10000000000000000 : ℝ) (1712011680521373 / 1000000000000000000 : ℝ) (173059245845363 / 5000000000000000 : ℝ)
    (cell12269 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · have h := gap_lower (n := 12269) (a := (80459903067 / 97656250000 : ℝ)) (b := (167960754941 / 100000000000000 : ℝ)) (q := (2308781552829 / 100000000000000 : ℝ))
      (E := (cell12269 ⟨49, by decide⟩).energy) (xi := (173059245845363 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12269 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12269]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12269])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12269) (a := (80459903067 / 97656250000 : ℝ)) (b := (167960754941 / 100000000000000 : ℝ)) (q := (2308781552829 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12269])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12269])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12269]

theorem cert12269_50 : CellCertificate 12269 (899137510094999 / 10000000000000000 : ℝ) (1712011680521373 / 1000000000000000000 : ℝ) (173059245845363 / 5000000000000000 : ℝ)
    (cell12269 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · have h := gap_lower (n := 12269) (a := (257365673701 / 312500000000 : ℝ)) (b := (167960754941 / 100000000000000 : ℝ)) (q := (2308785548327 / 100000000000000 : ℝ))
      (E := (cell12269 ⟨50, by decide⟩).energy) (xi := (173059245845363 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12269 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12269]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12269])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12269) (a := (257365673701 / 312500000000 : ℝ)) (b := (167960754941 / 100000000000000 : ℝ)) (q := (2308785548327 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12269])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12269])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12269]

theorem cert12269_51 : CellCertificate 12269 (899137510094999 / 10000000000000000 : ℝ) (1712011680521373 / 1000000000000000000 : ℝ) (173059245845363 / 5000000000000000 : ℝ)
    (cell12269 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · have h := gap_lower (n := 12269) (a := (82323113961071 / 100000000000000 : ℝ)) (b := (167960754941 / 100000000000000 : ℝ)) (q := (1154394764581 / 50000000000000 : ℝ))
      (E := (cell12269 ⟨51, by decide⟩).energy) (xi := (173059245845363 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12269 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12269]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12269])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12269) (a := (82323113961071 / 100000000000000 : ℝ)) (b := (167960754941 / 100000000000000 : ℝ)) (q := (1154394764581 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12269])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12269])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12269]

theorem cert12269_52 : CellCertificate 12269 (899137510094999 / 10000000000000000 : ℝ) (1712011680521373 / 1000000000000000000 : ℝ) (173059245845363 / 5000000000000000 : ℝ)
    (cell12269 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · have h := gap_lower (n := 12269) (a := (16457847168433 / 20000000000000 : ℝ)) (b := (167960754941 / 100000000000000 : ℝ)) (q := (2308793493259 / 100000000000000 : ℝ))
      (E := (cell12269 ⟨52, by decide⟩).energy) (xi := (173059245845363 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12269 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12269]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12269])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12269) (a := (16457847168433 / 20000000000000 : ℝ)) (b := (167960754941 / 100000000000000 : ℝ)) (q := (2308793493259 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12269])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12269])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12269]

theorem cert12269_53 : CellCertificate 12269 (899137510094999 / 10000000000000000 : ℝ) (1712011680521373 / 1000000000000000000 : ℝ) (173059245845363 / 5000000000000000 : ℝ)
    (cell12269 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · have h := gap_lower (n := 12269) (a := (5140961324941 / 6250000000000 : ℝ)) (b := (167960754941 / 100000000000000 : ℝ)) (q := (461759499467 / 20000000000000 : ℝ))
      (E := (cell12269 ⟨53, by decide⟩).energy) (xi := (173059245845363 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12269 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12269]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12269])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12269) (a := (5140961324941 / 6250000000000 : ℝ)) (b := (167960754941 / 100000000000000 : ℝ)) (q := (461759499467 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12269])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12269])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12269]

theorem cert12269_54 : CellCertificate 12269 (899137510094999 / 10000000000000000 : ℝ) (1712011680521373 / 1000000000000000000 : ℝ) (173059245845363 / 5000000000000000 : ℝ)
    (cell12269 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · have h := gap_lower (n := 12269) (a := (41110775001669 / 50000000000000 : ℝ)) (b := (167960754941 / 100000000000000 : ℝ)) (q := (577200384739 / 25000000000000 : ℝ))
      (E := (cell12269 ⟨54, by decide⟩).energy) (xi := (173059245845363 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12269 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12269]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12269])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12269) (a := (41110775001669 / 50000000000000 : ℝ)) (b := (167960754941 / 100000000000000 : ℝ)) (q := (577200384739 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12269])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12269])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12269]

theorem cert12269_55 : CellCertificate 12269 (899137510094999 / 10000000000000000 : ℝ) (1712011680521373 / 1000000000000000000 : ℝ) (173059245845363 / 5000000000000000 : ℝ)
    (cell12269 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · have h := gap_lower (n := 12269) (a := (41093871113373 / 50000000000000 : ℝ)) (b := (167960754941 / 100000000000000 : ℝ)) (q := (288600687171 / 12500000000000 : ℝ))
      (E := (cell12269 ⟨55, by decide⟩).energy) (xi := (173059245845363 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12269 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12269]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12269])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12269) (a := (41093871113373 / 50000000000000 : ℝ)) (b := (167960754941 / 100000000000000 : ℝ)) (q := (288600687171 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12269])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12269])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12269]

theorem cert12269_56 : CellCertificate 12269 (899137510094999 / 10000000000000000 : ℝ) (1712011680521373 / 1000000000000000000 : ℝ) (173059245845363 / 5000000000000000 : ℝ)
    (cell12269 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · have h := gap_lower (n := 12269) (a := (82153957841161 / 100000000000000 : ℝ)) (b := (167960754941 / 100000000000000 : ℝ)) (q := (577202371933 / 25000000000000 : ℝ))
      (E := (cell12269 ⟨56, by decide⟩).energy) (xi := (173059245845363 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12269 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12269]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12269])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12269) (a := (82153957841161 / 100000000000000 : ℝ)) (b := (167960754941 / 100000000000000 : ℝ)) (q := (577202371933 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12269])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12269])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12269]

theorem cert12269_57 : CellCertificate 12269 (899137510094999 / 10000000000000000 : ℝ) (1712011680521373 / 1000000000000000000 : ℝ) (173059245845363 / 5000000000000000 : ℝ)
    (cell12269 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · have h := gap_lower (n := 12269) (a := (82120196818601 / 100000000000000 : ℝ)) (b := (167960754941 / 100000000000000 : ℝ)) (q := (2308813506987 / 100000000000000 : ℝ))
      (E := (cell12269 ⟨57, by decide⟩).energy) (xi := (173059245845363 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12269 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12269]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12269])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12269) (a := (82120196818601 / 100000000000000 : ℝ)) (b := (167960754941 / 100000000000000 : ℝ)) (q := (2308813506987 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12269])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12269])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12269]

theorem cert12269_58 : CellCertificate 12269 (899137510094999 / 10000000000000000 : ℝ) (1712011680521373 / 1000000000000000000 : ℝ) (173059245845363 / 5000000000000000 : ℝ)
    (cell12269 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · have h := gap_lower (n := 12269) (a := (41043229565613 / 50000000000000 : ℝ)) (b := (167960754941 / 100000000000000 : ℝ)) (q := (2308817492731 / 100000000000000 : ℝ))
      (E := (cell12269 ⟨58, by decide⟩).energy) (xi := (173059245845363 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12269 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12269]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12269])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12269) (a := (41043229565613 / 50000000000000 : ℝ)) (b := (167960754941 / 100000000000000 : ℝ)) (q := (2308817492731 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12269])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12269])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12269]

theorem cert12269_59 : CellCertificate 12269 (899137510094999 / 10000000000000000 : ℝ) (1712011680521373 / 1000000000000000000 : ℝ) (173059245845363 / 5000000000000000 : ℝ)
    (cell12269 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · have h := gap_lower (n := 12269) (a := (16410548950267 / 20000000000000 : ℝ)) (b := (167960754941 / 100000000000000 : ℝ)) (q := (2308821500563 / 100000000000000 : ℝ))
      (E := (cell12269 ⟨59, by decide⟩).energy) (xi := (173059245845363 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12269 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12269]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12269])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12269) (a := (16410548950267 / 20000000000000 : ℝ)) (b := (167960754941 / 100000000000000 : ℝ)) (q := (2308821500563 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12269])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12269])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12269]

theorem cert12270_40 : CellCertificate 12270 (22477691431923 / 250000000000000 : ℝ) (342374420956821 / 200000000000000000 : ℝ) (86522382635203 / 2500000000000000 : ℝ)
    (cell12270 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · have h := gap_lower (n := 12270) (a := (82697327869303 / 100000000000000 : ℝ)) (b := (167946883593 / 100000000000000 : ℝ)) (q := (2308599974041 / 100000000000000 : ℝ))
      (E := (cell12270 ⟨40, by decide⟩).energy) (xi := (86522382635203 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12270 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12270]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12270])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12270) (a := (82697327869303 / 100000000000000 : ℝ)) (b := (167946883593 / 100000000000000 : ℝ)) (q := (2308599974041 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12270])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12270])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12270]

theorem cert12270_41 : CellCertificate 12270 (22477691431923 / 250000000000000 : ℝ) (342374420956821 / 200000000000000000 : ℝ) (86522382635203 / 2500000000000000 : ℝ)
    (cell12270 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · have h := gap_lower (n := 12270) (a := (82663189919479 / 100000000000000 : ℝ)) (b := (167946883593 / 100000000000000 : ℝ)) (q := (1154301976467 / 50000000000000 : ℝ))
      (E := (cell12270 ⟨41, by decide⟩).energy) (xi := (86522382635203 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12270 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12270]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12270])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12270) (a := (82663189919479 / 100000000000000 : ℝ)) (b := (167946883593 / 100000000000000 : ℝ)) (q := (1154301976467 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12270])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12270])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12270]

theorem cert12270_42 : CellCertificate 12270 (22477691431923 / 250000000000000 : ℝ) (342374420956821 / 200000000000000000 : ℝ) (86522382635203 / 2500000000000000 : ℝ)
    (cell12270 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · have h := gap_lower (n := 12270) (a := (82629075767111 / 100000000000000 : ℝ)) (b := (167946883593 / 100000000000000 : ℝ)) (q := (2308607926831 / 100000000000000 : ℝ))
      (E := (cell12270 ⟨42, by decide⟩).energy) (xi := (86522382635203 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12270 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12270]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12270])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12270) (a := (82629075767111 / 100000000000000 : ℝ)) (b := (167946883593 / 100000000000000 : ℝ)) (q := (2308607926831 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12270])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12270])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12270]

theorem cert12270_43 : CellCertificate 12270 (22477691431923 / 250000000000000 : ℝ) (342374420956821 / 200000000000000000 : ℝ) (86522382635203 / 2500000000000000 : ℝ)
    (cell12270 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · have h := gap_lower (n := 12270) (a := (41297492691087 / 50000000000000 : ℝ)) (b := (167946883593 / 100000000000000 : ℝ)) (q := (2308611954377 / 100000000000000 : ℝ))
      (E := (cell12270 ⟨43, by decide⟩).energy) (xi := (86522382635203 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12270 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12270]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12270])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12270) (a := (41297492691087 / 50000000000000 : ℝ)) (b := (167946883593 / 100000000000000 : ℝ)) (q := (2308611954377 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12270])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12270])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12270]

theorem cert12270_44 : CellCertificate 12270 (22477691431923 / 250000000000000 : ℝ) (342374420956821 / 200000000000000000 : ℝ) (86522382635203 / 2500000000000000 : ℝ)
    (cell12270 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · have h := gap_lower (n := 12270) (a := (82560918734791 / 100000000000000 : ℝ)) (b := (167946883593 / 100000000000000 : ℝ)) (q := (2308615917701 / 100000000000000 : ℝ))
      (E := (cell12270 ⟨44, by decide⟩).energy) (xi := (86522382635203 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12270 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12270]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12270])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12270) (a := (82560918734791 / 100000000000000 : ℝ)) (b := (167946883593 / 100000000000000 : ℝ)) (q := (2308615917701 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12270])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12270])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12270]

theorem cert12270_45 : CellCertificate 12270 (22477691431923 / 250000000000000 : ℝ) (342374420956821 / 200000000000000000 : ℝ) (86522382635203 / 2500000000000000 : ℝ)
    (cell12270 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · have h := gap_lower (n := 12270) (a := (82526875795237 / 100000000000000 : ℝ)) (b := (167946883593 / 100000000000000 : ℝ)) (q := (2308619933807 / 100000000000000 : ℝ))
      (E := (cell12270 ⟨45, by decide⟩).energy) (xi := (86522382635203 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12270 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12270]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12270])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12270) (a := (82526875795237 / 100000000000000 : ℝ)) (b := (167946883593 / 100000000000000 : ℝ)) (q := (2308619933807 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12270])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12270])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12270]

theorem cert12270_46 : CellCertificate 12270 (22477691431923 / 250000000000000 : ℝ) (342374420956821 / 200000000000000000 : ℝ) (86522382635203 / 2500000000000000 : ℝ)
    (cell12270 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · have h := gap_lower (n := 12270) (a := (41246428266969 / 50000000000000 : ℝ)) (b := (167946883593 / 100000000000000 : ℝ)) (q := (2308623943137 / 100000000000000 : ℝ))
      (E := (cell12270 ⟨46, by decide⟩).energy) (xi := (86522382635203 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12270 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12270]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12270])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12270) (a := (41246428266969 / 50000000000000 : ℝ)) (b := (167946883593 / 100000000000000 : ℝ)) (q := (2308623943137 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12270])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12270])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12270]

theorem cert12270_47 : CellCertificate 12270 (22477691431923 / 250000000000000 : ℝ) (342374420956821 / 200000000000000000 : ℝ) (86522382635203 / 2500000000000000 : ℝ)
    (cell12270 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · have h := gap_lower (n := 12270) (a := (82458860921467 / 100000000000000 : ℝ)) (b := (167946883593 / 100000000000000 : ℝ)) (q := (230862794469 / 10000000000000 : ℝ))
      (E := (cell12270 ⟨47, by decide⟩).energy) (xi := (86522382635203 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12270 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12270]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12270])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12270) (a := (82458860921467 / 100000000000000 : ℝ)) (b := (167946883593 / 100000000000000 : ℝ)) (q := (230862794469 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12270])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12270])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12270]

theorem cert12270_48 : CellCertificate 12270 (22477691431923 / 250000000000000 : ℝ) (342374420956821 / 200000000000000000 : ℝ) (86522382635203 / 2500000000000000 : ℝ)
    (cell12270 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · have h := gap_lower (n := 12270) (a := (82424888928549 / 100000000000000 : ℝ)) (b := (167946883593 / 100000000000000 : ℝ)) (q := (2308631937243 / 100000000000000 : ℝ))
      (E := (cell12270 ⟨48, by decide⟩).energy) (xi := (86522382635203 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12270 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12270]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12270])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12270) (a := (82424888928549 / 100000000000000 : ℝ)) (b := (167946883593 / 100000000000000 : ℝ)) (q := (2308631937243 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12270])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12270])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12270]

theorem cert12270_49 : CellCertificate 12270 (22477691431923 / 250000000000000 : ℝ) (342374420956821 / 200000000000000000 : ℝ) (86522382635203 / 2500000000000000 : ℝ)
    (cell12270 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · have h := gap_lower (n := 12270) (a := (82390940526053 / 100000000000000 : ℝ)) (b := (167946883593 / 100000000000000 : ℝ)) (q := (2308635919363 / 100000000000000 : ℝ))
      (E := (cell12270 ⟨49, by decide⟩).energy) (xi := (86522382635203 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12270 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12270]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12270])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12270) (a := (82390940526053 / 100000000000000 : ℝ)) (b := (167946883593 / 100000000000000 : ℝ)) (q := (2308635919363 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12270])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12270])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12270]

theorem cert12270_50 : CellCertificate 12270 (22477691431923 / 250000000000000 : ℝ) (342374420956821 / 200000000000000000 : ℝ) (86522382635203 / 2500000000000000 : ℝ)
    (cell12270 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · have h := gap_lower (n := 12270) (a := (82357015684997 / 100000000000000 : ℝ)) (b := (167946883593 / 100000000000000 : ℝ)) (q := (2308639948337 / 100000000000000 : ℝ))
      (E := (cell12270 ⟨50, by decide⟩).energy) (xi := (86522382635203 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12270 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12270]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12270])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12270) (a := (82357015684997 / 100000000000000 : ℝ)) (b := (167946883593 / 100000000000000 : ℝ)) (q := (2308639948337 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12270])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12270])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12270]

theorem cert12270_51 : CellCertificate 12270 (22477691431923 / 250000000000000 : ℝ) (342374420956821 / 200000000000000000 : ℝ) (86522382635203 / 2500000000000000 : ℝ)
    (cell12270 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · have h := gap_lower (n := 12270) (a := (2572597324267 / 3125000000000 : ℝ)) (b := (167946883593 / 100000000000000 : ℝ)) (q := (577160976111 / 25000000000000 : ℝ))
      (E := (cell12270 ⟨51, by decide⟩).energy) (xi := (86522382635203 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12270 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12270]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12270])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12270) (a := (2572597324267 / 3125000000000 : ℝ)) (b := (167946883593 / 100000000000000 : ℝ)) (q := (577160976111 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12270])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12270])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12270]

theorem cert12270_52 : CellCertificate 12270 (22477691431923 / 250000000000000 : ℝ) (342374420956821 / 200000000000000000 : ℝ) (86522382635203 / 2500000000000000 : ℝ)
    (cell12270 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · have h := gap_lower (n := 12270) (a := (82289236572001 / 100000000000000 : ℝ)) (b := (167946883593 / 100000000000000 : ℝ)) (q := (2308647903509 / 100000000000000 : ℝ))
      (E := (cell12270 ⟨52, by decide⟩).energy) (xi := (86522382635203 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12270 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12270]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12270])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12270) (a := (82289236572001 / 100000000000000 : ℝ)) (b := (167946883593 / 100000000000000 : ℝ)) (q := (2308647903509 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12270])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12270])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12270]

theorem cert12270_53 : CellCertificate 12270 (22477691431923 / 250000000000000 : ℝ) (342374420956821 / 200000000000000000 : ℝ) (86522382635203 / 2500000000000000 : ℝ)
    (cell12270 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · have h := gap_lower (n := 12270) (a := (4112769112141 / 5000000000000 : ℝ)) (b := (167946883593 / 100000000000000 : ℝ)) (q := (2308651884301 / 100000000000000 : ℝ))
      (E := (cell12270 ⟨53, by decide⟩).energy) (xi := (86522382635203 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12270 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12270]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12270])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12270) (a := (4112769112141 / 5000000000000 : ℝ)) (b := (167946883593 / 100000000000000 : ℝ)) (q := (2308651884301 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12270])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12270])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12270]

theorem cert12270_54 : CellCertificate 12270 (22477691431923 / 250000000000000 : ℝ) (342374420956821 / 200000000000000000 : ℝ) (86522382635203 / 2500000000000000 : ℝ)
    (cell12270 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · have h := gap_lower (n := 12270) (a := (82221551360597 / 100000000000000 : ℝ)) (b := (167946883593 / 100000000000000 : ℝ)) (q := (2308655903347 / 100000000000000 : ℝ))
      (E := (cell12270 ⟨54, by decide⟩).energy) (xi := (86522382635203 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12270 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12270]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12270])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12270) (a := (82221551360597 / 100000000000000 : ℝ)) (b := (167946883593 / 100000000000000 : ℝ)) (q := (2308655903347 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12270])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12270])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12270]

theorem cert12270_55 : CellCertificate 12270 (22477691431923 / 250000000000000 : ℝ) (342374420956821 / 200000000000000000 : ℝ) (86522382635203 / 2500000000000000 : ℝ)
    (cell12270 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · have h := gap_lower (n := 12270) (a := (8218774389707 / 10000000000000 : ℝ)) (b := (167946883593 / 100000000000000 : ℝ)) (q := (2308659898947 / 100000000000000 : ℝ))
      (E := (cell12270 ⟨55, by decide⟩).energy) (xi := (86522382635203 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12270 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12270]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12270])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12270) (a := (8218774389707 / 10000000000000 : ℝ)) (b := (167946883593 / 100000000000000 : ℝ)) (q := (2308659898947 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12270])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12270])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12270]

theorem cert12270_56 : CellCertificate 12270 (22477691431923 / 250000000000000 : ℝ) (342374420956821 / 200000000000000000 : ℝ) (86522382635203 / 2500000000000000 : ℝ)
    (cell12270 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · have h := gap_lower (n := 12270) (a := (82153959824117 / 100000000000000 : ℝ)) (b := (167946883593 / 100000000000000 : ℝ)) (q := (288582990907 / 12500000000000 : ℝ))
      (E := (cell12270 ⟨56, by decide⟩).energy) (xi := (86522382635203 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12270 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12270]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12270])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12270) (a := (82153959824117 / 100000000000000 : ℝ)) (b := (167946883593 / 100000000000000 : ℝ)) (q := (288582990907 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12270])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12270])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12270]

theorem cert12270_57 : CellCertificate 12270 (22477691431923 / 250000000000000 : ℝ) (342374420956821 / 200000000000000000 : ℝ) (86522382635203 / 2500000000000000 : ℝ)
    (cell12270 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · have h := gap_lower (n := 12270) (a := (513251244461 / 625000000000 : ℝ)) (b := (167946883593 / 100000000000000 : ℝ)) (q := (2308667926103 / 100000000000000 : ℝ))
      (E := (cell12270 ⟨57, by decide⟩).energy) (xi := (86522382635203 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12270 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12270]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12270])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12270) (a := (513251244461 / 625000000000 : ℝ)) (b := (167946883593 / 100000000000000 : ℝ)) (q := (2308667926103 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12270])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12270])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12270]

theorem cert12270_58 : CellCertificate 12270 (22477691431923 / 250000000000000 : ℝ) (342374420956821 / 200000000000000000 : ℝ) (86522382635203 / 2500000000000000 : ℝ)
    (cell12270 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · have h := gap_lower (n := 12270) (a := (82086461738157 / 100000000000000 : ℝ)) (b := (167946883593 / 100000000000000 : ℝ)) (q := (577167973037 / 25000000000000 : ℝ))
      (E := (cell12270 ⟨58, by decide⟩).energy) (xi := (86522382635203 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12270 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12270]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12270])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12270) (a := (82086461738157 / 100000000000000 : ℝ)) (b := (167946883593 / 100000000000000 : ℝ)) (q := (577167973037 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12270])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12270])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12270]

theorem cert12270_59 : CellCertificate 12270 (22477691431923 / 250000000000000 : ℝ) (342374420956821 / 200000000000000000 : ℝ) (86522382635203 / 2500000000000000 : ℝ)
    (cell12270 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · have h := gap_lower (n := 12270) (a := (82052747669609 / 100000000000000 : ℝ)) (b := (167946883593 / 100000000000000 : ℝ)) (q := (288584485123 / 12500000000000 : ℝ))
      (E := (cell12270 ⟨59, by decide⟩).energy) (xi := (86522382635203 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12270 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12270]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12270])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12270) (a := (82052747669609 / 100000000000000 : ℝ)) (b := (167946883593 / 100000000000000 : ℝ)) (q := (288584485123 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12270])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12270])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12270]

theorem cert12271_40 : CellCertificate 12271 (899077809146649 / 10000000000000000 : ℝ) (427933137950863 / 250000000000000000 : ℝ) (173030287179421 / 5000000000000000 : ℝ)
    (cell12271 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · have h := gap_lower (n := 12271) (a := (82697324798959 / 100000000000000 : ℝ)) (b := (33586602913 / 20000000000000 : ℝ)) (q := (1154227211059 / 50000000000000 : ℝ))
      (E := (cell12271 ⟨40, by decide⟩).energy) (xi := (173030287179421 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12271 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12271]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12271])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12271) (a := (82697324798959 / 100000000000000 : ℝ)) (b := (33586602913 / 20000000000000 : ℝ)) (q := (1154227211059 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12271])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12271])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12271]

theorem cert12271_41 : CellCertificate 12271 (899077809146649 / 10000000000000000 : ℝ) (427933137950863 / 250000000000000000 : ℝ) (173030287179421 / 5000000000000000 : ℝ)
    (cell12271 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · have h := gap_lower (n := 12271) (a := (3306527486731 / 4000000000000 : ℝ)) (b := (33586602913 / 20000000000000 : ℝ)) (q := (461691685563 / 20000000000000 : ℝ))
      (E := (cell12271 ⟨41, by decide⟩).energy) (xi := (173030287179421 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12271 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12271]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12271])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12271) (a := (3306527486731 / 4000000000000 : ℝ)) (b := (33586602913 / 20000000000000 : ℝ)) (q := (461691685563 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12271])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12271])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12271]

theorem cert12271_42 : CellCertificate 12271 (899077809146649 / 10000000000000000 : ℝ) (427933137950863 / 250000000000000000 : ℝ) (173030287179421 / 5000000000000000 : ℝ)
    (cell12271 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · have h := gap_lower (n := 12271) (a := (82629073334607 / 100000000000000 : ℝ)) (b := (33586602913 / 20000000000000 : ℝ)) (q := (2308462429279 / 100000000000000 : ℝ))
      (E := (cell12271 ⟨42, by decide⟩).energy) (xi := (173030287179421 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12271 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12271]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12271])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12271) (a := (82629073334607 / 100000000000000 : ℝ)) (b := (33586602913 / 20000000000000 : ℝ)) (q := (2308462429279 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12271])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12271])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12271]

theorem cert12271_43 : CellCertificate 12271 (899077809146649 / 10000000000000000 : ℝ) (427933137950863 / 250000000000000000 : ℝ) (173030287179421 / 5000000000000000 : ℝ)
    (cell12271 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · have h := gap_lower (n := 12271) (a := (10324372908491 / 12500000000000 : ℝ)) (b := (33586602913 / 20000000000000 : ℝ)) (q := (1154233213191 / 50000000000000 : ℝ))
      (E := (cell12271 ⟨43, by decide⟩).energy) (xi := (173030287179421 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12271 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12271]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12271])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12271) (a := (10324372908491 / 12500000000000 : ℝ)) (b := (33586602913 / 20000000000000 : ℝ)) (q := (1154233213191 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12271])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12271])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12271]

theorem cert12271_44 : CellCertificate 12271 (899077809146649 / 10000000000000000 : ℝ) (427933137950863 / 250000000000000000 : ℝ) (173030287179421 / 5000000000000000 : ℝ)
    (cell12271 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · have h := gap_lower (n := 12271) (a := (41280458469181 / 50000000000000 : ℝ)) (b := (33586602913 / 20000000000000 : ℝ)) (q := (1154235209389 / 50000000000000 : ℝ))
      (E := (cell12271 ⟨44, by decide⟩).energy) (xi := (173030287179421 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12271 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12271]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12271])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12271) (a := (41280458469181 / 50000000000000 : ℝ)) (b := (33586602913 / 20000000000000 : ℝ)) (q := (1154235209389 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12271])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12271])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12271]

theorem cert12271_45 : CellCertificate 12271 (899077809146649 / 10000000000000000 : ℝ) (427933137950863 / 250000000000000000 : ℝ) (173030287179421 / 5000000000000000 : ℝ)
    (cell12271 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · have h := gap_lower (n := 12271) (a := (41263437158093 / 50000000000000 : ℝ)) (b := (33586602913 / 20000000000000 : ℝ)) (q := (2308474405897 / 100000000000000 : ℝ))
      (E := (cell12271 ⟨45, by decide⟩).energy) (xi := (173030287179421 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12271 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12271]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12271])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12271) (a := (41263437158093 / 50000000000000 : ℝ)) (b := (33586602913 / 20000000000000 : ℝ)) (q := (2308474405897 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12271])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12271])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12271]

theorem cert12271_46 : CellCertificate 12271 (899077809146649 / 10000000000000000 : ℝ) (427933137950863 / 250000000000000000 : ℝ) (173030287179421 / 5000000000000000 : ℝ)
    (cell12271 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · have h := gap_lower (n := 12271) (a := (41246427685913 / 50000000000000 : ℝ)) (b := (33586602913 / 20000000000000 : ℝ)) (q := (1154239193477 / 50000000000000 : ℝ))
      (E := (cell12271 ⟨46, by decide⟩).energy) (xi := (173030287179421 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12271 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12271]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12271])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12271) (a := (41246427685913 / 50000000000000 : ℝ)) (b := (33586602913 / 20000000000000 : ℝ)) (q := (1154239193477 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12271])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12271])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12271]

theorem cert12271_47 : CellCertificate 12271 (899077809146649 / 10000000000000000 : ℝ) (427933137950863 / 250000000000000000 : ℝ) (173030287179421 / 5000000000000000 : ℝ)
    (cell12271 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · have h := gap_lower (n := 12271) (a := (82458860075857 / 100000000000000 : ℝ)) (b := (33586602913 / 20000000000000 : ℝ)) (q := (461696483963 / 20000000000000 : ℝ))
      (E := (cell12271 ⟨47, by decide⟩).energy) (xi := (173030287179421 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12271 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12271]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12271])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12271) (a := (82458860075857 / 100000000000000 : ℝ)) (b := (33586602913 / 20000000000000 : ℝ)) (q := (461696483963 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12271])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12271])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12271]

theorem cert12271_48 : CellCertificate 12271 (899077809146649 / 10000000000000000 : ℝ) (427933137950863 / 250000000000000000 : ℝ) (173030287179421 / 5000000000000000 : ℝ)
    (cell12271 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · have h := gap_lower (n := 12271) (a := (41212444199501 / 50000000000000 : ℝ)) (b := (33586602913 / 20000000000000 : ℝ)) (q := (2308486385547 / 100000000000000 : ℝ))
      (E := (cell12271 ⟨48, by decide⟩).energy) (xi := (173030287179421 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12271 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12271]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12271])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12271) (a := (41212444199501 / 50000000000000 : ℝ)) (b := (33586602913 / 20000000000000 : ℝ)) (q := (2308486385547 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12271])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12271])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12271]

theorem cert12271_49 : CellCertificate 12271 (899077809146649 / 10000000000000000 : ℝ) (427933137950863 / 250000000000000000 : ℝ) (173030287179421 / 5000000000000000 : ℝ)
    (cell12271 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · have h := gap_lower (n := 12271) (a := (41195470156067 / 50000000000000 : ℝ)) (b := (33586602913 / 20000000000000 : ℝ)) (q := (288561300059 / 12500000000000 : ℝ))
      (E := (cell12271 ⟨49, by decide⟩).energy) (xi := (173030287179421 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12271 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12271]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12271])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12271) (a := (41195470156067 / 50000000000000 : ℝ)) (b := (33586602913 / 20000000000000 : ℝ)) (q := (288561300059 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12271])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12271])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12271]

theorem cert12271_50 : CellCertificate 12271 (899077809146649 / 10000000000000000 : ℝ) (427933137950863 / 250000000000000000 : ℝ) (173030287179421 / 5000000000000000 : ℝ)
    (cell12271 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · have h := gap_lower (n := 12271) (a := (8235701578627 / 10000000000000 : ℝ)) (b := (33586602913 / 20000000000000 : ℝ)) (q := (230849440407 / 10000000000000 : ℝ))
      (E := (cell12271 ⟨50, by decide⟩).energy) (xi := (173030287179421 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12271 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12271]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12271])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12271) (a := (8235701578627 / 10000000000000 : ℝ)) (b := (33586602913 / 20000000000000 : ℝ)) (q := (230849440407 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12271])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12271])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12271]

theorem cert12271_51 : CellCertificate 12271 (899077809146649 / 10000000000000000 : ℝ) (427933137950863 / 250000000000000000 : ℝ) (173030287179421 / 5000000000000000 : ℝ)
    (cell12271 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · have h := gap_lower (n := 12271) (a := (82323114792573 / 100000000000000 : ℝ)) (b := (33586602913 / 20000000000000 : ℝ)) (q := (2308498394477 / 100000000000000 : ℝ))
      (E := (cell12271 ⟨51, by decide⟩).energy) (xi := (173030287179421 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12271 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12271]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12271])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12271) (a := (82323114792573 / 100000000000000 : ℝ)) (b := (33586602913 / 20000000000000 : ℝ)) (q := (2308498394477 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12271])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12271])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12271]

theorem cert12271_52 : CellCertificate 12271 (899077809146649 / 10000000000000000 : ℝ) (427933137950863 / 250000000000000000 : ℝ) (173030287179421 / 5000000000000000 : ℝ)
    (cell12271 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · have h := gap_lower (n := 12271) (a := (82289237302353 / 100000000000000 : ℝ)) (b := (33586602913 / 20000000000000 : ℝ)) (q := (577125592403 / 25000000000000 : ℝ))
      (E := (cell12271 ⟨52, by decide⟩).energy) (xi := (173030287179421 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12271 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12271]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12271])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12271) (a := (82289237302353 / 100000000000000 : ℝ)) (b := (33586602913 / 20000000000000 : ℝ)) (q := (577125592403 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12271])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12271])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12271]

theorem cert12271_53 : CellCertificate 12271 (899077809146649 / 10000000000000000 : ℝ) (427933137950863 / 250000000000000000 : ℝ) (173030287179421 / 5000000000000000 : ℝ)
    (cell12271 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · have h := gap_lower (n := 12271) (a := (82255383287061 / 100000000000000 : ℝ)) (b := (33586602913 / 20000000000000 : ℝ)) (q := (2308506386193 / 100000000000000 : ℝ))
      (E := (cell12271 ⟨53, by decide⟩).energy) (xi := (173030287179421 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12271 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12271]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12271])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12271) (a := (82255383287061 / 100000000000000 : ℝ)) (b := (33586602913 / 20000000000000 : ℝ)) (q := (2308506386193 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12271])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12271])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12271]

theorem cert12271_54 : CellCertificate 12271 (899077809146649 / 10000000000000000 : ℝ) (427933137950863 / 250000000000000000 : ℝ) (173030287179421 / 5000000000000000 : ℝ)
    (cell12271 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · have h := gap_lower (n := 12271) (a := (16444310543659 / 20000000000000 : ℝ)) (b := (33586602913 / 20000000000000 : ℝ)) (q := (9234041531 / 400000000000 : ℝ))
      (E := (cell12271 ⟨54, by decide⟩).energy) (xi := (173030287179421 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12271 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12271]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12271])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12271) (a := (16444310543659 / 20000000000000 : ℝ)) (b := (33586602913 / 20000000000000 : ℝ)) (q := (9234041531 / 400000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12271])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12271])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12271]

theorem cert12271_55 : CellCertificate 12271 (899077809146649 / 10000000000000000 : ℝ) (427933137950863 / 250000000000000000 : ℝ) (173030287179421 / 5000000000000000 : ℝ)
    (cell12271 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · have h := gap_lower (n := 12271) (a := (5136734097987 / 6250000000000 : ℝ)) (b := (33586602913 / 20000000000000 : ℝ)) (q := (230851435657 / 10000000000000 : ℝ))
      (E := (cell12271 ⟨55, by decide⟩).energy) (xi := (173030287179421 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12271 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12271]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12271])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12271) (a := (5136734097987 / 6250000000000 : ℝ)) (b := (33586602913 / 20000000000000 : ℝ)) (q := (230851435657 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12271])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12271])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12271]

theorem cert12271_56 : CellCertificate 12271 (899077809146649 / 10000000000000000 : ℝ) (427933137950863 / 250000000000000000 : ℝ) (173030287179421 / 5000000000000000 : ℝ)
    (cell12271 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · have h := gap_lower (n := 12271) (a := (82153961807433 / 100000000000000 : ℝ)) (b := (33586602913 / 20000000000000 : ℝ)) (q := (1154259181903 / 50000000000000 : ℝ))
      (E := (cell12271 ⟨56, by decide⟩).energy) (xi := (173030287179421 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12271 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12271]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12271])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12271) (a := (82153961807433 / 100000000000000 : ℝ)) (b := (33586602913 / 20000000000000 : ℝ)) (q := (1154259181903 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12271])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12271])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12271]

theorem cert12271_57 : CellCertificate 12271 (899077809146649 / 10000000000000000 : ℝ) (427933137950863 / 250000000000000000 : ℝ) (173030287179421 / 5000000000000000 : ℝ)
    (cell12271 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · have h := gap_lower (n := 12271) (a := (41060100704619 / 50000000000000 : ℝ)) (b := (33586602913 / 20000000000000 : ℝ)) (q := (2308522401393 / 100000000000000 : ℝ))
      (E := (cell12271 ⟨57, by decide⟩).energy) (xi := (173030287179421 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12271 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12271]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12271])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12271) (a := (41060100704619 / 50000000000000 : ℝ)) (b := (33586602913 / 20000000000000 : ℝ)) (q := (2308522401393 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12271])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12271])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12271]

theorem cert12271_58 : CellCertificate 12271 (899077809146649 / 10000000000000000 : ℝ) (427933137950863 / 250000000000000000 : ℝ) (173030287179421 / 5000000000000000 : ℝ)
    (cell12271 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · have h := gap_lower (n := 12271) (a := (82086464345369 / 100000000000000 : ℝ)) (b := (33586602913 / 20000000000000 : ℝ)) (q := (2308526347799 / 100000000000000 : ℝ))
      (E := (cell12271 ⟨58, by decide⟩).energy) (xi := (173030287179421 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12271 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12271]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12271])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12271) (a := (82086464345369 / 100000000000000 : ℝ)) (b := (33586602913 / 20000000000000 : ℝ)) (q := (2308526347799 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12271])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12271])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12271]

theorem cert12271_59 : CellCertificate 12271 (899077809146649 / 10000000000000000 : ℝ) (427933137950863 / 250000000000000000 : ℝ) (173030287179421 / 5000000000000000 : ℝ)
    (cell12271 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · have h := gap_lower (n := 12271) (a := (131284400941 / 160000000000 : ℝ)) (b := (33586602913 / 20000000000000 : ℝ)) (q := (288566297107 / 12500000000000 : ℝ))
      (E := (cell12271 ⟨59, by decide⟩).energy) (xi := (173030287179421 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12271 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12271]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12271])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12271) (a := (131284400941 / 160000000000 : ℝ)) (b := (33586602913 / 20000000000000 : ℝ)) (q := (288566297107 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12271])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12271])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12271]

theorem cert12272_40 : CellCertificate 12272 (899047965703029 / 10000000000000000 : ℝ) (34231860431477 / 20000000000000000 : ℝ) (346031623143367 / 10000000000000000 : ℝ)
    (cell12272 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · have h := gap_lower (n := 12272) (a := (10337165216201 / 12500000000000 : ℝ)) (b := (83959573929 / 50000000000000 : ℝ)) (q := (1154154491989 / 50000000000000 : ℝ))
      (E := (cell12272 ⟨40, by decide⟩).energy) (xi := (346031623143367 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12272 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12272]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12272])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12272) (a := (10337165216201 / 12500000000000 : ℝ)) (b := (83959573929 / 50000000000000 : ℝ)) (q := (1154154491989 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12272])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12272])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12272]

theorem cert12272_41 : CellCertificate 12272 (899047965703029 / 10000000000000000 : ℝ) (34231860431477 / 20000000000000000 : ℝ) (346031623143367 / 10000000000000000 : ℝ)
    (cell12272 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · have h := gap_lower (n := 12272) (a := (3306527376721 / 4000000000000 : ℝ)) (b := (83959573929 / 50000000000000 : ℝ)) (q := (2308313016567 / 100000000000000 : ℝ))
      (E := (cell12272 ⟨41, by decide⟩).energy) (xi := (346031623143367 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12272 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12272]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12272])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12272) (a := (3306527376721 / 4000000000000 : ℝ)) (b := (83959573929 / 50000000000000 : ℝ)) (q := (2308313016567 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12272])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12272])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12272]

theorem cert12272_42 : CellCertificate 12272 (899047965703029 / 10000000000000000 : ℝ) (34231860431477 / 20000000000000000 : ℝ) (346031623143367 / 10000000000000000 : ℝ)
    (cell12272 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · have h := gap_lower (n := 12272) (a := (10328633862877 / 12500000000000 : ℝ)) (b := (83959573929 / 50000000000000 : ℝ)) (q := (288539623367 / 12500000000000 : ℝ))
      (E := (cell12272 ⟨42, by decide⟩).energy) (xi := (346031623143367 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12272 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12272]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12272])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12272) (a := (10328633862877 / 12500000000000 : ℝ)) (b := (83959573929 / 50000000000000 : ℝ)) (q := (288539623367 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12272])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12272])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12272]

theorem cert12272_43 : CellCertificate 12272 (899047965703029 / 10000000000000000 : ℝ) (34231860431477 / 20000000000000000 : ℝ) (346031623143367 / 10000000000000000 : ℝ)
    (cell12272 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · have h := gap_lower (n := 12272) (a := (16518996230911 / 20000000000000 : ℝ)) (b := (83959573929 / 50000000000000 : ℝ)) (q := (461664202487 / 20000000000000 : ℝ))
      (E := (cell12272 ⟨43, by decide⟩).energy) (xi := (346031623143367 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12272 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12272]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12272])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12272) (a := (16518996230911 / 20000000000000 : ℝ)) (b := (83959573929 / 50000000000000 : ℝ)) (q := (461664202487 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12272])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12272])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12272]

theorem cert12272_44 : CellCertificate 12272 (899047965703029 / 10000000000000000 : ℝ) (34231860431477 / 20000000000000000 : ℝ) (346031623143367 / 10000000000000000 : ℝ)
    (cell12272 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · have h := gap_lower (n := 12272) (a := (82560915142767 / 100000000000000 : ℝ)) (b := (83959573929 / 50000000000000 : ℝ)) (q := (288540621899 / 12500000000000 : ℝ))
      (E := (cell12272 ⟨44, by decide⟩).energy) (xi := (346031623143367 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12272 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12272]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12272])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12272) (a := (82560915142767 / 100000000000000 : ℝ)) (b := (83959573929 / 50000000000000 : ℝ)) (q := (288540621899 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12272])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12272])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12272]

theorem cert12272_45 : CellCertificate 12272 (899047965703029 / 10000000000000000 : ℝ) (34231860431477 / 20000000000000000 : ℝ) (346031623143367 / 10000000000000000 : ℝ)
    (cell12272 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · have h := gap_lower (n := 12272) (a := (82526872837929 / 100000000000000 : ℝ)) (b := (83959573929 / 50000000000000 : ℝ)) (q := (230832899221 / 10000000000000 : ℝ))
      (E := (cell12272 ⟨45, by decide⟩).energy) (xi := (346031623143367 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12272 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12272]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12272])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12272) (a := (82526872837929 / 100000000000000 : ℝ)) (b := (83959573929 / 50000000000000 : ℝ)) (q := (230832899221 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12272])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12272])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12272]

theorem cert12272_46 : CellCertificate 12272 (899047965703029 / 10000000000000000 : ℝ) (34231860431477 / 20000000000000000 : ℝ) (346031623143367 / 10000000000000000 : ℝ)
    (cell12272 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · have h := gap_lower (n := 12272) (a := (20623213552617 / 25000000000000 : ℝ)) (b := (83959573929 / 50000000000000 : ℝ)) (q := (1154166472541 / 50000000000000 : ℝ))
      (E := (cell12272 ⟨46, by decide⟩).energy) (xi := (346031623143367 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12272 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12272]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12272])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12272) (a := (20623213552617 / 25000000000000 : ℝ)) (b := (83959573929 / 50000000000000 : ℝ)) (q := (1154166472541 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12272])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12272])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12272]

theorem cert12272_47 : CellCertificate 12272 (899047965703029 / 10000000000000000 : ℝ) (34231860431477 / 20000000000000000 : ℝ) (346031623143367 / 10000000000000000 : ℝ)
    (cell12272 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · have h := gap_lower (n := 12272) (a := (1030735740387 / 1250000000000 : ℝ)) (b := (83959573929 / 50000000000000 : ℝ)) (q := (2308336950473 / 100000000000000 : ℝ))
      (E := (cell12272 ⟨47, by decide⟩).energy) (xi := (346031623143367 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12272 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12272]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12272])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12272) (a := (1030735740387 / 1250000000000 : ℝ)) (b := (83959573929 / 50000000000000 : ℝ)) (q := (2308336950473 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12272])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12272])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12272]

theorem cert12272_48 : CellCertificate 12272 (899047965703029 / 10000000000000000 : ℝ) (34231860431477 / 20000000000000000 : ℝ) (346031623143367 / 10000000000000000 : ℝ)
    (cell12272 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · have h := gap_lower (n := 12272) (a := (8242488787013 / 10000000000000 : ℝ)) (b := (83959573929 / 50000000000000 : ℝ)) (q := (1154170474169 / 50000000000000 : ℝ))
      (E := (cell12272 ⟨48, by decide⟩).energy) (xi := (346031623143367 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12272 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12272]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12272])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12272) (a := (8242488787013 / 10000000000000 : ℝ)) (b := (83959573929 / 50000000000000 : ℝ)) (q := (1154170474169 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12272])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12272])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12272]

theorem cert12272_49 : CellCertificate 12272 (899047965703029 / 10000000000000000 : ℝ) (34231860431477 / 20000000000000000 : ℝ) (346031623143367 / 10000000000000000 : ℝ)
    (cell12272 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · have h := gap_lower (n := 12272) (a := (82390940098849 / 100000000000000 : ℝ)) (b := (83959573929 / 50000000000000 : ℝ)) (q := (2308344937241 / 100000000000000 : ℝ))
      (E := (cell12272 ⟨49, by decide⟩).energy) (xi := (346031623143367 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12272 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12272]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12272])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12272) (a := (82390940098849 / 100000000000000 : ℝ)) (b := (83959573929 / 50000000000000 : ℝ)) (q := (2308344937241 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12272])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12272])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12272]

theorem cert12272_50 : CellCertificate 12272 (899047965703029 / 10000000000000000 : ℝ) (34231860431477 / 20000000000000000 : ℝ) (346031623143367 / 10000000000000000 : ℝ)
    (cell12272 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · have h := gap_lower (n := 12272) (a := (82357015888137 / 100000000000000 : ℝ)) (b := (83959573929 / 50000000000000 : ℝ)) (q := (577087243617 / 25000000000000 : ℝ))
      (E := (cell12272 ⟨50, by decide⟩).energy) (xi := (346031623143367 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12272 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12272]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12272])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12272) (a := (82357015888137 / 100000000000000 : ℝ)) (b := (83959573929 / 50000000000000 : ℝ)) (q := (577087243617 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12272])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12272])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12272]

theorem cert12272_51 : CellCertificate 12272 (899047965703029 / 10000000000000000 : ℝ) (34231860431477 / 20000000000000000 : ℝ) (346031623143367 / 10000000000000000 : ℝ)
    (cell12272 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · have h := gap_lower (n := 12272) (a := (41161557604579 / 50000000000000 : ℝ)) (b := (83959573929 / 50000000000000 : ℝ)) (q := (1154176470149 / 50000000000000 : ℝ))
      (E := (cell12272 ⟨51, by decide⟩).energy) (xi := (346031623143367 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12272 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12272]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12272])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12272) (a := (41161557604579 / 50000000000000 : ℝ)) (b := (83959573929 / 50000000000000 : ℝ)) (q := (1154176470149 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12272])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12272])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12272]

theorem cert12272_52 : CellCertificate 12272 (899047965703029 / 10000000000000000 : ℝ) (34231860431477 / 20000000000000000 : ℝ) (346031623143367 / 10000000000000000 : ℝ)
    (cell12272 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · have h := gap_lower (n := 12272) (a := (82289238033221 / 100000000000000 : ℝ)) (b := (83959573929 / 50000000000000 : ℝ)) (q := (2308356950553 / 100000000000000 : ℝ))
      (E := (cell12272 ⟨52, by decide⟩).energy) (xi := (346031623143367 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12272 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12272]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12272])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12272) (a := (82289238033221 / 100000000000000 : ℝ)) (b := (83959573929 / 50000000000000 : ℝ)) (q := (2308356950553 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12272])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12272])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12272]

theorem cert12272_53 : CellCertificate 12272 (899047965703029 / 10000000000000000 : ℝ) (34231860431477 / 20000000000000000 : ℝ) (346031623143367 / 10000000000000000 : ℝ)
    (cell12272 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · have h := gap_lower (n := 12272) (a := (82255384331779 / 100000000000000 : ℝ)) (b := (83959573929 / 50000000000000 : ℝ)) (q := (144272559 / 6250000000 : ℝ))
      (E := (cell12272 ⟨53, by decide⟩).energy) (xi := (346031623143367 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12272 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12272]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12272])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12272) (a := (82255384331779 / 100000000000000 : ℝ)) (b := (83959573929 / 50000000000000 : ℝ)) (q := (144272559 / 6250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12272])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12272])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12272]

theorem cert12272_54 : CellCertificate 12272 (899047965703029 / 10000000000000000 : ℝ) (34231860431477 / 20000000000000000 : ℝ) (346031623143367 / 10000000000000000 : ℝ)
    (cell12272 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · have h := gap_lower (n := 12272) (a := (8222155407643 / 10000000000000 : ℝ)) (b := (83959573929 / 50000000000000 : ℝ)) (q := (1154182459067 / 50000000000000 : ℝ))
      (E := (cell12272 ⟨54, by decide⟩).energy) (xi := (346031623143367 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12272 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12272]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12272])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12272) (a := (8222155407643 / 10000000000000 : ℝ)) (b := (83959573929 / 50000000000000 : ℝ)) (q := (1154182459067 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12272])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12272])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12272]

theorem cert12272_55 : CellCertificate 12272 (899047965703029 / 10000000000000000 : ℝ) (34231860431477 / 20000000000000000 : ℝ) (346031623143367 / 10000000000000000 : ℝ)
    (cell12272 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · have h := gap_lower (n := 12272) (a := (82187747238913 / 100000000000000 : ℝ)) (b := (83959573929 / 50000000000000 : ℝ)) (q := (1154184464647 / 50000000000000 : ℝ))
      (E := (cell12272 ⟨55, by decide⟩).energy) (xi := (346031623143367 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12272 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12272]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12272])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12272) (a := (82187747238913 / 100000000000000 : ℝ)) (b := (83959573929 / 50000000000000 : ℝ)) (q := (1154184464647 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12272])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12272])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12272]

theorem cert12272_56 : CellCertificate 12272 (899047965703029 / 10000000000000000 : ℝ) (34231860431477 / 20000000000000000 : ℝ) (346031623143367 / 10000000000000000 : ℝ)
    (cell12272 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · have h := gap_lower (n := 12272) (a := (20538490947777 / 25000000000000 : ℝ)) (b := (83959573929 / 50000000000000 : ℝ)) (q := (461674583109 / 20000000000000 : ℝ))
      (E := (cell12272 ⟨56, by decide⟩).energy) (xi := (346031623143367 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12272 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12272]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12272])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12272) (a := (20538490947777 / 25000000000000 : ℝ)) (b := (83959573929 / 50000000000000 : ℝ)) (q := (461674583109 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12272])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12272])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12272]

theorem cert12272_57 : CellCertificate 12272 (899047965703029 / 10000000000000000 : ℝ) (34231860431477 / 20000000000000000 : ℝ) (346031623143367 / 10000000000000000 : ℝ)
    (cell12272 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · have h := gap_lower (n := 12272) (a := (82120203705037 / 100000000000000 : ℝ)) (b := (83959573929 / 50000000000000 : ℝ)) (q := (577094233213 / 25000000000000 : ℝ))
      (E := (cell12272 ⟨57, by decide⟩).energy) (xi := (346031623143367 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12272 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12272]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12272])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12272) (a := (82120203705037 / 100000000000000 : ℝ)) (b := (83959573929 / 50000000000000 : ℝ)) (q := (577094233213 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12272])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12272])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12272]

theorem cert12272_58 : CellCertificate 12272 (899047965703029 / 10000000000000000 : ℝ) (34231860431477 / 20000000000000000 : ℝ) (346031623143367 / 10000000000000000 : ℝ)
    (cell12272 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · have h := gap_lower (n := 12272) (a := (41043233476431 / 50000000000000 : ℝ)) (b := (83959573929 / 50000000000000 : ℝ)) (q := (1154190459407 / 50000000000000 : ℝ))
      (E := (cell12272 ⟨58, by decide⟩).energy) (xi := (346031623143367 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12272 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12272]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12272])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12272) (a := (41043233476431 / 50000000000000 : ℝ)) (b := (83959573929 / 50000000000000 : ℝ)) (q := (1154190459407 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12272])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12272])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12272]

theorem cert12272_59 : CellCertificate 12272 (899047965703029 / 10000000000000000 : ℝ) (34231860431477 / 20000000000000000 : ℝ) (346031623143367 / 10000000000000000 : ℝ)
    (cell12272 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · have h := gap_lower (n := 12272) (a := (82052753506883 / 100000000000000 : ℝ)) (b := (83959573929 / 50000000000000 : ℝ)) (q := (2308384929027 / 100000000000000 : ℝ))
      (E := (cell12272 ⟨59, by decide⟩).energy) (xi := (346031623143367 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12272 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12272]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12272])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12272) (a := (82052753506883 / 100000000000000 : ℝ)) (b := (83959573929 / 50000000000000 : ℝ)) (q := (2308384929027 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12272])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12272])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12272]

theorem cert12273_40 : CellCertificate 12273 (179803625388981 / 2000000000000000 : ℝ) (1711453514089737 / 1000000000000000000 : ℝ) (17300133844647 / 500000000000000 : ℝ)
    (cell12273 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · have h := gap_lower (n := 12273) (a := (82697318661249 / 100000000000000 : ℝ)) (b := (16790528347 / 10000000000000 : ℝ)) (q := (1154081829813 / 50000000000000 : ℝ))
      (E := (cell12273 ⟨40, by decide⟩).energy) (xi := (17300133844647 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12273 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12273]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12273])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12273) (a := (82697318661249 / 100000000000000 : ℝ)) (b := (16790528347 / 10000000000000 : ℝ)) (q := (1154081829813 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12273])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12273])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12273]

theorem cert12273_41 : CellCertificate 12273 (179803625388981 / 2000000000000000 : ℝ) (1711453514089737 / 1000000000000000000 : ℝ) (17300133844647 / 500000000000000 : ℝ)
    (cell12273 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · have h := gap_lower (n := 12273) (a := (82663181668727 / 100000000000000 : ℝ)) (b := (16790528347 / 10000000000000 : ℝ)) (q := (1154083830233 / 50000000000000 : ℝ))
      (E := (cell12273 ⟨41, by decide⟩).energy) (xi := (17300133844647 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12273 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12273]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12273])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12273) (a := (82663181668727 / 100000000000000 : ℝ)) (b := (16790528347 / 10000000000000 : ℝ)) (q := (1154083830233 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12273])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12273])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12273]

theorem cert12273_42 : CellCertificate 12273 (179803625388981 / 2000000000000000 : ℝ) (1711453514089737 / 1000000000000000000 : ℝ) (17300133844647 / 500000000000000 : ℝ)
    (cell12273 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · have h := gap_lower (n := 12273) (a := (82629068472337 / 100000000000000 : ℝ)) (b := (16790528347 / 10000000000000 : ℝ)) (q := (577042914639 / 25000000000000 : ℝ))
      (E := (cell12273 ⟨42, by decide⟩).energy) (xi := (17300133844647 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12273 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12273]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12273])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12273) (a := (82629068472337 / 100000000000000 : ℝ)) (b := (16790528347 / 10000000000000 : ℝ)) (q := (577042914639 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12273])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12273])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12273]

theorem cert12273_43 : CellCertificate 12273 (179803625388981 / 2000000000000000 : ℝ) (1711453514089737 / 1000000000000000000 : ℝ) (17300133844647 / 500000000000000 : ℝ)
    (cell12273 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · have h := gap_lower (n := 12273) (a := (41297489521027 / 50000000000000 : ℝ)) (b := (16790528347 / 10000000000000 : ℝ)) (q := (1154087826883 / 50000000000000 : ℝ))
      (E := (cell12273 ⟨43, by decide⟩).energy) (xi := (17300133844647 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12273 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12273]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12273])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12273) (a := (41297489521027 / 50000000000000 : ℝ)) (b := (16790528347 / 10000000000000 : ℝ)) (q := (1154087826883 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12273])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12273])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12273]

theorem cert12273_44 : CellCertificate 12273 (179803625388981 / 2000000000000000 : ℝ) (1711453514089737 / 1000000000000000000 : ℝ) (17300133844647 / 500000000000000 : ℝ)
    (cell12273 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · have h := gap_lower (n := 12273) (a := (20640228337001 / 25000000000000 : ℝ)) (b := (16790528347 / 10000000000000 : ℝ)) (q := (1154089822873 / 50000000000000 : ℝ))
      (E := (cell12273 ⟨44, by decide⟩).energy) (xi := (17300133844647 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12273 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12273]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12273])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12273) (a := (20640228337001 / 25000000000000 : ℝ)) (b := (16790528347 / 10000000000000 : ℝ)) (q := (1154089822873 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12273])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12273])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12273]

theorem cert12273_45 : CellCertificate 12273 (179803625388981 / 2000000000000000 : ℝ) (1711453514089737 / 1000000000000000000 : ℝ) (17300133844647 / 500000000000000 : ℝ)
    (cell12273 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · have h := gap_lower (n := 12273) (a := (5157929460029 / 6250000000000 : ℝ)) (b := (16790528347 / 10000000000000 : ℝ)) (q := (2308183633929 / 100000000000000 : ℝ))
      (E := (cell12273 ⟨45, by decide⟩).energy) (xi := (17300133844647 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12273 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12273]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12273])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12273) (a := (5157929460029 / 6250000000000 : ℝ)) (b := (16790528347 / 10000000000000 : ℝ)) (q := (2308183633929 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12273])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12273])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12273]

theorem cert12273_46 : CellCertificate 12273 (179803625388981 / 2000000000000000 : ℝ) (1711453514089737 / 1000000000000000000 : ℝ) (17300133844647 / 500000000000000 : ℝ)
    (cell12273 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · have h := gap_lower (n := 12273) (a := (82492853049863 / 100000000000000 : ℝ)) (b := (16790528347 / 10000000000000 : ℝ)) (q := (1154093808763 / 50000000000000 : ℝ))
      (E := (cell12273 ⟨46, by decide⟩).energy) (xi := (17300133844647 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12273 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12273]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12273])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12273) (a := (82492853049863 / 100000000000000 : ℝ)) (b := (16790528347 / 10000000000000 : ℝ)) (q := (1154093808763 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12273])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12273])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12273]

theorem cert12273_47 : CellCertificate 12273 (179803625388981 / 2000000000000000 : ℝ) (1711453514089737 / 1000000000000000000 : ℝ) (17300133844647 / 500000000000000 : ℝ)
    (cell12273 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · have h := gap_lower (n := 12273) (a := (82458858386777 / 100000000000000 : ℝ)) (b := (16790528347 / 10000000000000 : ℝ)) (q := (577047898883 / 25000000000000 : ℝ))
      (E := (cell12273 ⟨47, by decide⟩).energy) (xi := (17300133844647 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12273 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12273]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12273])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12273) (a := (82458858386777 / 100000000000000 : ℝ)) (b := (16790528347 / 10000000000000 : ℝ)) (q := (577047898883 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12273])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12273])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12273]

theorem cert12273_48 : CellCertificate 12273 (179803625388981 / 2000000000000000 : ℝ) (1711453514089737 / 1000000000000000000 : ℝ) (17300133844647 / 500000000000000 : ℝ)
    (cell12273 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · have h := gap_lower (n := 12273) (a := (82424887341931 / 100000000000000 : ℝ)) (b := (16790528347 / 10000000000000 : ℝ)) (q := (2308195625619 / 100000000000000 : ℝ))
      (E := (cell12273 ⟨48, by decide⟩).energy) (xi := (17300133844647 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12273 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12273]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12273])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12273) (a := (82424887341931 / 100000000000000 : ℝ)) (b := (16790528347 / 10000000000000 : ℝ)) (q := (2308195625619 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12273])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12273])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12273]

theorem cert12273_49 : CellCertificate 12273 (179803625388981 / 2000000000000000 : ℝ) (1711453514089737 / 1000000000000000000 : ℝ) (17300133844647 / 500000000000000 : ℝ)
    (cell12273 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · have h := gap_lower (n := 12273) (a := (82390939886199 / 100000000000000 : ℝ)) (b := (16790528347 / 10000000000000 : ℝ)) (q := (577049897147 / 25000000000000 : ℝ))
      (E := (cell12273 ⟨49, by decide⟩).energy) (xi := (17300133844647 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12273 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12273]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12273])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12273) (a := (82390939886199 / 100000000000000 : ℝ)) (b := (16790528347 / 10000000000000 : ℝ)) (q := (577049897147 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12273])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12273])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12273]

theorem cert12273_50 : CellCertificate 12273 (179803625388981 / 2000000000000000 : ℝ) (1711453514089737 / 1000000000000000000 : ℝ) (17300133844647 / 500000000000000 : ℝ)
    (cell12273 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · have h := gap_lower (n := 12273) (a := (82357015990599 / 100000000000000 : ℝ)) (b := (16790528347 / 10000000000000 : ℝ)) (q := (2308203600593 / 100000000000000 : ℝ))
      (E := (cell12273 ⟨50, by decide⟩).energy) (xi := (17300133844647 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12273 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12273]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12273])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12273) (a := (82357015990599 / 100000000000000 : ℝ)) (b := (16790528347 / 10000000000000 : ℝ)) (q := (2308203600593 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12273])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12273])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12273]

theorem cert12273_51 : CellCertificate 12273 (179803625388981 / 2000000000000000 : ℝ) (1711453514089737 / 1000000000000000000 : ℝ) (17300133844647 / 500000000000000 : ℝ)
    (cell12273 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · have h := gap_lower (n := 12273) (a := (41161557813149 / 50000000000000 : ℝ)) (b := (16790528347 / 10000000000000 : ℝ)) (q := (2308207600873 / 100000000000000 : ℝ))
      (E := (cell12273 ⟨51, by decide⟩).energy) (xi := (17300133844647 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12273 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12273]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12273])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12273) (a := (41161557813149 / 50000000000000 : ℝ)) (b := (16790528347 / 10000000000000 : ℝ)) (q := (2308207600873 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12273])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12273])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12273]

theorem cert12273_52 : CellCertificate 12273 (179803625388981 / 2000000000000000 : ℝ) (1711453514089737 / 1000000000000000000 : ℝ) (17300133844647 / 500000000000000 : ℝ)
    (cell12273 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · have h := gap_lower (n := 12273) (a := (16457847752921 / 20000000000000 : ℝ)) (b := (16790528347 / 10000000000000 : ℝ)) (q := (2308211587349 / 100000000000000 : ℝ))
      (E := (cell12273 ⟨52, by decide⟩).energy) (xi := (17300133844647 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12273 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12273]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12273])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12273) (a := (16457847752921 / 20000000000000 : ℝ)) (b := (16790528347 / 10000000000000 : ℝ)) (q := (2308211587349 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12273])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12273])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12273]

theorem cert12273_53 : CellCertificate 12273 (179803625388981 / 2000000000000000 : ℝ) (1711453514089737 / 1000000000000000000 : ℝ) (17300133844647 / 500000000000000 : ℝ)
    (cell12273 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · have h := gap_lower (n := 12273) (a := (41127692688487 / 50000000000000 : ℝ)) (b := (16790528347 / 10000000000000 : ℝ)) (q := (2308215616737 / 100000000000000 : ℝ))
      (E := (cell12273 ⟨53, by decide⟩).energy) (xi := (17300133844647 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12273 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12273]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12273])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12273) (a := (41127692688487 / 50000000000000 : ℝ)) (b := (16790528347 / 10000000000000 : ℝ)) (q := (2308215616737 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12273])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12273])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12273]

theorem cert12273_54 : CellCertificate 12273 (179803625388981 / 2000000000000000 : ℝ) (1711453514089737 / 1000000000000000000 : ℝ) (17300133844647 / 500000000000000 : ℝ)
    (cell12273 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · have h := gap_lower (n := 12273) (a := (82221555435003 / 100000000000000 : ℝ)) (b := (16790528347 / 10000000000000 : ℝ)) (q := (2308219568533 / 100000000000000 : ℝ))
      (E := (cell12273 ⟨54, by decide⟩).energy) (xi := (17300133844647 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12273 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12273]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12273])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12273) (a := (82221555435003 / 100000000000000 : ℝ)) (b := (16790528347 / 10000000000000 : ℝ)) (q := (2308219568533 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12273])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12273])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12273]

theorem cert12273_55 : CellCertificate 12273 (179803625388981 / 2000000000000000 : ℝ) (1711453514089737 / 1000000000000000000 : ℝ) (17300133844647 / 500000000000000 : ℝ)
    (cell12273 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · have h := gap_lower (n := 12273) (a := (82187748910431 / 100000000000000 : ℝ)) (b := (16790528347 / 10000000000000 : ℝ)) (q := (461644711613 / 20000000000000 : ℝ))
      (E := (cell12273 ⟨55, by decide⟩).energy) (xi := (17300133844647 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12273 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12273]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12273])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12273) (a := (82187748910431 / 100000000000000 : ℝ)) (b := (16790528347 / 10000000000000 : ℝ)) (q := (461644711613 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12273])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12273])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12273]

theorem cert12273_56 : CellCertificate 12273 (179803625388981 / 2000000000000000 : ℝ) (1711453514089737 / 1000000000000000000 : ℝ) (17300133844647 / 500000000000000 : ℝ)
    (cell12273 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · have h := gap_lower (n := 12273) (a := (82153965775141 / 100000000000000 : ℝ)) (b := (16790528347 / 10000000000000 : ℝ)) (q := (92329103299 / 4000000000000 : ℝ))
      (E := (cell12273 ⟨56, by decide⟩).energy) (xi := (17300133844647 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12273 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12273]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12273])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12273) (a := (82153965775141 / 100000000000000 : ℝ)) (b := (16790528347 / 10000000000000 : ℝ)) (q := (92329103299 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12273])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12273])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12273]

theorem cert12273_57 : CellCertificate 12273 (179803625388981 / 2000000000000000 : ℝ) (1711453514089737 / 1000000000000000000 : ℝ) (17300133844647 / 500000000000000 : ℝ)
    (cell12273 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · have h := gap_lower (n := 12273) (a := (16424041200231 / 20000000000000 : ℝ)) (b := (16790528347 / 10000000000000 : ℝ)) (q := (2308231579591 / 100000000000000 : ℝ))
      (E := (cell12273 ⟨57, by decide⟩).energy) (xi := (17300133844647 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12273 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12273]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12273])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12273) (a := (16424041200231 / 20000000000000 : ℝ)) (b := (16790528347 / 10000000000000 : ℝ)) (q := (2308231579591 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12273])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12273])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12273]

theorem cert12273_58 : CellCertificate 12273 (179803625388981 / 2000000000000000 : ℝ) (1711453514089737 / 1000000000000000000 : ℝ) (17300133844647 / 500000000000000 : ℝ)
    (cell12273 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · have h := gap_lower (n := 12273) (a := (16417293912127 / 20000000000000 : ℝ)) (b := (16790528347 / 10000000000000 : ℝ)) (q := (1154117802597 / 50000000000000 : ℝ))
      (E := (cell12273 ⟨58, by decide⟩).energy) (xi := (17300133844647 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12273 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12273]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12273])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12273) (a := (16417293912127 / 20000000000000 : ℝ)) (b := (16790528347 / 10000000000000 : ℝ)) (q := (1154117802597 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12273])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12273])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12273]

theorem cert12273_59 : CellCertificate 12273 (179803625388981 / 2000000000000000 : ℝ) (1711453514089737 / 1000000000000000000 : ℝ) (17300133844647 / 500000000000000 : ℝ)
    (cell12273 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · have h := gap_lower (n := 12273) (a := (82052756425883 / 100000000000000 : ℝ)) (b := (16790528347 / 10000000000000 : ℝ)) (q := (46164791933 / 2000000000000 : ℝ))
      (E := (cell12273 ⟨59, by decide⟩).energy) (xi := (17300133844647 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12273 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12273]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12273])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12273) (a := (82052756425883 / 100000000000000 : ℝ)) (b := (16790528347 / 10000000000000 : ℝ)) (q := (46164791933 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12273])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12273])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12273]

theorem cert12274_40 : CellCertificate 12274 (898988292871121 / 10000000000000000 : ℝ) (1711314029345551 / 1000000000000000000 : ℝ) (69194747121223 / 2000000000000000 : ℝ)
    (cell12274 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · have h := gap_lower (n := 12274) (a := (82697315593883 / 100000000000000 : ℝ)) (b := (839457107 / 500000000000 : ℝ)) (q := (2308018390357 / 100000000000000 : ℝ))
      (E := (cell12274 ⟨40, by decide⟩).energy) (xi := (69194747121223 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12274 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12274]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12274])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12274) (a := (82697315593883 / 100000000000000 : ℝ)) (b := (839457107 / 500000000000 : ℝ)) (q := (2308018390357 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12274])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12274])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12274]

theorem cert12274_41 : CellCertificate 12274 (898988292871121 / 10000000000000000 : ℝ) (1711314029345551 / 1000000000000000000 : ℝ) (69194747121223 / 2000000000000000 : ℝ)
    (cell12274 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · have h := gap_lower (n := 12274) (a := (41331589460191 / 50000000000000 : ℝ)) (b := (839457107 / 500000000000 : ℝ)) (q := (1154011179757 / 50000000000000 : ℝ))
      (E := (cell12274 ⟨41, by decide⟩).energy) (xi := (69194747121223 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12274 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12274]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12274])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12274) (a := (41331589460191 / 50000000000000 : ℝ)) (b := (839457107 / 500000000000 : ℝ)) (q := (1154011179757 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12274])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12274])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12274]

theorem cert12274_42 : CellCertificate 12274 (898988292871121 / 10000000000000000 : ℝ) (1711314029345551 / 1000000000000000000 : ℝ) (69194747121223 / 2000000000000000 : ℝ)
    (cell12274 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · have h := gap_lower (n := 12274) (a := (82629066042571 / 100000000000000 : ℝ)) (b := (839457107 / 500000000000 : ℝ)) (q := (2308026326639 / 100000000000000 : ℝ))
      (E := (cell12274 ⟨42, by decide⟩).energy) (xi := (69194747121223 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12274 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12274]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12274])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12274) (a := (82629066042571 / 100000000000000 : ℝ)) (b := (839457107 / 500000000000 : ℝ)) (q := (2308026326639 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12274])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12274])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12274]

theorem cert12274_43 : CellCertificate 12274 (898988292871121 / 10000000000000000 : ℝ) (1711314029345551 / 1000000000000000000 : ℝ) (69194747121223 / 2000000000000000 : ℝ)
    (cell12274 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · have h := gap_lower (n := 12274) (a := (41297488465213 / 50000000000000 : ℝ)) (b := (839457107 / 500000000000 : ℝ)) (q := (1154015175187 / 50000000000000 : ℝ))
      (E := (cell12274 ⟨43, by decide⟩).energy) (xi := (69194747121223 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12274 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12274]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12274])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12274) (a := (41297488465213 / 50000000000000 : ℝ)) (b := (839457107 / 500000000000 : ℝ)) (q := (1154015175187 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12274])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12274])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12274]

theorem cert12274_44 : CellCertificate 12274 (898988292871121 / 10000000000000000 : ℝ) (1711314029345551 / 1000000000000000000 : ℝ) (69194747121223 / 2000000000000000 : ℝ)
    (cell12274 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · have h := gap_lower (n := 12274) (a := (82560911554073 / 100000000000000 : ℝ)) (b := (839457107 / 500000000000 : ℝ)) (q := (2308034371643 / 100000000000000 : ℝ))
      (E := (cell12274 ⟨44, by decide⟩).energy) (xi := (69194747121223 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12274 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12274]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12274])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12274) (a := (82560911554073 / 100000000000000 : ℝ)) (b := (839457107 / 500000000000 : ℝ)) (q := (2308034371643 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12274])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12274])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12274]

theorem cert12274_45 : CellCertificate 12274 (898988292871121 / 10000000000000000 : ℝ) (1711314029345551 / 1000000000000000000 : ℝ) (69194747121223 / 2000000000000000 : ℝ)
    (cell12274 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · have h := gap_lower (n := 12274) (a := (5157929367737 / 6250000000000 : ℝ)) (b := (839457107 / 500000000000 : ℝ)) (q := (461607666211 / 20000000000000 : ℝ))
      (E := (cell12274 ⟨45, by decide⟩).energy) (xi := (69194747121223 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12274 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12274]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12274])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12274) (a := (5157929367737 / 6250000000000 : ℝ)) (b := (839457107 / 500000000000 : ℝ)) (q := (461607666211 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12274])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12274])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12274]

theorem cert12274_46 : CellCertificate 12274 (898988292871121 / 10000000000000000 : ℝ) (1711314029345551 / 1000000000000000000 : ℝ) (69194747121223 / 2000000000000000 : ℝ)
    (cell12274 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · have h := gap_lower (n := 12274) (a := (82492851890011 / 100000000000000 : ℝ)) (b := (839457107 / 500000000000 : ℝ)) (q := (14425264659 / 625000000000 : ℝ))
      (E := (cell12274 ⟨46, by decide⟩).energy) (xi := (69194747121223 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12274 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12274]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12274])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12274) (a := (82492851890011 / 100000000000000 : ℝ)) (b := (839457107 / 500000000000 : ℝ)) (q := (14425264659 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12274])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12274])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12274]

theorem cert12274_47 : CellCertificate 12274 (898988292871121 / 10000000000000000 : ℝ) (1711314029345551 / 1000000000000000000 : ℝ) (69194747121223 / 2000000000000000 : ℝ)
    (cell12274 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · have h := gap_lower (n := 12274) (a := (82458857543307 / 100000000000000 : ℝ)) (b := (839457107 / 500000000000 : ℝ)) (q := (577011588749 / 25000000000000 : ℝ))
      (E := (cell12274 ⟨47, by decide⟩).energy) (xi := (69194747121223 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12274 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12274]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12274])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12274) (a := (82458857543307 / 100000000000000 : ℝ)) (b := (839457107 / 500000000000 : ℝ)) (q := (577011588749 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12274])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12274])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12274]

theorem cert12274_48 : CellCertificate 12274 (898988292871121 / 10000000000000000 : ℝ) (1711314029345551 / 1000000000000000000 : ℝ) (69194747121223 / 2000000000000000 : ℝ)
    (cell12274 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · have h := gap_lower (n := 12274) (a := (41212443407203 / 50000000000000 : ℝ)) (b := (839457107 / 500000000000 : ℝ)) (q := (2308050358501 / 100000000000000 : ℝ))
      (E := (cell12274 ⟨48, by decide⟩).energy) (xi := (69194747121223 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12274 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12274]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12274])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12274) (a := (41212443407203 / 50000000000000 : ℝ)) (b := (839457107 / 500000000000 : ℝ)) (q := (2308050358501 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12274])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12274])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12274]

theorem cert12274_49 : CellCertificate 12274 (898988292871121 / 10000000000000000 : ℝ) (1711314029345551 / 1000000000000000000 : ℝ) (69194747121223 / 2000000000000000 : ℝ)
    (cell12274 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · have h := gap_lower (n := 12274) (a := (82390939674183 / 100000000000000 : ℝ)) (b := (839457107 / 500000000000 : ℝ)) (q := (1154027177257 / 50000000000000 : ℝ))
      (E := (cell12274 ⟨49, by decide⟩).energy) (xi := (69194747121223 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12274 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12274]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12274])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12274) (a := (82390939674183 / 100000000000000 : ℝ)) (b := (839457107 / 500000000000 : ℝ)) (q := (1154027177257 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12274])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12274])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12274]

theorem cert12274_50 : CellCertificate 12274 (898988292871121 / 10000000000000000 : ℝ) (1711314029345551 / 1000000000000000000 : ℝ) (69194747121223 / 2000000000000000 : ℝ)
    (cell12274 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · have h := gap_lower (n := 12274) (a := (10294627011707 / 12500000000000 : ℝ)) (b := (839457107 / 500000000000 : ℝ)) (q := (288507292673 / 12500000000000 : ℝ))
      (E := (cell12274 ⟨50, by decide⟩).energy) (xi := (69194747121223 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12274 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12274]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12274])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12274) (a := (10294627011707 / 12500000000000 : ℝ)) (b := (839457107 / 500000000000 : ℝ)) (q := (288507292673 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12274])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12274])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12274]

theorem cert12274_51 : CellCertificate 12274 (898988292871121 / 10000000000000000 : ℝ) (1711314029345551 / 1000000000000000000 : ℝ) (69194747121223 / 2000000000000000 : ℝ)
    (cell12274 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · have h := gap_lower (n := 12274) (a := (82323116043993 / 100000000000000 : ℝ)) (b := (839457107 / 500000000000 : ℝ)) (q := (57701557931 / 2500000000000 : ℝ))
      (E := (cell12274 ⟨51, by decide⟩).energy) (xi := (69194747121223 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12274 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12274]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12274])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12274) (a := (82323116043993 / 100000000000000 : ℝ)) (b := (839457107 / 500000000000 : ℝ)) (q := (57701557931 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12274])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12274])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12274]

theorem cert12274_52 : CellCertificate 12274 (898988292871121 / 10000000000000000 : ℝ) (1711314029345551 / 1000000000000000000 : ℝ) (69194747121223 / 2000000000000000 : ℝ)
    (cell12274 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · have h := gap_lower (n := 12274) (a := (10286154937063 / 12500000000000 : ℝ)) (b := (839457107 / 500000000000 : ℝ)) (q := (2308066338989 / 100000000000000 : ℝ))
      (E := (cell12274 ⟨52, by decide⟩).energy) (xi := (69194747121223 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12274 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12274]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12274])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12274) (a := (10286154937063 / 12500000000000 : ℝ)) (b := (839457107 / 500000000000 : ℝ)) (q := (2308066338989 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12274])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12274])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12274]

theorem cert12274_53 : CellCertificate 12274 (898988292871121 / 10000000000000000 : ℝ) (1711314029345551 / 1000000000000000000 : ℝ) (69194747121223 / 2000000000000000 : ℝ)
    (cell12274 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · have h := gap_lower (n := 12274) (a := (16451077284529 / 20000000000000 : ℝ)) (b := (839457107 / 500000000000 : ℝ)) (q := (144254392899 / 6250000000000 : ℝ))
      (E := (cell12274 ⟨53, by decide⟩).energy) (xi := (69194747121223 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12274 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12274]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12274])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12274) (a := (16451077284529 / 20000000000000 : ℝ)) (b := (839457107 / 500000000000 : ℝ)) (q := (144254392899 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12274])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12274])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12274]

theorem cert12274_54 : CellCertificate 12274 (898988292871121 / 10000000000000000 : ℝ) (1711314029345551 / 1000000000000000000 : ℝ) (69194747121223 / 2000000000000000 : ℝ)
    (cell12274 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · have h := gap_lower (n := 12274) (a := (20555389198503 / 25000000000000 : ℝ)) (b := (839457107 / 500000000000 : ℝ)) (q := (2308074333951 / 100000000000000 : ℝ))
      (E := (cell12274 ⟨54, by decide⟩).energy) (xi := (69194747121223 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12274 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12274]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12274])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12274) (a := (20555389198503 / 25000000000000 : ℝ)) (b := (839457107 / 500000000000 : ℝ)) (q := (2308074333951 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12274])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12274])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12274]

theorem cert12274_55 : CellCertificate 12274 (898988292871121 / 10000000000000000 : ℝ) (1711314029345551 / 1000000000000000000 : ℝ) (69194747121223 / 2000000000000000 : ℝ)
    (cell12274 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · have h := gap_lower (n := 12274) (a := (20546937645587 / 25000000000000 : ℝ)) (b := (839457107 / 500000000000 : ℝ)) (q := (2308078301941 / 100000000000000 : ℝ))
      (E := (cell12274 ⟨55, by decide⟩).energy) (xi := (69194747121223 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12274 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12274]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12274])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12274) (a := (20546937645587 / 25000000000000 : ℝ)) (b := (839457107 / 500000000000 : ℝ)) (q := (2308078301941 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12274])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12274])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12274]

theorem cert12274_56 : CellCertificate 12274 (898988292871121 / 10000000000000000 : ℝ) (1711314029345551 / 1000000000000000000 : ℝ) (69194747121223 / 2000000000000000 : ℝ)
    (cell12274 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · have h := gap_lower (n := 12274) (a := (41076983879767 / 50000000000000 : ℝ)) (b := (839457107 / 500000000000 : ℝ)) (q := (577020576379 / 25000000000000 : ℝ))
      (E := (cell12274 ⟨56, by decide⟩).energy) (xi := (69194747121223 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12274 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12274]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12274])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12274) (a := (41076983879767 / 50000000000000 : ℝ)) (b := (839457107 / 500000000000 : ℝ)) (q := (577020576379 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12274])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12274])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12274]

theorem cert12274_57 : CellCertificate 12274 (898988292871121 / 10000000000000000 : ℝ) (1711314029345551 / 1000000000000000000 : ℝ) (69194747121223 / 2000000000000000 : ℝ)
    (cell12274 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · have h := gap_lower (n := 12274) (a := (82120208297593 / 100000000000000 : ℝ)) (b := (839457107 / 500000000000 : ℝ)) (q := (288510785313 / 12500000000000 : ℝ))
      (E := (cell12274 ⟨57, by decide⟩).energy) (xi := (69194747121223 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12274 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12274]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12274])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12274) (a := (82120208297593 / 100000000000000 : ℝ)) (b := (839457107 / 500000000000 : ℝ)) (q := (288510785313 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12274])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12274])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12274]

theorem cert12274_58 : CellCertificate 12274 (898988292871121 / 10000000000000000 : ℝ) (1711314029345551 / 1000000000000000000 : ℝ) (69194747121223 / 2000000000000000 : ℝ)
    (cell12274 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · have h := gap_lower (n := 12274) (a := (8208647216869 / 10000000000000 : ℝ)) (b := (839457107 / 500000000000 : ℝ)) (q := (461618057737 / 20000000000000 : ℝ))
      (E := (cell12274 ⟨58, by decide⟩).energy) (xi := (69194747121223 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12274 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12274]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12274])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12274) (a := (8208647216869 / 10000000000000 : ℝ)) (b := (839457107 / 500000000000 : ℝ)) (q := (461618057737 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12274])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12274])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12274]

theorem cert12274_59 : CellCertificate 12274 (898988292871121 / 10000000000000000 : ℝ) (1711314029345551 / 1000000000000000000 : ℝ) (69194747121223 / 2000000000000000 : ℝ)
    (cell12274 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · have h := gap_lower (n := 12274) (a := (20513189836281 / 25000000000000 : ℝ)) (b := (839457107 / 500000000000 : ℝ)) (q := (36063973759 / 1562500000000 : ℝ))
      (E := (cell12274 ⟨59, by decide⟩).energy) (xi := (69194747121223 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12274 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12274]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12274])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12274) (a := (20513189836281 / 25000000000000 : ℝ)) (b := (839457107 / 500000000000 : ℝ)) (q := (36063973759 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12274])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12274])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12274]

end BstLean.Part263
