import BstLean.Part268CellShard20Data

/-! Twenty scalar cells per dimension in a 25-dimension shard. -/
namespace BstLean.Part268
open Real BstLean.Part263

theorem cert12850_0 : CellCertificate 12850 (882547001325949 / 10000000000000000 : ℝ) (326915923546393 / 200000000000000000 : ℝ) (66017052037419 / 2000000000000000 : ℝ)
    (cell12850 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · have h := gap_lower (n := 12850) (a := (10509218443829 / 12500000000000 : ℝ)) (b := (160273419151 / 100000000000000 : ℝ)) (q := (2233421087907 / 100000000000000 : ℝ))
      (E := (cell12850 ⟨0, by decide⟩).energy) (xi := (66017052037419 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12850 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12850]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12850])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12850) (a := (10509218443829 / 12500000000000 : ℝ)) (b := (160273419151 / 100000000000000 : ℝ)) (q := (2233421087907 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12850])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12850])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12850]

theorem cert12850_1 : CellCertificate 12850 (882547001325949 / 10000000000000000 : ℝ) (326915923546393 / 200000000000000000 : ℝ) (66017052037419 / 2000000000000000 : ℝ)
    (cell12850 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · have h := gap_lower (n := 12850) (a := (42019410064339 / 50000000000000 : ℝ)) (b := (160273419151 / 100000000000000 : ℝ)) (q := (89337003119 / 4000000000000 : ℝ))
      (E := (cell12850 ⟨1, by decide⟩).energy) (xi := (66017052037419 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12850 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12850]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12850])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12850) (a := (42019410064339 / 50000000000000 : ℝ)) (b := (160273419151 / 100000000000000 : ℝ)) (q := (89337003119 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12850])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12850])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12850]

theorem cert12850_2 : CellCertificate 12850 (882547001325949 / 10000000000000000 : ℝ) (326915923546393 / 200000000000000000 : ℝ) (66017052037419 / 2000000000000000 : ℝ)
    (cell12850 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · have h := gap_lower (n := 12850) (a := (84003917573749 / 100000000000000 : ℝ)) (b := (160273419151 / 100000000000000 : ℝ)) (q := (1116714545031 / 50000000000000 : ℝ))
      (E := (cell12850 ⟨2, by decide⟩).energy) (xi := (66017052037419 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12850 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12850]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12850])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12850) (a := (84003917573749 / 100000000000000 : ℝ)) (b := (160273419151 / 100000000000000 : ℝ)) (q := (1116714545031 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12850])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12850])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12850]

theorem cert12850_3 : CellCertificate 12850 (882547001325949 / 10000000000000000 : ℝ) (326915923546393 / 200000000000000000 : ℝ) (66017052037419 / 2000000000000000 : ℝ)
    (cell12850 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · have h := gap_lower (n := 12850) (a := (41984519924747 / 50000000000000 : ℝ)) (b := (160273419151 / 100000000000000 : ℝ)) (q := (1116716537451 / 50000000000000 : ℝ))
      (E := (cell12850 ⟨3, by decide⟩).energy) (xi := (66017052037419 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12850 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12850]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12850])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12850) (a := (41984519924747 / 50000000000000 : ℝ)) (b := (160273419151 / 100000000000000 : ℝ)) (q := (1116716537451 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12850])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12850])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12850]

theorem cert12850_4 : CellCertificate 12850 (882547001325949 / 10000000000000000 : ℝ) (326915923546393 / 200000000000000000 : ℝ) (66017052037419 / 2000000000000000 : ℝ)
    (cell12850 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · have h := gap_lower (n := 12850) (a := (83934186919751 / 100000000000000 : ℝ)) (b := (160273419151 / 100000000000000 : ℝ)) (q := (558359274679 / 25000000000000 : ℝ))
      (E := (cell12850 ⟨4, by decide⟩).energy) (xi := (66017052037419 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12850 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12850]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12850])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12850) (a := (83934186919751 / 100000000000000 : ℝ)) (b := (160273419151 / 100000000000000 : ℝ)) (q := (558359274679 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12850])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12850])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12850]

theorem cert12850_5 : CellCertificate 12850 (882547001325949 / 10000000000000000 : ℝ) (326915923546393 / 200000000000000000 : ℝ) (66017052037419 / 2000000000000000 : ℝ)
    (cell12850 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · have h := gap_lower (n := 12850) (a := (83899358748547 / 100000000000000 : ℝ)) (b := (160273419151 / 100000000000000 : ℝ)) (q := (2233441111679 / 100000000000000 : ℝ))
      (E := (cell12850 ⟨5, by decide⟩).energy) (xi := (66017052037419 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12850 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12850]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12850])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12850) (a := (83899358748547 / 100000000000000 : ℝ)) (b := (160273419151 / 100000000000000 : ℝ)) (q := (2233441111679 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12850])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12850])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12850]

theorem cert12850_6 : CellCertificate 12850 (882547001325949 / 10000000000000000 : ℝ) (326915923546393 / 200000000000000000 : ℝ) (66017052037419 / 2000000000000000 : ℝ)
    (cell12850 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · have h := gap_lower (n := 12850) (a := (83864555300099 / 100000000000000 : ℝ)) (b := (160273419151 / 100000000000000 : ℝ)) (q := (34897579119 / 1562500000000 : ℝ))
      (E := (cell12850 ⟨6, by decide⟩).energy) (xi := (66017052037419 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12850 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12850]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12850])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12850) (a := (83864555300099 / 100000000000000 : ℝ)) (b := (160273419151 / 100000000000000 : ℝ)) (q := (34897579119 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12850])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12850])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12850]

theorem cert12850_7 : CellCertificate 12850 (882547001325949 / 10000000000000000 : ℝ) (326915923546393 / 200000000000000000 : ℝ) (66017052037419 / 2000000000000000 : ℝ)
    (cell12850 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · have h := gap_lower (n := 12850) (a := (83829776538813 / 100000000000000 : ℝ)) (b := (160273419151 / 100000000000000 : ℝ)) (q := (2233449077971 / 100000000000000 : ℝ))
      (E := (cell12850 ⟨7, by decide⟩).energy) (xi := (66017052037419 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12850 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12850]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12850])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12850) (a := (83829776538813 / 100000000000000 : ℝ)) (b := (160273419151 / 100000000000000 : ℝ)) (q := (2233449077971 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12850])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12850])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12850]

theorem cert12850_8 : CellCertificate 12850 (882547001325949 / 10000000000000000 : ℝ) (326915923546393 / 200000000000000000 : ℝ) (66017052037419 / 2000000000000000 : ℝ)
    (cell12850 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · have h := gap_lower (n := 12850) (a := (41897511214639 / 50000000000000 : ℝ)) (b := (160273419151 / 100000000000000 : ℝ)) (q := (2233453104087 / 100000000000000 : ℝ))
      (E := (cell12850 ⟨8, by decide⟩).energy) (xi := (66017052037419 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12850 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12850]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12850])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12850) (a := (41897511214639 / 50000000000000 : ℝ)) (b := (160273419151 / 100000000000000 : ℝ)) (q := (2233453104087 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12850])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12850])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12850]

theorem cert12850_9 : CellCertificate 12850 (882547001325949 / 10000000000000000 : ℝ) (326915923546393 / 200000000000000000 : ℝ) (66017052037419 / 2000000000000000 : ℝ)
    (cell12850 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · have h := gap_lower (n := 12850) (a := (5235018308517 / 6250000000000 : ℝ)) (b := (160273419151 / 100000000000000 : ℝ)) (q := (27918213637 / 1250000000000 : ℝ))
      (E := (cell12850 ⟨9, by decide⟩).energy) (xi := (66017052037419 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12850 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12850]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12850])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12850) (a := (5235018308517 / 6250000000000 : ℝ)) (b := (160273419151 / 100000000000000 : ℝ)) (q := (27918213637 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12850])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12850])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12850]

theorem cert12850_10 : CellCertificate 12850 (882547001325949 / 10000000000000000 : ℝ) (326915923546393 / 200000000000000000 : ℝ) (66017052037419 / 2000000000000000 : ℝ)
    (cell12850 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · have h := gap_lower (n := 12850) (a := (41862794012377 / 50000000000000 : ℝ)) (b := (160273419151 / 100000000000000 : ℝ)) (q := (1744891487 / 78125000000 : ℝ))
      (E := (cell12850 ⟨10, by decide⟩).energy) (xi := (66017052037419 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12850 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12850]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12850])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12850) (a := (41862794012377 / 50000000000000 : ℝ)) (b := (160273419151 / 100000000000000 : ℝ)) (q := (1744891487 / 78125000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12850])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12850])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12850]

theorem cert12850_11 : CellCertificate 12850 (882547001325949 / 10000000000000000 : ℝ) (326915923546393 / 200000000000000000 : ℝ) (66017052037419 / 2000000000000000 : ℝ)
    (cell12850 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · have h := gap_lower (n := 12850) (a := (41845453829933 / 50000000000000 : ℝ)) (b := (160273419151 / 100000000000000 : ℝ)) (q := (2233465089739 / 100000000000000 : ℝ))
      (E := (cell12850 ⟨11, by decide⟩).energy) (xi := (66017052037419 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12850 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12850]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12850])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12850) (a := (41845453829933 / 50000000000000 : ℝ)) (b := (160273419151 / 100000000000000 : ℝ)) (q := (2233465089739 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12850])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12850])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12850]

theorem cert12850_12 : CellCertificate 12850 (882547001325949 / 10000000000000000 : ℝ) (326915923546393 / 200000000000000000 : ℝ) (66017052037419 / 2000000000000000 : ℝ)
    (cell12850 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · have h := gap_lower (n := 12850) (a := (41828125903467 / 50000000000000 : ℝ)) (b := (160273419151 / 100000000000000 : ℝ)) (q := (1116734557207 / 50000000000000 : ℝ))
      (E := (cell12850 ⟨12, by decide⟩).energy) (xi := (66017052037419 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12850 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12850]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12850])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12850) (a := (41828125903467 / 50000000000000 : ℝ)) (b := (160273419151 / 100000000000000 : ℝ)) (q := (1116734557207 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12850])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12850])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12850]

theorem cert12850_13 : CellCertificate 12850 (882547001325949 / 10000000000000000 : ℝ) (326915923546393 / 200000000000000000 : ℝ) (66017052037419 / 2000000000000000 : ℝ)
    (cell12850 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · have h := gap_lower (n := 12850) (a := (41810810215731 / 50000000000000 : ℝ)) (b := (160273419151 / 100000000000000 : ℝ)) (q := (1116736562647 / 50000000000000 : ℝ))
      (E := (cell12850 ⟨13, by decide⟩).energy) (xi := (66017052037419 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12850 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12850]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12850])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12850) (a := (41810810215731 / 50000000000000 : ℝ)) (b := (160273419151 / 100000000000000 : ℝ)) (q := (1116736562647 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12850])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12850])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12850]

theorem cert12850_14 : CellCertificate 12850 (882547001325949 / 10000000000000000 : ℝ) (326915923546393 / 200000000000000000 : ℝ) (66017052037419 / 2000000000000000 : ℝ)
    (cell12850 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · have h := gap_lower (n := 12850) (a := (41793506749567 / 50000000000000 : ℝ)) (b := (160273419151 / 100000000000000 : ℝ)) (q := (2233477128099 / 100000000000000 : ℝ))
      (E := (cell12850 ⟨14, by decide⟩).energy) (xi := (66017052037419 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12850 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12850]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12850])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12850) (a := (41793506749567 / 50000000000000 : ℝ)) (b := (160273419151 / 100000000000000 : ℝ)) (q := (2233477128099 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12850])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12850])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12850]

theorem cert12850_15 : CellCertificate 12850 (882547001325949 / 10000000000000000 : ℝ) (326915923546393 / 200000000000000000 : ℝ) (66017052037419 / 2000000000000000 : ℝ)
    (cell12850 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · have h := gap_lower (n := 12850) (a := (83552430975811 / 100000000000000 : ℝ)) (b := (160273419151 / 100000000000000 : ℝ)) (q := (446696225661 / 20000000000000 : ℝ))
      (E := (cell12850 ⟨15, by decide⟩).energy) (xi := (66017052037419 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12850 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12850]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12850])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12850) (a := (83552430975811 / 100000000000000 : ℝ)) (b := (160273419151 / 100000000000000 : ℝ)) (q := (446696225661 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12850])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12850])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12850]

theorem cert12850_16 : CellCertificate 12850 (882547001325949 / 10000000000000000 : ℝ) (326915923546393 / 200000000000000000 : ℝ) (66017052037419 / 2000000000000000 : ℝ)
    (cell12850 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · have h := gap_lower (n := 12850) (a := (41758936413767 / 50000000000000 : ℝ)) (b := (160273419151 / 100000000000000 : ℝ)) (q := (279185641393 / 12500000000000 : ℝ))
      (E := (cell12850 ⟨16, by decide⟩).energy) (xi := (66017052037419 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12850 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12850]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12850])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12850) (a := (41758936413767 / 50000000000000 : ℝ)) (b := (160273419151 / 100000000000000 : ℝ)) (q := (279185641393 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12850])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12850])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12850]

theorem cert12850_17 : CellCertificate 12850 (882547001325949 / 10000000000000000 : ℝ) (326915923546393 / 200000000000000000 : ℝ) (66017052037419 / 2000000000000000 : ℝ)
    (cell12850 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · have h := gap_lower (n := 12850) (a := (20870834755129 / 25000000000000 : ℝ)) (b := (160273419151 / 100000000000000 : ℝ)) (q := (558372285401 / 25000000000000 : ℝ))
      (E := (cell12850 ⟨17, by decide⟩).energy) (xi := (66017052037419 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12850 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12850]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12850])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12850) (a := (20870834755129 / 25000000000000 : ℝ)) (b := (160273419151 / 100000000000000 : ℝ)) (q := (558372285401 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12850])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12850])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12850]

theorem cert12850_18 : CellCertificate 12850 (882547001325949 / 10000000000000000 : ℝ) (326915923546393 / 200000000000000000 : ℝ) (66017052037419 / 2000000000000000 : ℝ)
    (cell12850 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · have h := gap_lower (n := 12850) (a := (83448829521147 / 100000000000000 : ℝ)) (b := (160273419151 / 100000000000000 : ℝ)) (q := (1116746553093 / 50000000000000 : ℝ))
      (E := (cell12850 ⟨18, by decide⟩).energy) (xi := (66017052037419 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12850 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12850]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12850])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12850) (a := (83448829521147 / 100000000000000 : ℝ)) (b := (160273419151 / 100000000000000 : ℝ)) (q := (1116746553093 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12850])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12850])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12850]

theorem cert12850_19 : CellCertificate 12850 (882547001325949 / 10000000000000000 : ℝ) (326915923546393 / 200000000000000000 : ℝ) (66017052037419 / 2000000000000000 : ℝ)
    (cell12850 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · have h := gap_lower (n := 12850) (a := (83414344295991 / 100000000000000 : ℝ)) (b := (160273419151 / 100000000000000 : ℝ)) (q := (1116748572933 / 50000000000000 : ℝ))
      (E := (cell12850 ⟨19, by decide⟩).energy) (xi := (66017052037419 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12850 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12850]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12850])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12850) (a := (83414344295991 / 100000000000000 : ℝ)) (b := (160273419151 / 100000000000000 : ℝ)) (q := (1116748572933 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12850])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12850])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12850]

theorem cert12851_0 : CellCertificate 12851 (11031496114267 / 125000000000000 : ℝ) (163445238166167 / 100000000000000000 : ℝ) (13202358532691 / 400000000000000 : ℝ)
    (cell12851 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · have h := gap_lower (n := 12851) (a := (2627304149191 / 3125000000000 : ℝ)) (b := (160260799073 / 100000000000000 : ℝ)) (q := (17447679657 / 781250000000 : ℝ))
      (E := (cell12851 ⟨0, by decide⟩).energy) (xi := (13202358532691 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12851 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12851]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12851])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12851) (a := (2627304149191 / 3125000000000 : ℝ)) (b := (160260799073 / 100000000000000 : ℝ)) (q := (17447679657 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12851])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12851])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12851]

theorem cert12851_1 : CellCertificate 12851 (11031496114267 / 125000000000000 : ℝ) (163445238166167 / 100000000000000000 : ℝ) (13202358532691 / 400000000000000 : ℝ)
    (cell12851 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · have h := gap_lower (n := 12851) (a := (21009701416613 / 25000000000000 : ℝ)) (b := (160260799073 / 100000000000000 : ℝ)) (q := (89332280721 / 4000000000000 : ℝ))
      (E := (cell12851 ⟨1, by decide⟩).energy) (xi := (13202358532691 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12851 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12851]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12851])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12851) (a := (21009701416613 / 25000000000000 : ℝ)) (b := (160260799073 / 100000000000000 : ℝ)) (q := (89332280721 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12851])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12851])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12851]

theorem cert12851_2 : CellCertificate 12851 (11031496114267 / 125000000000000 : ℝ) (163445238166167 / 100000000000000000 : ℝ) (13202358532691 / 400000000000000 : ℝ)
    (cell12851 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · have h := gap_lower (n := 12851) (a := (672031227403 / 800000000000 : ℝ)) (b := (160260799073 / 100000000000000 : ℝ)) (q := (1116655502433 / 50000000000000 : ℝ))
      (E := (cell12851 ⟨2, by decide⟩).energy) (xi := (13202358532691 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12851 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12851]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12851])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12851) (a := (672031227403 / 800000000000 : ℝ)) (b := (160260799073 / 100000000000000 : ℝ)) (q := (1116655502433 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12851])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12851])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12851]

theorem cert12851_3 : CellCertificate 12851 (11031496114267 / 125000000000000 : ℝ) (163445238166167 / 100000000000000000 : ℝ) (13202358532691 / 400000000000000 : ℝ)
    (cell12851 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · have h := gap_lower (n := 12851) (a := (83969026014527 / 100000000000000 : ℝ)) (b := (160260799073 / 100000000000000 : ℝ)) (q := (1116657511537 / 50000000000000 : ℝ))
      (E := (cell12851 ⟨3, by decide⟩).energy) (xi := (13202358532691 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12851 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12851]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12851])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12851) (a := (83969026014527 / 100000000000000 : ℝ)) (b := (160260799073 / 100000000000000 : ℝ)) (q := (1116657511537 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12851])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12851])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12851]

theorem cert12851_4 : CellCertificate 12851 (11031496114267 / 125000000000000 : ℝ) (163445238166167 / 100000000000000000 : ℝ) (13202358532691 / 400000000000000 : ℝ)
    (cell12851 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · have h := gap_lower (n := 12851) (a := (83934173397749 / 100000000000000 : ℝ)) (b := (160260799073 / 100000000000000 : ℝ)) (q := (2233319023101 / 100000000000000 : ℝ))
      (E := (cell12851 ⟨4, by decide⟩).energy) (xi := (13202358532691 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12851 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12851]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12851])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12851) (a := (83934173397749 / 100000000000000 : ℝ)) (b := (160260799073 / 100000000000000 : ℝ)) (q := (2233319023101 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12851])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12851])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12851]

theorem cert12851_5 : CellCertificate 12851 (11031496114267 / 125000000000000 : ℝ) (163445238166167 / 100000000000000000 : ℝ) (13202358532691 / 400000000000000 : ℝ)
    (cell12851 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · have h := gap_lower (n := 12851) (a := (8389934553907 / 10000000000000 : ℝ)) (b := (160260799073 / 100000000000000 : ℝ)) (q := (17447836039 / 781250000000 : ℝ))
      (E := (cell12851 ⟨5, by decide⟩).energy) (xi := (13202358532691 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12851 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12851]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12851])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12851) (a := (8389934553907 / 10000000000000 : ℝ)) (b := (160260799073 / 100000000000000 : ℝ)) (q := (17447836039 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12851])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12851])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12851]

theorem cert12851_6 : CellCertificate 12851 (11031496114267 / 125000000000000 : ℝ) (163445238166167 / 100000000000000000 : ℝ) (13202358532691 / 400000000000000 : ℝ)
    (cell12851 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · have h := gap_lower (n := 12851) (a := (83864542402707 / 100000000000000 : ℝ)) (b := (160260799073 / 100000000000000 : ℝ)) (q := (2233327000537 / 100000000000000 : ℝ))
      (E := (cell12851 ⟨6, by decide⟩).energy) (xi := (13202358532691 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12851 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12851]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12851])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12851) (a := (83864542402707 / 100000000000000 : ℝ)) (b := (160260799073 / 100000000000000 : ℝ)) (q := (2233327000537 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12851])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12851])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12851]

theorem cert12851_7 : CellCertificate 12851 (11031496114267 / 125000000000000 : ℝ) (163445238166167 / 100000000000000000 : ℝ) (13202358532691 / 400000000000000 : ℝ)
    (cell12851 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · have h := gap_lower (n := 12851) (a := (41914881976533 / 50000000000000 : ℝ)) (b := (160260799073 / 100000000000000 : ℝ)) (q := (2233330993273 / 100000000000000 : ℝ))
      (E := (cell12851 ⟨7, by decide⟩).energy) (xi := (13202358532691 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12851 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12851]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12851])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12851) (a := (41914881976533 / 50000000000000 : ℝ)) (b := (160260799073 / 100000000000000 : ℝ)) (q := (2233330993273 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12851])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12851])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12851]

theorem cert12851_8 : CellCertificate 12851 (11031496114267 / 125000000000000 : ℝ) (163445238166167 / 100000000000000000 : ℝ) (13202358532691 / 400000000000000 : ℝ)
    (cell12851 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · have h := gap_lower (n := 12851) (a := (41897505077369 / 50000000000000 : ℝ)) (b := (160260799073 / 100000000000000 : ℝ)) (q := (558333749621 / 25000000000000 : ℝ))
      (E := (cell12851 ⟨8, by decide⟩).energy) (xi := (13202358532691 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12851 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12851]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12851])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12851) (a := (41897505077369 / 50000000000000 : ℝ)) (b := (160260799073 / 100000000000000 : ℝ)) (q := (558333749621 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12851])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12851])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12851]

theorem cert12851_9 : CellCertificate 12851 (11031496114267 / 125000000000000 : ℝ) (163445238166167 / 100000000000000000 : ℝ) (13202358532691 / 400000000000000 : ℝ)
    (cell12851 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · have h := gap_lower (n := 12851) (a := (41880140486251 / 50000000000000 : ℝ)) (b := (160260799073 / 100000000000000 : ℝ)) (q := (1116669511599 / 50000000000000 : ℝ))
      (E := (cell12851 ⟨9, by decide⟩).energy) (xi := (13202358532691 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12851 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12851]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12851])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12851) (a := (41880140486251 / 50000000000000 : ℝ)) (b := (160260799073 / 100000000000000 : ℝ)) (q := (1116669511599 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12851])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12851])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12851]

theorem cert12851_10 : CellCertificate 12851 (11031496114267 / 125000000000000 : ℝ) (163445238166167 / 100000000000000000 : ℝ) (13202358532691 / 400000000000000 : ℝ)
    (cell12851 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · have h := gap_lower (n := 12851) (a := (83725576371317 / 100000000000000 : ℝ)) (b := (160260799073 / 100000000000000 : ℝ)) (q := (2233343016139 / 100000000000000 : ℝ))
      (E := (cell12851 ⟨10, by decide⟩).energy) (xi := (13202358532691 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12851 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12851]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12851])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12851) (a := (83725576371317 / 100000000000000 : ℝ)) (b := (160260799073 / 100000000000000 : ℝ)) (q := (2233343016139 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12851])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12851])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12851]

theorem cert12851_11 : CellCertificate 12851 (11031496114267 / 125000000000000 : ℝ) (163445238166167 / 100000000000000000 : ℝ) (13202358532691 / 400000000000000 : ℝ)
    (cell12851 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · have h := gap_lower (n := 12851) (a := (10461362039541 / 12500000000000 : ℝ)) (b := (160260799073 / 100000000000000 : ℝ)) (q := (2233347041851 / 100000000000000 : ℝ))
      (E := (cell12851 ⟨11, by decide⟩).energy) (xi := (13202358532691 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12851 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12851]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12851])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12851) (a := (10461362039541 / 12500000000000 : ℝ)) (b := (160260799073 / 100000000000000 : ℝ)) (q := (2233347041851 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12851])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12851])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12851]

theorem cert12851_12 : CellCertificate 12851 (11031496114267 / 125000000000000 : ℝ) (163445238166167 / 100000000000000000 : ℝ) (13202358532691 / 400000000000000 : ℝ)
    (cell12851 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · have h := gap_lower (n := 12851) (a := (4182812038643 / 5000000000000 : ℝ)) (b := (160260799073 / 100000000000000 : ℝ)) (q := (223335104851 / 10000000000000 : ℝ))
      (E := (cell12851 ⟨12, by decide⟩).energy) (xi := (13202358532691 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12851 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12851]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12851])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12851) (a := (4182812038643 / 5000000000000 : ℝ)) (b := (160260799073 / 100000000000000 : ℝ)) (q := (223335104851 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12851])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12851])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12851]

theorem cert12851_13 : CellCertificate 12851 (11031496114267 / 125000000000000 : ℝ) (163445238166167 / 100000000000000000 : ℝ) (13202358532691 / 400000000000000 : ℝ)
    (cell12851 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · have h := gap_lower (n := 12851) (a := (41810804853209 / 50000000000000 : ℝ)) (b := (160260799073 / 100000000000000 : ℝ)) (q := (1116677521041 / 50000000000000 : ℝ))
      (E := (cell12851 ⟨13, by decide⟩).energy) (xi := (13202358532691 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12851 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12851]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12851])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12851) (a := (41810804853209 / 50000000000000 : ℝ)) (b := (160260799073 / 100000000000000 : ℝ)) (q := (1116677521041 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12851])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12851])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12851]

theorem cert12851_14 : CellCertificate 12851 (11031496114267 / 125000000000000 : ℝ) (163445238166167 / 100000000000000000 : ℝ) (13202358532691 / 400000000000000 : ℝ)
    (cell12851 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · have h := gap_lower (n := 12851) (a := (83587003082687 / 100000000000000 : ℝ)) (b := (160260799073 / 100000000000000 : ℝ)) (q := (34896234817 / 1562500000000 : ℝ))
      (E := (cell12851 ⟨14, by decide⟩).energy) (xi := (13202358532691 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12851 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12851]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12851])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12851) (a := (83587003082687 / 100000000000000 : ℝ)) (b := (160260799073 / 100000000000000 : ℝ)) (q := (34896234817 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12851])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12851])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12851]

theorem cert12851_15 : CellCertificate 12851 (11031496114267 / 125000000000000 : ℝ) (163445238166167 / 100000000000000000 : ℝ) (13202358532691 / 400000000000000 : ℝ)
    (cell12851 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · have h := gap_lower (n := 12851) (a := (8355242086753 / 10000000000000 : ℝ)) (b := (160260799073 / 100000000000000 : ℝ)) (q := (1116681535389 / 50000000000000 : ℝ))
      (E := (cell12851 ⟨15, by decide⟩).energy) (xi := (13202358532691 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12851 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12851]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12851])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12851) (a := (8355242086753 / 10000000000000 : ℝ)) (b := (160260799073 / 100000000000000 : ℝ)) (q := (1116681535389 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12851])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12851])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12851]

theorem cert12851_16 : CellCertificate 12851 (11031496114267 / 125000000000000 : ℝ) (163445238166167 / 100000000000000000 : ℝ) (13202358532691 / 400000000000000 : ℝ)
    (cell12851 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · have h := gap_lower (n := 12851) (a := (83517863026987 / 100000000000000 : ℝ)) (b := (160260799073 / 100000000000000 : ℝ)) (q := (1116683529227 / 50000000000000 : ℝ))
      (E := (cell12851 ⟨16, by decide⟩).energy) (xi := (13202358532691 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12851 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12851]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12851])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12851) (a := (83517863026987 / 100000000000000 : ℝ)) (b := (160260799073 / 100000000000000 : ℝ)) (q := (1116683529227 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12851])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12851])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12851]

theorem cert12851_17 : CellCertificate 12851 (11031496114267 / 125000000000000 : ℝ) (163445238166167 / 100000000000000000 : ℝ) (13202358532691 / 400000000000000 : ℝ)
    (cell12851 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · have h := gap_lower (n := 12851) (a := (3339333181091 / 4000000000000 : ℝ)) (b := (160260799073 / 100000000000000 : ℝ)) (q := (446674210891 / 20000000000000 : ℝ))
      (E := (cell12851 ⟨17, by decide⟩).energy) (xi := (13202358532691 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12851 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12851]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12851])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12851) (a := (3339333181091 / 4000000000000 : ℝ)) (b := (160260799073 / 100000000000000 : ℝ)) (q := (446674210891 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12851])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12851])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12851]

theorem cert12851_18 : CellCertificate 12851 (11031496114267 / 125000000000000 : ℝ) (163445238166167 / 100000000000000000 : ℝ) (13202358532691 / 400000000000000 : ℝ)
    (cell12851 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · have h := gap_lower (n := 12851) (a := (41724410167391 / 50000000000000 : ℝ)) (b := (160260799073 / 100000000000000 : ℝ)) (q := (223337506353 / 10000000000000 : ℝ))
      (E := (cell12851 ⟨18, by decide⟩).energy) (xi := (13202358532691 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12851 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12851]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12851])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12851) (a := (41724410167391 / 50000000000000 : ℝ)) (b := (160260799073 / 100000000000000 : ℝ)) (q := (223337506353 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12851])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12851])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12851]

theorem cert12851_19 : CellCertificate 12851 (11031496114267 / 125000000000000 : ℝ) (163445238166167 / 100000000000000000 : ℝ) (13202358532691 / 400000000000000 : ℝ)
    (cell12851 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · have h := gap_lower (n := 12851) (a := (83414335416073 / 100000000000000 : ℝ)) (b := (160260799073 / 100000000000000 : ℝ)) (q := (2233379031913 / 100000000000000 : ℝ))
      (E := (cell12851 ⟨19, by decide⟩).energy) (xi := (13202358532691 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12851 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12851]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12851])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12851) (a := (83414335416073 / 100000000000000 : ℝ)) (b := (160260799073 / 100000000000000 : ℝ)) (q := (2233379031913 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12851])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12851])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12851]

theorem cert12852_0 : CellCertificate 12852 (441246190516477 / 5000000000000000 : ℝ) (1634325165398003 / 1000000000000000000 : ℝ) (330032670683247 / 10000000000000000 : ℝ)
    (cell12852 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · have h := gap_lower (n := 12852) (a := (16814743599979 / 20000000000000 : ℝ)) (b := (80124090497 / 50000000000000 : ℝ)) (q := (2233184957563 / 100000000000000 : ℝ))
      (E := (cell12852 ⟨0, by decide⟩).energy) (xi := (330032670683247 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12852 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12852]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12852])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12852) (a := (16814743599979 / 20000000000000 : ℝ)) (b := (80124090497 / 50000000000000 : ℝ)) (q := (2233184957563 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12852])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12852])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12852]

theorem cert12852_1 : CellCertificate 12852 (441246190516477 / 5000000000000000 : ℝ) (1634325165398003 / 1000000000000000000 : ℝ) (330032670683247 / 10000000000000000 : ℝ)
    (cell12852 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · have h := gap_lower (n := 12852) (a := (21009697801623 / 25000000000000 : ℝ)) (b := (80124090497 / 50000000000000 : ℝ)) (q := (2233188953567 / 100000000000000 : ℝ))
      (E := (cell12852 ⟨1, by decide⟩).energy) (xi := (330032670683247 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12852 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12852]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12852])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12852) (a := (21009697801623 / 25000000000000 : ℝ)) (b := (80124090497 / 50000000000000 : ℝ)) (q := (2233188953567 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12852])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12852])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12852]

theorem cert12852_2 : CellCertificate 12852 (441246190516477 / 5000000000000000 : ℝ) (1634325165398003 / 1000000000000000000 : ℝ) (330032670683247 / 10000000000000000 : ℝ)
    (cell12852 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · have h := gap_lower (n := 12852) (a := (84003889279227 / 100000000000000 : ℝ)) (b := (80124090497 / 50000000000000 : ℝ)) (q := (1116596486537 / 50000000000000 : ℝ))
      (E := (cell12852 ⟨2, by decide⟩).energy) (xi := (330032670683247 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12852 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12852]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12852])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12852) (a := (84003889279227 / 100000000000000 : ℝ)) (b := (80124090497 / 50000000000000 : ℝ)) (q := (1116596486537 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12852])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12852])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12852]

theorem cert12852_3 : CellCertificate 12852 (441246190516477 / 5000000000000000 : ℝ) (1634325165398003 / 1000000000000000000 : ℝ) (330032670683247 / 10000000000000000 : ℝ)
    (cell12852 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · have h := gap_lower (n := 12852) (a := (335876048727 / 400000000000 : ℝ)) (b := (80124090497 / 50000000000000 : ℝ)) (q := (446639393363 / 20000000000000 : ℝ))
      (E := (cell12852 ⟨3, by decide⟩).energy) (xi := (330032670683247 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12852 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12852]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12852])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12852) (a := (335876048727 / 400000000000 : ℝ)) (b := (80124090497 / 50000000000000 : ℝ)) (q := (446639393363 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12852])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12852])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12852]

theorem cert12852_4 : CellCertificate 12852 (441246190516477 / 5000000000000000 : ℝ) (1634325165398003 / 1000000000000000000 : ℝ) (330032670683247 / 10000000000000000 : ℝ)
    (cell12852 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · have h := gap_lower (n := 12852) (a := (839341598779 / 1000000000000 : ℝ)) (b := (80124090497 / 50000000000000 : ℝ)) (q := (2233200943093 / 100000000000000 : ℝ))
      (E := (cell12852 ⟨4, by decide⟩).energy) (xi := (330032670683247 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12852 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12852]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12852])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12852) (a := (839341598779 / 1000000000000 : ℝ)) (b := (80124090497 / 50000000000000 : ℝ)) (q := (2233200943093 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12852])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12852])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12852]

theorem cert12852_5 : CellCertificate 12852 (441246190516477 / 5000000000000000 : ℝ) (1634325165398003 / 1000000000000000000 : ℝ) (330032670683247 / 10000000000000000 : ℝ)
    (cell12852 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · have h := gap_lower (n := 12852) (a := (83899332331707 / 100000000000000 : ℝ)) (b := (80124090497 / 50000000000000 : ℝ)) (q := (1116602483947 / 50000000000000 : ℝ))
      (E := (cell12852 ⟨5, by decide⟩).energy) (xi := (330032670683247 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12852 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12852]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12852])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12852) (a := (83899332331707 / 100000000000000 : ℝ)) (b := (80124090497 / 50000000000000 : ℝ)) (q := (1116602483947 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12852])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12852])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12852]

theorem cert12852_6 : CellCertificate 12852 (441246190516477 / 5000000000000000 : ℝ) (1634325165398003 / 1000000000000000000 : ℝ) (330032670683247 / 10000000000000000 : ℝ)
    (cell12852 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · have h := gap_lower (n := 12852) (a := (83864529507391 / 100000000000000 : ℝ)) (b := (80124090497 / 50000000000000 : ℝ)) (q := (223320899111 / 10000000000000 : ℝ))
      (E := (cell12852 ⟨6, by decide⟩).energy) (xi := (330032670683247 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12852 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12852]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12852])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12852) (a := (83864529507391 / 100000000000000 : ℝ)) (b := (80124090497 / 50000000000000 : ℝ)) (q := (223320899111 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12852])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12852])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12852]

theorem cert12852_7 : CellCertificate 12852 (441246190516477 / 5000000000000000 : ℝ) (1634325165398003 / 1000000000000000000 : ℝ) (330032670683247 / 10000000000000000 : ℝ)
    (cell12852 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · have h := gap_lower (n := 12852) (a := (41914875684679 / 50000000000000 : ℝ)) (b := (80124090497 / 50000000000000 : ℝ)) (q := (139575810143 / 6250000000000 : ℝ))
      (E := (cell12852 ⟨7, by decide⟩).energy) (xi := (330032670683247 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12852 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12852]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12852])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12852) (a := (41914875684679 / 50000000000000 : ℝ)) (b := (80124090497 / 50000000000000 : ℝ)) (q := (139575810143 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12852])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12852])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12852]

theorem cert12852_8 : CellCertificate 12852 (441246190516477 / 5000000000000000 : ℝ) (1634325165398003 / 1000000000000000000 : ℝ) (330032670683247 / 10000000000000000 : ℝ)
    (cell12852 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · have h := gap_lower (n := 12852) (a := (418974989411 / 500000000000 : ℝ)) (b := (80124090497 / 50000000000000 : ℝ)) (q := (1116608502333 / 50000000000000 : ℝ))
      (E := (cell12852 ⟨8, by decide⟩).energy) (xi := (330032670683247 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12852 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12852]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12852])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12852) (a := (418974989411 / 500000000000 : ℝ)) (b := (80124090497 / 50000000000000 : ℝ)) (q := (1116608502333 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12852])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12852])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12852]

theorem cert12852_9 : CellCertificate 12852 (441246190516477 / 5000000000000000 : ℝ) (1634325165398003 / 1000000000000000000 : ℝ) (330032670683247 / 10000000000000000 : ℝ)
    (cell12852 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · have h := gap_lower (n := 12852) (a := (10470033626337 / 12500000000000 : ℝ)) (b := (80124090497 / 50000000000000 : ℝ)) (q := (279152626159 / 12500000000000 : ℝ))
      (E := (cell12852 ⟨9, by decide⟩).energy) (xi := (330032670683247 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12852 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12852]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12852])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12852) (a := (10470033626337 / 12500000000000 : ℝ)) (b := (80124090497 / 50000000000000 : ℝ)) (q := (279152626159 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12852])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12852])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12852]

theorem cert12852_10 : CellCertificate 12852 (441246190516477 / 5000000000000000 : ℝ) (1634325165398003 / 1000000000000000000 : ℝ) (330032670683247 / 10000000000000000 : ℝ)
    (cell12852 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · have h := gap_lower (n := 12852) (a := (1308211948747 / 1562500000000 : ℝ)) (b := (80124090497 / 50000000000000 : ℝ)) (q := (446644996563 / 20000000000000 : ℝ))
      (E := (cell12852 ⟨10, by decide⟩).energy) (xi := (330032670683247 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12852 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12852]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12852])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12852) (a := (1308211948747 / 1562500000000 : ℝ)) (b := (80124090497 / 50000000000000 : ℝ)) (q := (446644996563 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12852])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12852])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12852]

theorem cert12852_11 : CellCertificate 12852 (441246190516477 / 5000000000000000 : ℝ) (1634325165398003 / 1000000000000000000 : ℝ) (330032670683247 / 10000000000000000 : ℝ)
    (cell12852 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · have h := gap_lower (n := 12852) (a := (2092272124367 / 2500000000000 : ℝ)) (b := (80124090497 / 50000000000000 : ℝ)) (q := (2233228989839 / 100000000000000 : ℝ))
      (E := (cell12852 ⟨11, by decide⟩).energy) (xi := (330032670683247 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12852 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12852]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12852])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12852) (a := (2092272124367 / 2500000000000 : ℝ)) (b := (80124090497 / 50000000000000 : ℝ)) (q := (2233228989839 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12852])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12852])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12852]

theorem cert12852_12 : CellCertificate 12852 (441246190516477 / 5000000000000000 : ℝ) (1634325165398003 / 1000000000000000000 : ℝ) (330032670683247 / 10000000000000000 : ℝ)
    (cell12852 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · have h := gap_lower (n := 12852) (a := (41828114870319 / 50000000000000 : ℝ)) (b := (80124090497 / 50000000000000 : ℝ)) (q := (2233232978521 / 100000000000000 : ℝ))
      (E := (cell12852 ⟨12, by decide⟩).energy) (xi := (330032670683247 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12852 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12852]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12852])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12852) (a := (41828114870319 / 50000000000000 : ℝ)) (b := (80124090497 / 50000000000000 : ℝ)) (q := (2233232978521 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12852])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12852])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12852]

theorem cert12852_13 : CellCertificate 12852 (441246190516477 / 5000000000000000 : ℝ) (1634325165398003 / 1000000000000000000 : ℝ) (330032670683247 / 10000000000000000 : ℝ)
    (cell12852 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · have h := gap_lower (n := 12852) (a := (83621598983189 / 100000000000000 : ℝ)) (b := (80124090497 / 50000000000000 : ℝ)) (q := (1116618506477 / 50000000000000 : ℝ))
      (E := (cell12852 ⟨13, by decide⟩).energy) (xi := (330032670683247 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12852 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12852]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12852])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12852) (a := (83621598983189 / 100000000000000 : ℝ)) (b := (80124090497 / 50000000000000 : ℝ)) (q := (1116618506477 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12852])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12852])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12852]

theorem cert12852_14 : CellCertificate 12852 (441246190516477 / 5000000000000000 : ℝ) (1634325165398003 / 1000000000000000000 : ℝ) (330032670683247 / 10000000000000000 : ℝ)
    (cell12852 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · have h := gap_lower (n := 12852) (a := (41793496334009 / 50000000000000 : ℝ)) (b := (80124090497 / 50000000000000 : ℝ)) (q := (1116620491311 / 50000000000000 : ℝ))
      (E := (cell12852 ⟨14, by decide⟩).energy) (xi := (330032670683247 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12852 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12852]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12852])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12852) (a := (41793496334009 / 50000000000000 : ℝ)) (b := (80124090497 / 50000000000000 : ℝ)) (q := (1116620491311 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12852])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12852])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12852]

theorem cert12852_15 : CellCertificate 12852 (441246190516477 / 5000000000000000 : ℝ) (1634325165398003 / 1000000000000000000 : ℝ) (330032670683247 / 10000000000000000 : ℝ)
    (cell12852 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · have h := gap_lower (n := 12852) (a := (83552410760991 / 100000000000000 : ℝ)) (b := (80124090497 / 50000000000000 : ℝ)) (q := (2233245009279 / 100000000000000 : ℝ))
      (E := (cell12852 ⟨15, by decide⟩).energy) (xi := (330032670683247 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12852 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12852]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12852])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12852) (a := (83552410760991 / 100000000000000 : ℝ)) (b := (80124090497 / 50000000000000 : ℝ)) (q := (2233245009279 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12852])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12852])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12852]

theorem cert12852_16 : CellCertificate 12852 (441246190516477 / 5000000000000000 : ℝ) (1634325165398003 / 1000000000000000000 : ℝ) (330032670683247 / 10000000000000000 : ℝ)
    (cell12852 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · have h := gap_lower (n := 12852) (a := (41758926614073 / 50000000000000 : ℝ)) (b := (80124090497 / 50000000000000 : ℝ)) (q := (2233248981829 / 100000000000000 : ℝ))
      (E := (cell12852 ⟨16, by decide⟩).energy) (xi := (330032670683247 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12852 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12852]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12852])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12852) (a := (41758926614073 / 50000000000000 : ℝ)) (b := (80124090497 / 50000000000000 : ℝ)) (q := (2233248981829 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12852])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12852])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12852]

theorem cert12852_17 : CellCertificate 12852 (441246190516477 / 5000000000000000 : ℝ) (1634325165398003 / 1000000000000000000 : ℝ) (330032670683247 / 10000000000000000 : ℝ)
    (cell12852 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · have h := gap_lower (n := 12852) (a := (83483320035701 / 100000000000000 : ℝ)) (b := (80124090497 / 50000000000000 : ℝ)) (q := (1116626510817 / 50000000000000 : ℝ))
      (E := (cell12852 ⟨17, by decide⟩).energy) (xi := (330032670683247 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12852 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12852]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12852])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12852) (a := (83483320035701 / 100000000000000 : ℝ)) (b := (80124090497 / 50000000000000 : ℝ)) (q := (1116626510817 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12852])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12852])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12852]

theorem cert12852_18 : CellCertificate 12852 (441246190516477 / 5000000000000000 : ℝ) (1634325165398003 / 1000000000000000000 : ℝ) (330032670683247 / 10000000000000000 : ℝ)
    (cell12852 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · have h := gap_lower (n := 12852) (a := (83448811150047 / 100000000000000 : ℝ)) (b := (80124090497 / 50000000000000 : ℝ)) (q := (279157127127 / 12500000000000 : ℝ))
      (E := (cell12852 ⟨18, by decide⟩).energy) (xi := (330032670683247 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12852 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12852]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12852])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12852) (a := (83448811150047 / 100000000000000 : ℝ)) (b := (80124090497 / 50000000000000 : ℝ)) (q := (279157127127 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12852])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12852])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12852]

theorem cert12852_19 : CellCertificate 12852 (441246190516477 / 5000000000000000 : ℝ) (1634325165398003 / 1000000000000000000 : ℝ) (330032670683247 / 10000000000000000 : ℝ)
    (cell12852 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · have h := gap_lower (n := 12852) (a := (83414326537749 / 100000000000000 : ℝ)) (b := (80124090497 / 50000000000000 : ℝ)) (q := (55831525767 / 2500000000000 : ℝ))
      (E := (cell12852 ⟨19, by decide⟩).energy) (xi := (330032670683247 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12852 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12852]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12852])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12852) (a := (83414326537749 / 100000000000000 : ℝ)) (b := (80124090497 / 50000000000000 : ℝ)) (q := (55831525767 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12852])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12852])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12852]

theorem cert12853_0 : CellCertificate 12853 (882465076999773 / 10000000000000000 : ℝ) (1634197968936341 / 1000000000000000000 : ℝ) (41250797785489 / 1250000000000000 : ℝ)
    (cell12853 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · have h := gap_lower (n := 12853) (a := (84073703227979 / 100000000000000 : ℝ)) (b := (10014722807 / 6250000000000 : ℝ)) (q := (1116533486157 / 50000000000000 : ℝ))
      (E := (cell12853 ⟨0, by decide⟩).energy) (xi := (41250797785489 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12853 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12853]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12853])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12853) (a := (84073703227979 / 100000000000000 : ℝ)) (b := (10014722807 / 6250000000000 : ℝ)) (q := (1116533486157 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12853])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12853])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12853]

theorem cert12853_1 : CellCertificate 12853 (882465076999773 / 10000000000000000 : ℝ) (1634197968936341 / 1000000000000000000 : ℝ) (41250797785489 / 1250000000000000 : ℝ)
    (cell12853 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · have h := gap_lower (n := 12853) (a := (16807755349759 / 20000000000000 : ℝ)) (b := (10014722807 / 6250000000000 : ℝ)) (q := (1116535471227 / 50000000000000 : ℝ))
      (E := (cell12853 ⟨1, by decide⟩).energy) (xi := (41250797785489 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12853 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12853]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12853])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12853) (a := (16807755349759 / 20000000000000 : ℝ)) (b := (10014722807 / 6250000000000 : ℝ)) (q := (1116535471227 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12853])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12853])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12853]

theorem cert12853_2 : CellCertificate 12853 (882465076999773 / 10000000000000000 : ℝ) (1634197968936341 / 1000000000000000000 : ℝ) (41250797785489 / 1250000000000000 : ℝ)
    (cell12853 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · have h := gap_lower (n := 12853) (a := (42001937567653 / 50000000000000 : ℝ)) (b := (10014722807 / 6250000000000 : ℝ)) (q := (446614987363 / 20000000000000 : ℝ))
      (E := (cell12853 ⟨2, by decide⟩).energy) (xi := (41250797785489 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12853 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12853]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12853])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12853) (a := (42001937567653 / 50000000000000 : ℝ)) (b := (10014722807 / 6250000000000 : ℝ)) (q := (446614987363 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12853])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12853])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12853]

theorem cert12853_3 : CellCertificate 12853 (882465076999773 / 10000000000000000 : ℝ) (1634197968936341 / 1000000000000000000 : ℝ) (41250797785489 / 1250000000000000 : ℝ)
    (cell12853 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · have h := gap_lower (n := 12853) (a := (83968998351161 / 100000000000000 : ℝ)) (b := (10014722807 / 6250000000000 : ℝ)) (q := (89323158561 / 4000000000000 : ℝ))
      (E := (cell12853 ⟨3, by decide⟩).energy) (xi := (41250797785489 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12853 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12853]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12853])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12853) (a := (83968998351161 / 100000000000000 : ℝ)) (b := (10014722807 / 6250000000000 : ℝ)) (q := (89323158561 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12853])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12853])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12853]

theorem cert12853_4 : CellCertificate 12853 (882465076999773 / 10000000000000000 : ℝ) (1634197968936341 / 1000000000000000000 : ℝ) (41250797785489 / 1250000000000000 : ℝ)
    (cell12853 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · have h := gap_lower (n := 12853) (a := (83934146360201 / 100000000000000 : ℝ)) (b := (10014722807 / 6250000000000 : ℝ)) (q := (446616594907 / 20000000000000 : ℝ))
      (E := (cell12853 ⟨4, by decide⟩).energy) (xi := (41250797785489 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12853 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12853]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12853])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12853) (a := (83934146360201 / 100000000000000 : ℝ)) (b := (10014722807 / 6250000000000 : ℝ)) (q := (446616594907 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12853])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12853])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12853]

theorem cert12853_5 : CellCertificate 12853 (882465076999773 / 10000000000000000 : ℝ) (1634197968936341 / 1000000000000000000 : ℝ) (41250797785489 / 1250000000000000 : ℝ)
    (cell12853 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · have h := gap_lower (n := 12853) (a := (41949659563229 / 50000000000000 : ℝ)) (b := (10014722807 / 6250000000000 : ℝ)) (q := (2233086976387 / 100000000000000 : ℝ))
      (E := (cell12853 ⟨5, by decide⟩).energy) (xi := (41250797785489 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12853 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12853]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12853])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12853) (a := (41949659563229 / 50000000000000 : ℝ)) (b := (10014722807 / 6250000000000 : ℝ)) (q := (2233086976387 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12853])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12853])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12853]

theorem cert12853_6 : CellCertificate 12853 (882465076999773 / 10000000000000000 : ℝ) (1634197968936341 / 1000000000000000000 : ℝ) (41250797785489 / 1250000000000000 : ℝ)
    (cell12853 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · have h := gap_lower (n := 12853) (a := (83864516614151 / 100000000000000 : ℝ)) (b := (10014722807 / 6250000000000 : ℝ)) (q := (2233090977371 / 100000000000000 : ℝ))
      (E := (cell12853 ⟨6, by decide⟩).energy) (xi := (41250797785489 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12853 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12853]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12853])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12853) (a := (83864516614151 / 100000000000000 : ℝ)) (b := (10014722807 / 6250000000000 : ℝ)) (q := (2233090977371 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12853])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12853])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12853]

theorem cert12853_7 : CellCertificate 12853 (882465076999773 / 10000000000000000 : ℝ) (1634197968936341 / 1000000000000000000 : ℝ) (41250797785489 / 1250000000000000 : ℝ)
    (cell12853 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · have h := gap_lower (n := 12853) (a := (83829738787689 / 100000000000000 : ℝ)) (b := (10014722807 / 6250000000000 : ℝ)) (q := (1116547492509 / 50000000000000 : ℝ))
      (E := (cell12853 ⟨7, by decide⟩).energy) (xi := (41250797785489 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12853 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12853]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12853])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12853) (a := (83829738787689 / 100000000000000 : ℝ)) (b := (10014722807 / 6250000000000 : ℝ)) (q := (1116547492509 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12853])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12853])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12853]

theorem cert12853_8 : CellCertificate 12853 (882465076999773 / 10000000000000000 : ℝ) (1634197968936341 / 1000000000000000000 : ℝ) (41250797785489 / 1250000000000000 : ℝ)
    (cell12853 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · have h := gap_lower (n := 12853) (a := (83794985611663 / 100000000000000 : ℝ)) (b := (10014722807 / 6250000000000 : ℝ)) (q := (1116549474301 / 50000000000000 : ℝ))
      (E := (cell12853 ⟨8, by decide⟩).energy) (xi := (41250797785489 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12853 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12853]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12853])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12853) (a := (83794985611663 / 100000000000000 : ℝ)) (b := (10014722807 / 6250000000000 : ℝ)) (q := (1116549474301 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12853])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12853])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12853]

theorem cert12853_9 : CellCertificate 12853 (882465076999773 / 10000000000000000 : ℝ) (1634197968936341 / 1000000000000000000 : ℝ) (41250797785489 / 1250000000000000 : ℝ)
    (cell12853 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · have h := gap_lower (n := 12853) (a := (16752051410171 / 20000000000000 : ℝ)) (b := (10014722807 / 6250000000000 : ℝ)) (q := (558275747787 / 25000000000000 : ℝ))
      (E := (cell12853 ⟨9, by decide⟩).energy) (xi := (41250797785489 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12853 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12853]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12853])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12853) (a := (16752051410171 / 20000000000000 : ℝ)) (b := (10014722807 / 6250000000000 : ℝ)) (q := (558275747787 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12853])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12853])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12853]

theorem cert12853_10 : CellCertificate 12853 (882465076999773 / 10000000000000000 : ℝ) (1634197968936341 / 1000000000000000000 : ℝ) (41250797785489 / 1250000000000000 : ℝ)
    (cell12853 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · have h := gap_lower (n := 12853) (a := (3349022122809 / 4000000000000 : ℝ)) (b := (10014722807 / 6250000000000 : ℝ)) (q := (2233106945333 / 100000000000000 : ℝ))
      (E := (cell12853 ⟨10, by decide⟩).energy) (xi := (41250797785489 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12853 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12853]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12853])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12853) (a := (3349022122809 / 4000000000000 : ℝ)) (b := (10014722807 / 6250000000000 : ℝ)) (q := (2233106945333 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12853])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12853])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12853]

theorem cert12853_11 : CellCertificate 12853 (882465076999773 / 10000000000000000 : ℝ) (1634197968936341 / 1000000000000000000 : ℝ) (41250797785489 / 1250000000000000 : ℝ)
    (cell12853 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · have h := gap_lower (n := 12853) (a := (83690873634921 / 100000000000000 : ℝ)) (b := (10014722807 / 6250000000000 : ℝ)) (q := (223311099179 / 10000000000000 : ℝ))
      (E := (cell12853 ⟨11, by decide⟩).energy) (xi := (41250797785489 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12853 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12853]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12853])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12853) (a := (83690873634921 / 100000000000000 : ℝ)) (b := (10014722807 / 6250000000000 : ℝ)) (q := (223311099179 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12853])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12853])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12853]

theorem cert12853_12 : CellCertificate 12853 (882465076999773 / 10000000000000000 : ℝ) (1634197968936341 / 1000000000000000000 : ℝ) (41250797785489 / 1250000000000000 : ℝ)
    (cell12853 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · have h := gap_lower (n := 12853) (a := (20914054677567 / 25000000000000 : ℝ)) (b := (10014722807 / 6250000000000 : ℝ)) (q := (558278740639 / 25000000000000 : ℝ))
      (E := (cell12853 ⟨12, by decide⟩).energy) (xi := (41250797785489 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12853 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12853]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12853])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12853) (a := (20914054677567 / 25000000000000 : ℝ)) (b := (10014722807 / 6250000000000 : ℝ)) (q := (558278740639 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12853])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12853])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12853]

theorem cert12853_13 : CellCertificate 12853 (882465076999773 / 10000000000000000 : ℝ) (1634197968936341 / 1000000000000000000 : ℝ) (41250797785489 / 1250000000000000 : ℝ)
    (cell12853 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · have h := gap_lower (n := 12853) (a := (3344863530471 / 4000000000000 : ℝ)) (b := (10014722807 / 6250000000000 : ℝ)) (q := (2233118979781 / 100000000000000 : ℝ))
      (E := (cell12853 ⟨13, by decide⟩).energy) (xi := (41250797785489 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12853 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12853]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12853])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12853) (a := (3344863530471 / 4000000000000 : ℝ)) (b := (10014722807 / 6250000000000 : ℝ)) (q := (2233118979781 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12853])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12853])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12853]

theorem cert12853_14 : CellCertificate 12853 (882465076999773 / 10000000000000000 : ℝ) (1634197968936341 / 1000000000000000000 : ℝ) (41250797785489 / 1250000000000000 : ℝ)
    (cell12853 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · have h := gap_lower (n := 12853) (a := (10448372781891 / 12500000000000 : ℝ)) (b := (10014722807 / 6250000000000 : ℝ)) (q := (2233122991101 / 100000000000000 : ℝ))
      (E := (cell12853 ⟨14, by decide⟩).energy) (xi := (41250797785489 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12853 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12853]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12853])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12853) (a := (10448372781891 / 12500000000000 : ℝ)) (b := (10014722807 / 6250000000000 : ℝ)) (q := (2233122991101 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12853])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12853])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12853]

theorem cert12853_15 : CellCertificate 12853 (882465076999773 / 10000000000000000 : ℝ) (1634197968936341 / 1000000000000000000 : ℝ) (41250797785489 / 1250000000000000 : ℝ)
    (cell12853 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · have h := gap_lower (n := 12853) (a := (1305506260253 / 1562500000000 : ℝ)) (b := (10014722807 / 6250000000000 : ℝ)) (q := (2233127001989 / 100000000000000 : ℝ))
      (E := (cell12853 ⟨15, by decide⟩).energy) (xi := (41250797785489 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12853 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12853]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12853])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12853) (a := (1305506260253 / 1562500000000 : ℝ)) (b := (10014722807 / 6250000000000 : ℝ)) (q := (2233127001989 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12853])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12853])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12853]

theorem cert12853_16 : CellCertificate 12853 (882465076999773 / 10000000000000000 : ℝ) (1634197968936341 / 1000000000000000000 : ℝ) (41250797785489 / 1250000000000000 : ℝ)
    (cell12853 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · have h := gap_lower (n := 12853) (a := (83517843431009 / 100000000000000 : ℝ)) (b := (10014722807 / 6250000000000 : ℝ)) (q := (2233131017673 / 100000000000000 : ℝ))
      (E := (cell12853 ⟨16, by decide⟩).energy) (xi := (41250797785489 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12853 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12853]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12853])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12853) (a := (83517843431009 / 100000000000000 : ℝ)) (b := (10014722807 / 6250000000000 : ℝ)) (q := (2233131017673 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12853])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12853])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12853]

theorem cert12853_17 : CellCertificate 12853 (882465076999773 / 10000000000000000 : ℝ) (1634197968936341 / 1000000000000000000 : ℝ) (41250797785489 / 1250000000000000 : ℝ)
    (cell12853 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · have h := gap_lower (n := 12853) (a := (16696662109159 / 20000000000000 : ℝ)) (b := (10014722807 / 6250000000000 : ℝ)) (q := (2233134984919 / 100000000000000 : ℝ))
      (E := (cell12853 ⟨17, by decide⟩).energy) (xi := (41250797785489 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12853 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12853]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12853])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12853) (a := (16696662109159 / 20000000000000 : ℝ)) (b := (10014722807 / 6250000000000 : ℝ)) (q := (2233134984919 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12853])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12853])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12853]

theorem cert12853_18 : CellCertificate 12853 (882465076999773 / 10000000000000000 : ℝ) (1634197968936341 / 1000000000000000000 : ℝ) (41250797785489 / 1250000000000000 : ℝ)
    (cell12853 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · have h := gap_lower (n := 12853) (a := (83448801966943 / 100000000000000 : ℝ)) (b := (10014722807 / 6250000000000 : ℝ)) (q := (2233139024893 / 100000000000000 : ℝ))
      (E := (cell12853 ⟨18, by decide⟩).energy) (xi := (41250797785489 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12853 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12853]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12853])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12853) (a := (83448801966943 / 100000000000000 : ℝ)) (b := (10014722807 / 6250000000000 : ℝ)) (q := (2233139024893 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12853])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12853])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12853]

theorem cert12853_19 : CellCertificate 12853 (882465076999773 / 10000000000000000 : ℝ) (1634197968936341 / 1000000000000000000 : ℝ) (41250797785489 / 1250000000000000 : ℝ)
    (cell12853 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · have h := gap_lower (n := 12853) (a := (83414317661019 / 100000000000000 : ℝ)) (b := (10014722807 / 6250000000000 : ℝ)) (q := (2233143025629 / 100000000000000 : ℝ))
      (E := (cell12853 ⟨19, by decide⟩).energy) (xi := (41250797785489 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12853 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12853]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12853])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12853) (a := (83414317661019 / 100000000000000 : ℝ)) (b := (10014722807 / 6250000000000 : ℝ)) (q := (2233143025629 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12853])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12853])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12853]

theorem cert12854_0 : CellCertificate 12854 (441218888520431 / 5000000000000000 : ℝ) (81703539613603 / 50000000000000000 : ℝ) (82495024529543 / 2500000000000000 : ℝ)
    (cell12854 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · have h := gap_lower (n := 12854) (a := (16814737691673 / 20000000000000 : ℝ)) (b := (160222950829 / 100000000000000 : ℝ)) (q := (2232948982519 / 100000000000000 : ℝ))
      (E := (cell12854 ⟨0, by decide⟩).energy) (xi := (82495024529543 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12854 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12854]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12854])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12854) (a := (16814737691673 / 20000000000000 : ℝ)) (b := (160222950829 / 100000000000000 : ℝ)) (q := (2232948982519 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12854])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12854])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12854]

theorem cert12854_1 : CellCertificate 12854 (441218888520431 / 5000000000000000 : ℝ) (81703539613603 / 50000000000000000 : ℝ) (82495024529543 / 2500000000000000 : ℝ)
    (cell12854 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · have h := gap_lower (n := 12854) (a := (42019381146681 / 50000000000000 : ℝ)) (b := (160222950829 / 100000000000000 : ℝ)) (q := (2232952984683 / 100000000000000 : ℝ))
      (E := (cell12854 ⟨1, by decide⟩).energy) (xi := (82495024529543 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12854 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12854]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12854])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12854) (a := (42019381146681 / 50000000000000 : ℝ)) (b := (160222950829 / 100000000000000 : ℝ)) (q := (2232952984683 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12854])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12854])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12854]

theorem cert12854_2 : CellCertificate 12854 (441218888520431 / 5000000000000000 : ℝ) (81703539613603 / 50000000000000000 : ℝ) (82495024529543 / 2500000000000000 : ℝ)
    (cell12854 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · have h := gap_lower (n := 12854) (a := (8400386099361 / 10000000000000 : ℝ)) (b := (160222950829 / 100000000000000 : ℝ)) (q := (1116478476981 / 50000000000000 : ℝ))
      (E := (cell12854 ⟨2, by decide⟩).energy) (xi := (82495024529543 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12854 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12854]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12854])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12854) (a := (8400386099361 / 10000000000000 : ℝ)) (b := (160222950829 / 100000000000000 : ℝ)) (q := (1116478476981 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12854])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12854])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12854]

theorem cert12854_3 : CellCertificate 12854 (441218888520431 / 5000000000000000 : ℝ) (81703539613603 / 50000000000000000 : ℝ) (82495024529543 / 2500000000000000 : ℝ)
    (cell12854 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · have h := gap_lower (n := 12854) (a := (2099224613069 / 2500000000000 : ℝ)) (b := (160222950829 / 100000000000000 : ℝ)) (q := (1116480478403 / 50000000000000 : ℝ))
      (E := (cell12854 ⟨3, by decide⟩).energy) (xi := (82495024529543 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12854 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12854]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12854])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12854) (a := (2099224613069 / 2500000000000 : ℝ)) (b := (160222950829 / 100000000000000 : ℝ)) (q := (1116480478403 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12854])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12854])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12854]

theorem cert12854_4 : CellCertificate 12854 (441218888520431 / 5000000000000000 : ℝ) (81703539613603 / 50000000000000000 : ℝ) (82495024529543 / 2500000000000000 : ℝ)
    (cell12854 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · have h := gap_lower (n := 12854) (a := (83934132844653 / 100000000000000 : ℝ)) (b := (160222950829 / 100000000000000 : ℝ)) (q := (2232964943667 / 100000000000000 : ℝ))
      (E := (cell12854 ⟨4, by decide⟩).energy) (xi := (82495024529543 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12854 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12854]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12854])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12854) (a := (83934132844653 / 100000000000000 : ℝ)) (b := (160222950829 / 100000000000000 : ℝ)) (q := (2232964943667 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12854])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12854])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12854]

theorem cert12854_5 : CellCertificate 12854 (441218888520431 / 5000000000000000 : ℝ) (81703539613603 / 50000000000000000 : ℝ) (82495024529543 / 2500000000000000 : ℝ)
    (cell12854 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · have h := gap_lower (n := 12854) (a := (41949652961661 / 50000000000000 : ℝ)) (b := (160222950829 / 100000000000000 : ℝ)) (q := (2232968980529 / 100000000000000 : ℝ))
      (E := (cell12854 ⟨5, by decide⟩).energy) (xi := (82495024529543 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12854 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12854]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12854])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12854) (a := (41949652961661 / 50000000000000 : ℝ)) (b := (160222950829 / 100000000000000 : ℝ)) (q := (2232968980529 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12854])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12854])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12854]

theorem cert12854_6 : CellCertificate 12854 (441218888520431 / 5000000000000000 : ℝ) (81703539613603 / 50000000000000000 : ℝ) (82495024529543 / 2500000000000000 : ℝ)
    (cell12854 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · have h := gap_lower (n := 12854) (a := (83864503722987 / 100000000000000 : ℝ)) (b := (160222950829 / 100000000000000 : ℝ)) (q := (1116486479659 / 50000000000000 : ℝ))
      (E := (cell12854 ⟨6, by decide⟩).energy) (xi := (82495024529543 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12854 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12854]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12854])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12854) (a := (83864503722987 / 100000000000000 : ℝ)) (b := (160222950829 / 100000000000000 : ℝ)) (q := (1116486479659 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12854])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12854])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12854]

theorem cert12854_7 : CellCertificate 12854 (441218888520431 / 5000000000000000 : ℝ) (81703539613603 / 50000000000000000 : ℝ) (82495024529543 / 2500000000000000 : ℝ)
    (cell12854 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · have h := gap_lower (n := 12854) (a := (83829726208057 / 100000000000000 : ℝ)) (b := (160222950829 / 100000000000000 : ℝ)) (q := (89319080139 / 4000000000000 : ℝ))
      (E := (cell12854 ⟨7, by decide⟩).energy) (xi := (82495024529543 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12854 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12854]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12854])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12854) (a := (83829726208057 / 100000000000000 : ℝ)) (b := (160222950829 / 100000000000000 : ℝ)) (q := (89319080139 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12854])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12854])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12854]

theorem cert12854_8 : CellCertificate 12854 (441218888520431 / 5000000000000000 : ℝ) (81703539613603 / 50000000000000000 : ℝ) (82495024529543 / 2500000000000000 : ℝ)
    (cell12854 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · have h := gap_lower (n := 12854) (a := (83794973343127 / 100000000000000 : ℝ)) (b := (160222950829 / 100000000000000 : ℝ)) (q := (89319240173 / 4000000000000 : ℝ))
      (E := (cell12854 ⟨8, by decide⟩).energy) (xi := (82495024529543 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12854 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12854]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12854])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12854) (a := (83794973343127 / 100000000000000 : ℝ)) (b := (160222950829 / 100000000000000 : ℝ)) (q := (89319240173 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12854])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12854])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12854]

theorem cert12854_9 : CellCertificate 12854 (441218888520431 / 5000000000000000 : ℝ) (81703539613603 / 50000000000000000 : ℝ) (82495024529543 / 2500000000000000 : ℝ)
    (cell12854 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · have h := gap_lower (n := 12854) (a := (5235015318311 / 6250000000000 : ℝ)) (b := (160222950829 / 100000000000000 : ℝ)) (q := (558246242207 / 25000000000000 : ℝ))
      (E := (cell12854 ⟨9, by decide⟩).energy) (xi := (82495024529543 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12854 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12854]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12854])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12854) (a := (5235015318311 / 6250000000000 : ℝ)) (b := (160222950829 / 100000000000000 : ℝ)) (q := (558246242207 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12854])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12854])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12854]

theorem cert12854_10 : CellCertificate 12854 (441218888520431 / 5000000000000000 : ℝ) (81703539613603 / 50000000000000000 : ℝ) (82495024529543 / 2500000000000000 : ℝ)
    (cell12854 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · have h := gap_lower (n := 12854) (a := (83725541422569 / 100000000000000 : ℝ)) (b := (160222950829 / 100000000000000 : ℝ)) (q := (2232988961749 / 100000000000000 : ℝ))
      (E := (cell12854 ⟨10, by decide⟩).energy) (xi := (82495024529543 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12854 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12854]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12854])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12854) (a := (83725541422569 / 100000000000000 : ℝ)) (b := (160222950829 / 100000000000000 : ℝ)) (q := (2232988961749 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12854])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12854])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12854]

theorem cert12854_11 : CellCertificate 12854 (441218888520431 / 5000000000000000 : ℝ) (81703539613603 / 50000000000000000 : ℝ) (82495024529543 / 2500000000000000 : ℝ)
    (cell12854 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · have h := gap_lower (n := 12854) (a := (83690862297051 / 100000000000000 : ℝ)) (b := (160222950829 / 100000000000000 : ℝ)) (q := (2232992989619 / 100000000000000 : ℝ))
      (E := (cell12854 ⟨11, by decide⟩).energy) (xi := (82495024529543 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12854 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12854]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12854])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12854) (a := (83690862297051 / 100000000000000 : ℝ)) (b := (160222950829 / 100000000000000 : ℝ)) (q := (2232992989619 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12854])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12854])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12854]

theorem cert12854_12 : CellCertificate 12854 (441218888520431 / 5000000000000000 : ℝ) (81703539613603 / 50000000000000000 : ℝ) (82495024529543 / 2500000000000000 : ℝ)
    (cell12854 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · have h := gap_lower (n := 12854) (a := (83656207681751 / 100000000000000 : ℝ)) (b := (160222950829 / 100000000000000 : ℝ)) (q := (558249250153 / 25000000000000 : ℝ))
      (E := (cell12854 ⟨12, by decide⟩).energy) (xi := (82495024529543 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12854 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12854]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12854])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12854) (a := (83656207681751 / 100000000000000 : ℝ)) (b := (160222950829 / 100000000000000 : ℝ)) (q := (558249250153 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12854])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12854])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12854]

theorem cert12854_13 : CellCertificate 12854 (441218888520431 / 5000000000000000 : ℝ) (81703539613603 / 50000000000000000 : ℝ) (82495024529543 / 2500000000000000 : ℝ)
    (cell12854 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · have h := gap_lower (n := 12854) (a := (83621577542177 / 100000000000000 : ℝ)) (b := (160222950829 / 100000000000000 : ℝ)) (q := (223300100069 / 10000000000000 : ℝ))
      (E := (cell12854 ⟨13, by decide⟩).energy) (xi := (82495024529543 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12854 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12854]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12854])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12854) (a := (83621577542177 / 100000000000000 : ℝ)) (b := (160222950829 / 100000000000000 : ℝ)) (q := (223300100069 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12854])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12854])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12854]

theorem cert12854_14 : CellCertificate 12854 (441218888520431 / 5000000000000000 : ℝ) (81703539613603 / 50000000000000000 : ℝ) (82495024529543 / 2500000000000000 : ℝ)
    (cell12854 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · have h := gap_lower (n := 12854) (a := (5224185740251 / 6250000000000 : ℝ)) (b := (160222950829 / 100000000000000 : ℝ)) (q := (2233004995571 / 100000000000000 : ℝ))
      (E := (cell12854 ⟨14, by decide⟩).energy) (xi := (82495024529543 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12854 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12854]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12854])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12854) (a := (5224185740251 / 6250000000000 : ℝ)) (b := (160222950829 / 100000000000000 : ℝ)) (q := (2233004995571 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12854])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12854])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12854]

theorem cert12854_15 : CellCertificate 12854 (441218888520431 / 5000000000000000 : ℝ) (81703539613603 / 50000000000000000 : ℝ) (82495024529543 / 2500000000000000 : ℝ)
    (cell12854 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · have h := gap_lower (n := 12854) (a := (16710478110627 / 20000000000000 : ℝ)) (b := (160222950829 / 100000000000000 : ℝ)) (q := (2233008990727 / 100000000000000 : ℝ))
      (E := (cell12854 ⟨15, by decide⟩).energy) (xi := (82495024529543 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12854 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12854]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12854])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12854) (a := (16710478110627 / 20000000000000 : ℝ)) (b := (160222950829 / 100000000000000 : ℝ)) (q := (2233008990727 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12854])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12854])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12854]

theorem cert12854_16 : CellCertificate 12854 (441218888520431 / 5000000000000000 : ℝ) (81703539613603 / 50000000000000000 : ℝ) (82495024529543 / 2500000000000000 : ℝ)
    (cell12854 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · have h := gap_lower (n := 12854) (a := (3340713345423 / 4000000000000 : ℝ)) (b := (160222950829 / 100000000000000 : ℝ)) (q := (1116506495693 / 50000000000000 : ℝ))
      (E := (cell12854 ⟨16, by decide⟩).energy) (xi := (82495024529543 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12854 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12854]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12854])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12854) (a := (3340713345423 / 4000000000000 : ℝ)) (b := (160222950829 / 100000000000000 : ℝ)) (q := (1116506495693 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12854])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12854])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12854]

theorem cert12854_17 : CellCertificate 12854 (441218888520431 / 5000000000000000 : ℝ) (81703539613603 / 50000000000000000 : ℝ) (82495024529543 / 2500000000000000 : ℝ)
    (cell12854 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · have h := gap_lower (n := 12854) (a := (20870825264389 / 25000000000000 : ℝ)) (b := (160222950829 / 100000000000000 : ℝ)) (q := (2233017002533 / 100000000000000 : ℝ))
      (E := (cell12854 ⟨17, by decide⟩).energy) (xi := (82495024529543 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12854 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12854]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12854])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12854) (a := (20870825264389 / 25000000000000 : ℝ)) (b := (160222950829 / 100000000000000 : ℝ)) (q := (2233017002533 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12854])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12854])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12854]

theorem cert12854_18 : CellCertificate 12854 (441218888520431 / 5000000000000000 : ℝ) (81703539613603 / 50000000000000000 : ℝ) (82495024529543 / 2500000000000000 : ℝ)
    (cell12854 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · have h := gap_lower (n := 12854) (a := (83448792785469 / 100000000000000 : ℝ)) (b := (160222950829 / 100000000000000 : ℝ)) (q := (2233021028913 / 100000000000000 : ℝ))
      (E := (cell12854 ⟨18, by decide⟩).energy) (xi := (82495024529543 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12854 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12854]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12854])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12854) (a := (83448792785469 / 100000000000000 : ℝ)) (b := (160222950829 / 100000000000000 : ℝ)) (q := (2233021028913 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12854])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12854])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12854]

theorem cert12854_19 : CellCertificate 12854 (441218888520431 / 5000000000000000 : ℝ) (81703539613603 / 50000000000000000 : ℝ) (82495024529543 / 2500000000000000 : ℝ)
    (cell12854 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · have h := gap_lower (n := 12854) (a := (83414308785883 / 100000000000000 : ℝ)) (b := (160222950829 / 100000000000000 : ℝ)) (q := (1116512508379 / 50000000000000 : ℝ))
      (E := (cell12854 ⟨19, by decide⟩).energy) (xi := (82495024529543 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12854 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12854]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12854])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12854) (a := (83414308785883 / 100000000000000 : ℝ)) (b := (160222950829 / 100000000000000 : ℝ)) (q := (1116512508379 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12854])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12854])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12854]

theorem cert12855_0 : CellCertificate 12855 (176482096231053 / 2000000000000000 : ℝ) (1633943635400539 / 1000000000000000000 : ℝ) (329953818184927 / 10000000000000000 : ℝ)
    (cell12855 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · have h := gap_lower (n := 12855) (a := (21018418422763 / 25000000000000 : ℝ)) (b := (80105169371 / 50000000000000 : ℝ)) (q := (1116415494091 / 50000000000000 : ℝ))
      (E := (cell12855 ⟨0, by decide⟩).energy) (xi := (329953818184927 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12855 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12855]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12855])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12855) (a := (21018418422763 / 25000000000000 : ℝ)) (b := (80105169371 / 50000000000000 : ℝ)) (q := (1116415494091 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12855])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12855])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12855]

theorem cert12855_1 : CellCertificate 12855 (176482096231053 / 2000000000000000 : ℝ) (1633943635400539 / 1000000000000000000 : ℝ) (329953818184927 / 10000000000000000 : ℝ)
    (cell12855 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · have h := gap_lower (n := 12855) (a := (1313105435003 / 1562500000000 : ℝ)) (b := (80105169371 / 50000000000000 : ℝ)) (q := (223283502241 / 10000000000000 : ℝ))
      (E := (cell12855 ⟨1, by decide⟩).energy) (xi := (329953818184927 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12855 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12855]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12855])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12855) (a := (1313105435003 / 1562500000000 : ℝ)) (b := (80105169371 / 50000000000000 : ℝ)) (q := (223283502241 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12855])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12855])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12855]

theorem cert12855_2 : CellCertificate 12855 (176482096231053 / 2000000000000000 : ℝ) (1633943635400539 / 1000000000000000000 : ℝ) (329953818184927 / 10000000000000000 : ℝ)
    (cell12855 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · have h := gap_lower (n := 12855) (a := (4200192342707 / 5000000000000 : ℝ)) (b := (80105169371 / 50000000000000 : ℝ)) (q := (558209756129 / 25000000000000 : ℝ))
      (E := (cell12855 ⟨2, by decide⟩).energy) (xi := (329953818184927 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12855 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12855]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12855])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12855) (a := (4200192342707 / 5000000000000 : ℝ)) (b := (80105169371 / 50000000000000 : ℝ)) (q := (558209756129 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12855])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12855])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12855]

theorem cert12855_3 : CellCertificate 12855 (176482096231053 / 2000000000000000 : ℝ) (1633943635400539 / 1000000000000000000 : ℝ) (329953818184927 / 10000000000000000 : ℝ)
    (cell12855 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · have h := gap_lower (n := 12855) (a := (83968970696547 / 100000000000000 : ℝ)) (b := (80105169371 / 50000000000000 : ℝ)) (q := (2232843003057 / 100000000000000 : ℝ))
      (E := (cell12855 ⟨3, by decide⟩).energy) (xi := (329953818184927 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12855 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12855]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12855])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12855) (a := (83968970696547 / 100000000000000 : ℝ)) (b := (80105169371 / 50000000000000 : ℝ)) (q := (2232843003057 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12855])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12855])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12855]

theorem cert12855_4 : CellCertificate 12855 (176482096231053 / 2000000000000000 : ℝ) (1633943635400539 / 1000000000000000000 : ℝ) (329953818184927 / 10000000000000000 : ℝ)
    (cell12855 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · have h := gap_lower (n := 12855) (a := (16786823866251 / 20000000000000 : ℝ)) (b := (80105169371 / 50000000000000 : ℝ)) (q := (2232847024251 / 100000000000000 : ℝ))
      (E := (cell12855 ⟨4, by decide⟩).energy) (xi := (329953818184927 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12855 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12855]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12855])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12855) (a := (16786823866251 / 20000000000000 : ℝ)) (b := (80105169371 / 50000000000000 : ℝ)) (q := (2232847024251 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12855])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12855])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12855]

theorem cert12855_5 : CellCertificate 12855 (176482096231053 / 2000000000000000 : ℝ) (1633943635400539 / 1000000000000000000 : ℝ) (329953818184927 / 10000000000000000 : ℝ)
    (cell12855 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · have h := gap_lower (n := 12855) (a := (41949646361149 / 50000000000000 : ℝ)) (b := (80105169371 / 50000000000000 : ℝ)) (q := (446570207653 / 20000000000000 : ℝ))
      (E := (cell12855 ⟨5, by decide⟩).energy) (xi := (329953818184927 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12855 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12855]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12855])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12855) (a := (41949646361149 / 50000000000000 : ℝ)) (b := (80105169371 / 50000000000000 : ℝ)) (q := (446570207653 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12855])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12855])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12855]

theorem cert12855_6 : CellCertificate 12855 (176482096231053 / 2000000000000000 : ℝ) (1633943635400539 / 1000000000000000000 : ℝ) (329953818184927 / 10000000000000000 : ℝ)
    (cell12855 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · have h := gap_lower (n := 12855) (a := (41932245416949 / 50000000000000 : ℝ)) (b := (80105169371 / 50000000000000 : ℝ)) (q := (2232854994921 / 100000000000000 : ℝ))
      (E := (cell12855 ⟨6, by decide⟩).energy) (xi := (329953818184927 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12855 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12855]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12855])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12855) (a := (41932245416949 / 50000000000000 : ℝ)) (b := (80105169371 / 50000000000000 : ℝ)) (q := (2232854994921 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12855])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12855])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12855]

theorem cert12855_7 : CellCertificate 12855 (176482096231053 / 2000000000000000 : ℝ) (1633943635400539 / 1000000000000000000 : ℝ) (329953818184927 / 10000000000000000 : ℝ)
    (cell12855 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · have h := gap_lower (n := 12855) (a := (327459818869 / 390625000000 : ℝ)) (b := (80105169371 / 50000000000000 : ℝ)) (q := (1116429508829 / 50000000000000 : ℝ))
      (E := (cell12855 ⟨7, by decide⟩).energy) (xi := (329953818184927 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12855 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12855]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12855])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12855) (a := (327459818869 / 390625000000 : ℝ)) (b := (80105169371 / 50000000000000 : ℝ)) (q := (1116429508829 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12855])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12855])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12855]

theorem cert12855_8 : CellCertificate 12855 (176482096231053 / 2000000000000000 : ℝ) (1633943635400539 / 1000000000000000000 : ℝ) (329953818184927 / 10000000000000000 : ℝ)
    (cell12855 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · have h := gap_lower (n := 12855) (a := (83794961076591 / 100000000000000 : ℝ)) (b := (80105169371 / 50000000000000 : ℝ)) (q := (2232862997803 / 100000000000000 : ℝ))
      (E := (cell12855 ⟨8, by decide⟩).energy) (xi := (329953818184927 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12855 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12855]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12855])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12855) (a := (83794961076591 / 100000000000000 : ℝ)) (b := (80105169371 / 50000000000000 : ℝ)) (q := (2232862997803 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12855])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12855])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12855]

theorem cert12855_9 : CellCertificate 12855 (176482096231053 / 2000000000000000 : ℝ) (1633943635400539 / 1000000000000000000 : ℝ) (329953818184927 / 10000000000000000 : ℝ)
    (cell12855 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · have h := gap_lower (n := 12855) (a := (83760233137061 / 100000000000000 : ℝ)) (b := (80105169371 / 50000000000000 : ℝ)) (q := (2232867000347 / 100000000000000 : ℝ))
      (E := (cell12855 ⟨9, by decide⟩).energy) (xi := (329953818184927 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12855 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12855]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12855])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12855) (a := (83760233137061 / 100000000000000 : ℝ)) (b := (80105169371 / 50000000000000 : ℝ)) (q := (2232867000347 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12855])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12855])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12855]

theorem cert12855_10 : CellCertificate 12855 (176482096231053 / 2000000000000000 : ℝ) (1633943635400539 / 1000000000000000000 : ℝ) (329953818184927 / 10000000000000000 : ℝ)
    (cell12855 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · have h := gap_lower (n := 12855) (a := (41862764888419 / 50000000000000 : ℝ)) (b := (80105169371 / 50000000000000 : ℝ)) (q := (2232871032069 / 100000000000000 : ℝ))
      (E := (cell12855 ⟨10, by decide⟩).energy) (xi := (329953818184927 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12855 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12855]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12855])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12855) (a := (41862764888419 / 50000000000000 : ℝ)) (b := (80105169371 / 50000000000000 : ℝ)) (q := (2232871032069 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12855])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12855])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12855]

theorem cert12855_11 : CellCertificate 12855 (176482096231053 / 2000000000000000 : ℝ) (1633943635400539 / 1000000000000000000 : ℝ) (329953818184927 / 10000000000000000 : ℝ)
    (cell12855 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · have h := gap_lower (n := 12855) (a := (8369085096107 / 10000000000000 : ℝ)) (b := (80105169371 / 50000000000000 : ℝ)) (q := (558218760353 / 25000000000000 : ℝ))
      (E := (cell12855 ⟨11, by decide⟩).energy) (xi := (329953818184927 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12855 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12855]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12855])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12855) (a := (8369085096107 / 10000000000000 : ℝ)) (b := (80105169371 / 50000000000000 : ℝ)) (q := (558218760353 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12855])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12855])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12855]

theorem cert12855_12 : CellCertificate 12855 (176482096231053 / 2000000000000000 : ℝ) (1633943635400539 / 1000000000000000000 : ℝ) (329953818184927 / 10000000000000000 : ℝ)
    (cell12855 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · have h := gap_lower (n := 12855) (a := (16731239331017 / 20000000000000 : ℝ)) (b := (80105169371 / 50000000000000 : ℝ)) (q := (558219758647 / 25000000000000 : ℝ))
      (E := (cell12855 ⟨12, by decide⟩).energy) (xi := (329953818184927 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12855 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12855]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12855])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12855) (a := (16731239331017 / 20000000000000 : ℝ)) (b := (80105169371 / 50000000000000 : ℝ)) (q := (558219758647 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12855])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12855])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12855]

theorem cert12855_13 : CellCertificate 12855 (176482096231053 / 2000000000000000 : ℝ) (1633943635400539 / 1000000000000000000 : ℝ) (329953818184927 / 10000000000000000 : ℝ)
    (cell12855 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · have h := gap_lower (n := 12855) (a := (10452695853049 / 12500000000000 : ℝ)) (b := (80105169371 / 50000000000000 : ℝ)) (q := (1116441508779 / 50000000000000 : ℝ))
      (E := (cell12855 ⟨13, by decide⟩).energy) (xi := (329953818184927 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12855 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12855]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12855])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12855) (a := (10452695853049 / 12500000000000 : ℝ)) (b := (80105169371 / 50000000000000 : ℝ)) (q := (1116441508779 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12855])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12855])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12855]

theorem cert12855_14 : CellCertificate 12855 (176482096231053 / 2000000000000000 : ℝ) (1633943635400539 / 1000000000000000000 : ℝ) (329953818184927 / 10000000000000000 : ℝ)
    (cell12855 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · have h := gap_lower (n := 12855) (a := (83586961434681 / 100000000000000 : ℝ)) (b := (80105169371 / 50000000000000 : ℝ)) (q := (2232887054191 / 100000000000000 : ℝ))
      (E := (cell12855 ⟨14, by decide⟩).energy) (xi := (329953818184927 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12855 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12855]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12855])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12855) (a := (83586961434681 / 100000000000000 : ℝ)) (b := (80105169371 / 50000000000000 : ℝ)) (q := (2232887054191 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12855])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12855])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12855]

theorem cert12855_15 : CellCertificate 12855 (176482096231053 / 2000000000000000 : ℝ) (1633943635400539 / 1000000000000000000 : ℝ) (329953818184927 / 10000000000000000 : ℝ)
    (cell12855 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · have h := gap_lower (n := 12855) (a := (83552380451817 / 100000000000000 : ℝ)) (b := (80105169371 / 50000000000000 : ℝ)) (q := (558222758419 / 25000000000000 : ℝ))
      (E := (cell12855 ⟨15, by decide⟩).energy) (xi := (329953818184927 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12855 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12855]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12855])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12855) (a := (83552380451817 / 100000000000000 : ℝ)) (b := (80105169371 / 50000000000000 : ℝ)) (q := (558222758419 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12855])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12855])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12855]

theorem cert12855_16 : CellCertificate 12855 (176482096231053 / 2000000000000000 : ℝ) (1633943635400539 / 1000000000000000000 : ℝ) (329953818184927 / 10000000000000000 : ℝ)
    (cell12855 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · have h := gap_lower (n := 12855) (a := (16703564768369 / 20000000000000 : ℝ)) (b := (80105169371 / 50000000000000 : ℝ)) (q := (2232895019369 / 100000000000000 : ℝ))
      (E := (cell12855 ⟨16, by decide⟩).energy) (xi := (329953818184927 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12855 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12855]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12855])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12855) (a := (16703564768369 / 20000000000000 : ℝ)) (b := (80105169371 / 50000000000000 : ℝ)) (q := (2232895019369 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12855])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12855])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12855]

theorem cert12855_17 : CellCertificate 12855 (176482096231053 / 2000000000000000 : ℝ) (1633943635400539 / 1000000000000000000 : ℝ) (329953818184927 / 10000000000000000 : ℝ)
    (cell12855 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · have h := gap_lower (n := 12855) (a := (83483291570983 / 100000000000000 : ℝ)) (b := (80105169371 / 50000000000000 : ℝ)) (q := (27911238431 / 1250000000000 : ℝ))
      (E := (cell12855 ⟨17, by decide⟩).energy) (xi := (329953818184927 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12855 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12855]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12855])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12855) (a := (83483291570983 / 100000000000000 : ℝ)) (b := (80105169371 / 50000000000000 : ℝ)) (q := (27911238431 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12855])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12855])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12855]

theorem cert12855_18 : CellCertificate 12855 (176482096231053 / 2000000000000000 : ℝ) (1633943635400539 / 1000000000000000000 : ℝ) (329953818184927 / 10000000000000000 : ℝ)
    (cell12855 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · have h := gap_lower (n := 12855) (a := (133518053769 / 160000000000 : ℝ)) (b := (80105169371 / 50000000000000 : ℝ)) (q := (55822575727 / 2500000000000 : ℝ))
      (E := (cell12855 ⟨18, by decide⟩).energy) (xi := (329953818184927 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12855 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12855]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12855])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12855) (a := (133518053769 / 160000000000 : ℝ)) (b := (80105169371 / 50000000000000 : ℝ)) (q := (55822575727 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12855])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12855])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12855]

theorem cert12855_19 : CellCertificate 12855 (176482096231053 / 2000000000000000 : ℝ) (1633943635400539 / 1000000000000000000 : ℝ) (329953818184927 / 10000000000000000 : ℝ)
    (cell12855 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · have h := gap_lower (n := 12855) (a := (4170714995617 / 5000000000000 : ℝ)) (b := (80105169371 / 50000000000000 : ℝ)) (q := (2232907062341 / 100000000000000 : ℝ))
      (E := (cell12855 ⟨19, by decide⟩).energy) (xi := (329953818184927 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12855 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12855]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12855])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12855) (a := (4170714995617 / 5000000000000 : ℝ)) (b := (80105169371 / 50000000000000 : ℝ)) (q := (2232907062341 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12855])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12855])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12855]

theorem cert12856_0 : CellCertificate 12856 (35295327573681 / 400000000000000 : ℝ) (1633816498317157 / 1000000000000000000 : ℝ) (8248188562077 / 250000000000000 : ℝ)
    (cell12856 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · have h := gap_lower (n := 12856) (a := (84073658926039 / 100000000000000 : ℝ)) (b := (160197728653 / 100000000000000 : ℝ)) (q := (2232713047129 / 100000000000000 : ℝ))
      (E := (cell12856 ⟨0, by decide⟩).energy) (xi := (8248188562077 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12856 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12856]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12856])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12856) (a := (84073658926039 / 100000000000000 : ℝ)) (b := (160197728653 / 100000000000000 : ℝ)) (q := (2232713047129 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12856])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12856])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12856]

theorem cert12856_1 : CellCertificate 12856 (35295327573681 / 400000000000000 : ℝ) (1633816498317157 / 1000000000000000000 : ℝ) (8248188562077 / 250000000000000 : ℝ)
    (cell12856 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · have h := gap_lower (n := 12856) (a := (16807746677857 / 20000000000000 : ℝ)) (b := (160197728653 / 100000000000000 : ℝ)) (q := (2232717055633 / 100000000000000 : ℝ))
      (E := (cell12856 ⟨1, by decide⟩).energy) (xi := (8248188562077 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12856 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12856]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12856])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12856) (a := (16807746677857 / 20000000000000 : ℝ)) (b := (160197728653 / 100000000000000 : ℝ)) (q := (2232717055633 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12856])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12856])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12856]

theorem cert12856_2 : CellCertificate 12856 (35295327573681 / 400000000000000 : ℝ) (1633816498317157 / 1000000000000000000 : ℝ) (8248188562077 / 250000000000000 : ℝ)
    (cell12856 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · have h := gap_lower (n := 12856) (a := (16800766543379 / 20000000000000 : ℝ)) (b := (160197728653 / 100000000000000 : ℝ)) (q := (1116360545303 / 50000000000000 : ℝ))
      (E := (cell12856 ⟨2, by decide⟩).energy) (xi := (8248188562077 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12856 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12856]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12856])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12856) (a := (16800766543379 / 20000000000000 : ℝ)) (b := (160197728653 / 100000000000000 : ℝ)) (q := (1116360545303 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12856])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12856])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12856]

theorem cert12856_3 : CellCertificate 12856 (35295327573681 / 400000000000000 : ℝ) (1633816498317157 / 1000000000000000000 : ℝ) (8248188562077 / 250000000000000 : ℝ)
    (cell12856 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · have h := gap_lower (n := 12856) (a := (83968956872521 / 100000000000000 : ℝ)) (b := (160197728653 / 100000000000000 : ℝ)) (q := (1116362551389 / 50000000000000 : ℝ))
      (E := (cell12856 ⟨3, by decide⟩).energy) (xi := (8248188562077 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12856 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12856]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12856])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12856) (a := (83968956872521 / 100000000000000 : ℝ)) (b := (160197728653 / 100000000000000 : ℝ)) (q := (1116362551389 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12856])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12856])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12856]

theorem cert12856_4 : CellCertificate 12856 (35295327573681 / 400000000000000 : ℝ) (1633816498317157 / 1000000000000000000 : ℝ) (8248188562077 / 250000000000000 : ℝ)
    (cell12856 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · have h := gap_lower (n := 12856) (a := (83934105820007 / 100000000000000 : ℝ)) (b := (160197728653 / 100000000000000 : ℝ)) (q := (2232729100447 / 100000000000000 : ℝ))
      (E := (cell12856 ⟨4, by decide⟩).energy) (xi := (8248188562077 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12856 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12856]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12856])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12856) (a := (83934105820007 / 100000000000000 : ℝ)) (b := (160197728653 / 100000000000000 : ℝ)) (q := (2232729100447 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12856])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12856])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12856]

theorem cert12856_5 : CellCertificate 12856 (35295327573681 / 400000000000000 : ℝ) (1633816498317157 / 1000000000000000000 : ℝ) (8248188562077 / 250000000000000 : ℝ)
    (cell12856 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · have h := gap_lower (n := 12856) (a := (83899279523387 / 100000000000000 : ℝ)) (b := (160197728653 / 100000000000000 : ℝ)) (q := (558183272913 / 25000000000000 : ℝ))
      (E := (cell12856 ⟨5, by decide⟩).energy) (xi := (8248188562077 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12856 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12856]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12856])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12856) (a := (83899279523387 / 100000000000000 : ℝ)) (b := (160197728653 / 100000000000000 : ℝ)) (q := (558183272913 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12856])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12856])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12856]

theorem cert12856_6 : CellCertificate 12856 (35295327573681 / 400000000000000 : ℝ) (1633816498317157 / 1000000000000000000 : ℝ) (8248188562077 / 250000000000000 : ℝ)
    (cell12856 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · have h := gap_lower (n := 12856) (a := (20966119486721 / 25000000000000 : ℝ)) (b := (160197728653 / 100000000000000 : ℝ)) (q := (1116368542089 / 50000000000000 : ℝ))
      (E := (cell12856 ⟨6, by decide⟩).energy) (xi := (8248188562077 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12856 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12856]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12856])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12856) (a := (20966119486721 / 25000000000000 : ℝ)) (b := (160197728653 / 100000000000000 : ℝ)) (q := (1116368542089 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12856])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12856])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12856]

theorem cert12856_7 : CellCertificate 12856 (35295327573681 / 400000000000000 : ℝ) (1633816498317157 / 1000000000000000000 : ℝ) (8248188562077 / 250000000000000 : ℝ)
    (cell12856 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · have h := gap_lower (n := 12856) (a := (20957425263727 / 25000000000000 : ℝ)) (b := (160197728653 / 100000000000000 : ℝ)) (q := (2232741085559 / 100000000000000 : ℝ))
      (E := (cell12856 ⟨7, by decide⟩).energy) (xi := (8248188562077 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12856 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12856]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12856])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12856) (a := (20957425263727 / 25000000000000 : ℝ)) (b := (160197728653 / 100000000000000 : ℝ)) (q := (2232741085559 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12856])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12856])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12856]

theorem cert12856_8 : CellCertificate 12856 (35295327573681 / 400000000000000 : ℝ) (1633816498317157 / 1000000000000000000 : ℝ) (8248188562077 / 250000000000000 : ℝ)
    (cell12856 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · have h := gap_lower (n := 12856) (a := (16758989762411 / 20000000000000 : ℝ)) (b := (160197728653 / 100000000000000 : ℝ)) (q := (69773284471 / 3125000000000 : ℝ))
      (E := (cell12856 ⟨8, by decide⟩).energy) (xi := (8248188562077 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12856 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12856]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12856])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12856) (a := (16758989762411 / 20000000000000 : ℝ)) (b := (160197728653 / 100000000000000 : ℝ)) (q := (69773284471 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12856])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12856])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12856]

theorem cert12856_9 : CellCertificate 12856 (35295327573681 / 400000000000000 : ℝ) (1633816498317157 / 1000000000000000000 : ℝ) (8248188562077 / 250000000000000 : ℝ)
    (cell12856 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · have h := gap_lower (n := 12856) (a := (83760221183109 / 100000000000000 : ℝ)) (b := (160197728653 / 100000000000000 : ℝ)) (q := (1116374542853 / 50000000000000 : ℝ))
      (E := (cell12856 ⟨9, by decide⟩).energy) (xi := (8248188562077 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12856 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12856]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12856])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12856) (a := (83760221183109 / 100000000000000 : ℝ)) (b := (160197728653 / 100000000000000 : ℝ)) (q := (1116374542853 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12856])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12856])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12856]

theorem cert12856_10 : CellCertificate 12856 (35295327573681 / 400000000000000 : ℝ) (1633816498317157 / 1000000000000000000 : ℝ) (8248188562077 / 250000000000000 : ℝ)
    (cell12856 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · have h := gap_lower (n := 12856) (a := (83725518133033 / 100000000000000 : ℝ)) (b := (160197728653 / 100000000000000 : ℝ)) (q := (2232753098229 / 100000000000000 : ℝ))
      (E := (cell12856 ⟨10, by decide⟩).energy) (xi := (8248188562077 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12856 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12856]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12856])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12856) (a := (83725518133033 / 100000000000000 : ℝ)) (b := (160197728653 / 100000000000000 : ℝ)) (q := (2232753098229 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12856])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12856])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12856]

theorem cert12856_11 : CellCertificate 12856 (35295327573681 / 400000000000000 : ℝ) (1633816498317157 / 1000000000000000000 : ℝ) (8248188562077 / 250000000000000 : ℝ)
    (cell12856 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · have h := gap_lower (n := 12856) (a := (83690839626977 / 100000000000000 : ℝ)) (b := (160197728653 / 100000000000000 : ℝ)) (q := (446551417817 / 20000000000000 : ℝ))
      (E := (cell12856 ⟨11, by decide⟩).energy) (xi := (8248188562077 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12856 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12856]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12856])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12856) (a := (83690839626977 / 100000000000000 : ℝ)) (b := (160197728653 / 100000000000000 : ℝ)) (q := (446551417817 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12856])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12856])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12856]

theorem cert12856_12 : CellCertificate 12856 (35295327573681 / 400000000000000 : ℝ) (1633816498317157 / 1000000000000000000 : ℝ) (8248188562077 / 250000000000000 : ℝ)
    (cell12856 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · have h := gap_lower (n := 12856) (a := (83656185630269 / 100000000000000 : ℝ)) (b := (160197728653 / 100000000000000 : ℝ)) (q := (2232761122589 / 100000000000000 : ℝ))
      (E := (cell12856 ⟨12, by decide⟩).energy) (xi := (8248188562077 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12856 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12856]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12856])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12856) (a := (83656185630269 / 100000000000000 : ℝ)) (b := (160197728653 / 100000000000000 : ℝ)) (q := (2232761122589 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12856])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12856])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12856]

theorem cert12856_13 : CellCertificate 12856 (35295327573681 / 400000000000000 : ℝ) (1633816498317157 / 1000000000000000000 : ℝ) (8248188562077 / 250000000000000 : ℝ)
    (cell12856 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · have h := gap_lower (n := 12856) (a := (41810778054211 / 50000000000000 : ℝ)) (b := (160197728653 / 100000000000000 : ℝ)) (q := (2232765088511 / 100000000000000 : ℝ))
      (E := (cell12856 ⟨13, by decide⟩).energy) (xi := (8248188562077 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12856 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12856]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12856])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12856) (a := (41810778054211 / 50000000000000 : ℝ)) (b := (160197728653 / 100000000000000 : ℝ)) (q := (2232765088511 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12856])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12856])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12856]

theorem cert12856_14 : CellCertificate 12856 (35295327573681 / 400000000000000 : ℝ) (1633816498317157 / 1000000000000000000 : ℝ) (8248188562077 / 250000000000000 : ℝ)
    (cell12856 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · have h := gap_lower (n := 12856) (a := (83586951027123 / 100000000000000 : ℝ)) (b := (160197728653 / 100000000000000 : ℝ)) (q := (558192277201 / 25000000000000 : ℝ))
      (E := (cell12856 ⟨14, by decide⟩).energy) (xi := (8248188562077 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12856 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12856]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12856])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12856) (a := (83586951027123 / 100000000000000 : ℝ)) (b := (160197728653 / 100000000000000 : ℝ)) (q := (558192277201 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12856])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12856])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12856]

theorem cert12856_15 : CellCertificate 12856 (35295327573681 / 400000000000000 : ℝ) (1633816498317157 / 1000000000000000000 : ℝ) (8248188562077 / 250000000000000 : ℝ)
    (cell12856 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · have h := gap_lower (n := 12856) (a := (1044404629403 / 1250000000000 : ℝ)) (b := (160197728653 / 100000000000000 : ℝ)) (q := (139548320677 / 6250000000000 : ℝ))
      (E := (cell12856 ⟨15, by decide⟩).energy) (xi := (8248188562077 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12856 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12856]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12856])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12856) (a := (1044404629403 / 1250000000000 : ℝ)) (b := (160197728653 / 100000000000000 : ℝ)) (q := (139548320677 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12856])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12856])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12856]

theorem cert12856_16 : CellCertificate 12856 (35295327573681 / 400000000000000 : ℝ) (1633816498317157 / 1000000000000000000 : ℝ) (8248188562077 / 250000000000000 : ℝ)
    (cell12856 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · have h := gap_lower (n := 12856) (a := (41758907024909 / 50000000000000 : ℝ)) (b := (160197728653 / 100000000000000 : ℝ)) (q := (1116388550811 / 50000000000000 : ℝ))
      (E := (cell12856 ⟨16, by decide⟩).energy) (xi := (8248188562077 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12856 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12856]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12856])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12856) (a := (41758907024909 / 50000000000000 : ℝ)) (b := (160197728653 / 100000000000000 : ℝ)) (q := (1116388550811 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12856])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12856])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12856]

theorem cert12856_17 : CellCertificate 12856 (35295327573681 / 400000000000000 : ℝ) (1633816498317157 / 1000000000000000000 : ℝ) (8248188562077 / 250000000000000 : ℝ)
    (cell12856 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · have h := gap_lower (n := 12856) (a := (83483282086077 / 100000000000000 : ℝ)) (b := (160197728653 / 100000000000000 : ℝ)) (q := (2232781142533 / 100000000000000 : ℝ))
      (E := (cell12856 ⟨17, by decide⟩).energy) (xi := (8248188562077 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12856 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12856]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12856])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12856) (a := (83483282086077 / 100000000000000 : ℝ)) (b := (160197728653 / 100000000000000 : ℝ)) (q := (2232781142533 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12856])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12856])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12856]

theorem cert12856_18 : CellCertificate 12856 (35295327573681 / 400000000000000 : ℝ) (1633816498317157 / 1000000000000000000 : ℝ) (8248188562077 / 250000000000000 : ℝ)
    (cell12856 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · have h := gap_lower (n := 12856) (a := (83448774427411 / 100000000000000 : ℝ)) (b := (160197728653 / 100000000000000 : ℝ)) (q := (446557028377 / 20000000000000 : ℝ))
      (E := (cell12856 ⟨18, by decide⟩).energy) (xi := (8248188562077 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12856 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12856]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12856])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12856) (a := (83448774427411 / 100000000000000 : ℝ)) (b := (160197728653 / 100000000000000 : ℝ)) (q := (446557028377 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12856])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12856])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12856]

theorem cert12856_19 : CellCertificate 12856 (35295327573681 / 400000000000000 : ℝ) (1633816498317157 / 1000000000000000000 : ℝ) (8248188562077 / 250000000000000 : ℝ)
    (cell12856 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · have h := gap_lower (n := 12856) (a := (83414291040389 / 100000000000000 : ℝ)) (b := (160197728653 / 100000000000000 : ℝ)) (q := (558197276027 / 25000000000000 : ℝ))
      (E := (cell12856 ⟨19, by decide⟩).energy) (xi := (8248188562077 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12856 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12856]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12856])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12856) (a := (83414291040389 / 100000000000000 : ℝ)) (b := (160197728653 / 100000000000000 : ℝ)) (q := (558197276027 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12856])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12856])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12856]

theorem cert12857_0 : CellCertificate 12857 (220588975400047 / 2500000000000000 : ℝ) (102105586313581 / 62500000000000000 : ℝ) (164950635505767 / 5000000000000000 : ℝ)
    (cell12857 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · have h := gap_lower (n := 12857) (a := (42036822081663 / 50000000000000 : ℝ)) (b := (160185120559 / 100000000000000 : ℝ)) (q := (2232595159363 / 100000000000000 : ℝ))
      (E := (cell12857 ⟨0, by decide⟩).energy) (xi := (164950635505767 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12857 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12857]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12857])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12857) (a := (42036822081663 / 50000000000000 : ℝ)) (b := (160185120559 / 100000000000000 : ℝ)) (q := (2232595159363 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12857])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12857])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12857]

theorem cert12857_1 : CellCertificate 12857 (220588975400047 / 2500000000000000 : ℝ) (102105586313581 / 62500000000000000 : ℝ) (164950635505767 / 5000000000000000 : ℝ)
    (cell12857 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · have h := gap_lower (n := 12857) (a := (525241993379 / 625000000000 : ℝ)) (b := (160185120559 / 100000000000000 : ℝ)) (q := (558149785551 / 25000000000000 : ℝ))
      (E := (cell12857 ⟨1, by decide⟩).energy) (xi := (164950635505767 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12857 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12857]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12857])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12857) (a := (525241993379 / 625000000000 : ℝ)) (b := (160185120559 / 100000000000000 : ℝ)) (q := (558149785551 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12857])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12857])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12857]

theorem cert12857_2 : CellCertificate 12857 (220588975400047 / 2500000000000000 : ℝ) (102105586313581 / 62500000000000000 : ℝ) (164950635505767 / 5000000000000000 : ℝ)
    (cell12857 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · have h := gap_lower (n := 12857) (a := (42001909290937 / 50000000000000 : ℝ)) (b := (160185120559 / 100000000000000 : ℝ)) (q := (1116301576117 / 50000000000000 : ℝ))
      (E := (cell12857 ⟨2, by decide⟩).energy) (xi := (164950635505767 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12857 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12857]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12857])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12857) (a := (42001909290937 / 50000000000000 : ℝ)) (b := (160185120559 / 100000000000000 : ℝ)) (q := (1116301576117 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12857])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12857])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12857]

theorem cert12857_3 : CellCertificate 12857 (220588975400047 / 2500000000000000 : ℝ) (102105586313581 / 62500000000000000 : ℝ) (164950635505767 / 5000000000000000 : ℝ)
    (cell12857 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · have h := gap_lower (n := 12857) (a := (41984471525341 / 50000000000000 : ℝ)) (b := (160185120559 / 100000000000000 : ℝ)) (q := (558151799519 / 25000000000000 : ℝ))
      (E := (cell12857 ⟨3, by decide⟩).energy) (xi := (164950635505767 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12857 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12857]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12857])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12857) (a := (41984471525341 / 50000000000000 : ℝ)) (b := (160185120559 / 100000000000000 : ℝ)) (q := (558151799519 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12857])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12857])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12857]

theorem cert12857_4 : CellCertificate 12857 (220588975400047 / 2500000000000000 : ℝ) (102105586313581 / 62500000000000000 : ℝ) (164950635505767 / 5000000000000000 : ℝ)
    (cell12857 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · have h := gap_lower (n := 12857) (a := (20983523077727 / 25000000000000 : ℝ)) (b := (160185120559 / 100000000000000 : ℝ)) (q := (1116305586129 / 50000000000000 : ℝ))
      (E := (cell12857 ⟨4, by decide⟩).energy) (xi := (164950635505767 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12857 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12857]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12857])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12857) (a := (20983523077727 / 25000000000000 : ℝ)) (b := (160185120559 / 100000000000000 : ℝ)) (q := (1116305586129 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12857])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12857])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12857]

theorem cert12857_5 : CellCertificate 12857 (220588975400047 / 2500000000000000 : ℝ) (102105586313581 / 62500000000000000 : ℝ) (164950635505767 / 5000000000000000 : ℝ)
    (cell12857 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · have h := gap_lower (n := 12857) (a := (83899266326587 / 100000000000000 : ℝ)) (b := (160185120559 / 100000000000000 : ℝ)) (q := (446523039727 / 20000000000000 : ℝ))
      (E := (cell12857 ⟨5, by decide⟩).energy) (xi := (164950635505767 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12857 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12857]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12857])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12857) (a := (83899266326587 / 100000000000000 : ℝ)) (b := (160185120559 / 100000000000000 : ℝ)) (q := (446523039727 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12857])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12857])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12857]

theorem cert12857_6 : CellCertificate 12857 (220588975400047 / 2500000000000000 : ℝ) (102105586313581 / 62500000000000000 : ℝ) (164950635505767 / 5000000000000000 : ℝ)
    (cell12857 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · have h := gap_lower (n := 12857) (a := (83864465061943 / 100000000000000 : ℝ)) (b := (160185120559 / 100000000000000 : ℝ)) (q := (223261916913 / 10000000000000 : ℝ))
      (E := (cell12857 ⟨6, by decide⟩).energy) (xi := (164950635505767 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12857 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12857]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12857])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12857) (a := (83864465061943 / 100000000000000 : ℝ)) (b := (160185120559 / 100000000000000 : ℝ)) (q := (223261916913 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12857])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12857])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12857]

theorem cert12857_7 : CellCertificate 12857 (220588975400047 / 2500000000000000 : ℝ) (102105586313581 / 62500000000000000 : ℝ) (164950635505767 / 5000000000000000 : ℝ)
    (cell12857 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · have h := gap_lower (n := 12857) (a := (20957422120347 / 25000000000000 : ℝ)) (b := (160185120559 / 100000000000000 : ℝ)) (q := (111631160359 / 5000000000000 : ℝ))
      (E := (cell12857 ⟨7, by decide⟩).energy) (xi := (164950635505767 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12857 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12857]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12857])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12857) (a := (20957422120347 / 25000000000000 : ℝ)) (b := (160185120559 / 100000000000000 : ℝ)) (q := (111631160359 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12857])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12857])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12857]

theorem cert12857_8 : CellCertificate 12857 (220588975400047 / 2500000000000000 : ℝ) (102105586313581 / 62500000000000000 : ℝ) (164950635505767 / 5000000000000000 : ℝ)
    (cell12857 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · have h := gap_lower (n := 12857) (a := (83794936549519 / 100000000000000 : ℝ)) (b := (160185120559 / 100000000000000 : ℝ)) (q := (2232627204109 / 100000000000000 : ℝ))
      (E := (cell12857 ⟨8, by decide⟩).energy) (xi := (164950635505767 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12857 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12857]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12857])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12857) (a := (83794936549519 / 100000000000000 : ℝ)) (b := (160185120559 / 100000000000000 : ℝ)) (q := (2232627204109 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12857])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12857])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12857]

theorem cert12857_9 : CellCertificate 12857 (220588975400047 / 2500000000000000 : ℝ) (102105586313581 / 62500000000000000 : ℝ) (164950635505767 / 5000000000000000 : ℝ)
    (cell12857 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · have h := gap_lower (n := 12857) (a := (41880104615559 / 50000000000000 : ℝ)) (b := (160185120559 / 100000000000000 : ℝ)) (q := (2232631166873 / 100000000000000 : ℝ))
      (E := (cell12857 ⟨9, by decide⟩).energy) (xi := (164950635505767 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12857 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12857]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12857])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12857) (a := (41880104615559 / 50000000000000 : ℝ)) (b := (160185120559 / 100000000000000 : ℝ)) (q := (2232631166873 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12857])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12857])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12857]

theorem cert12857_10 : CellCertificate 12857 (220588975400047 / 2500000000000000 : ℝ) (102105586313581 / 62500000000000000 : ℝ) (164950635505767 / 5000000000000000 : ℝ)
    (cell12857 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · have h := gap_lower (n := 12857) (a := (5232844155697 / 6250000000000 : ℝ)) (b := (160185120559 / 100000000000000 : ℝ)) (q := (558158790059 / 25000000000000 : ℝ))
      (E := (cell12857 ⟨10, by decide⟩).energy) (xi := (164950635505767 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12857 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12857]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12857])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12857) (a := (5232844155697 / 6250000000000 : ℝ)) (b := (160185120559 / 100000000000000 : ℝ)) (q := (558158790059 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12857])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12857])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12857]

theorem cert12857_11 : CellCertificate 12857 (220588975400047 / 2500000000000000 : ℝ) (102105586313581 / 62500000000000000 : ℝ) (164950635505767 / 5000000000000000 : ℝ)
    (cell12857 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · have h := gap_lower (n := 12857) (a := (83690828294771 / 100000000000000 : ℝ)) (b := (160185120559 / 100000000000000 : ℝ)) (q := (89305567629 / 4000000000000 : ℝ))
      (E := (cell12857 ⟨11, by decide⟩).energy) (xi := (164950635505767 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12857 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12857]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12857])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12857) (a := (83690828294771 / 100000000000000 : ℝ)) (b := (160185120559 / 100000000000000 : ℝ)) (q := (89305567629 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12857])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12857])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12857]

theorem cert12857_12 : CellCertificate 12857 (220588975400047 / 2500000000000000 : ℝ) (102105586313581 / 62500000000000000 : ℝ) (164950635505767 / 5000000000000000 : ℝ)
    (cell12857 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · have h := gap_lower (n := 12857) (a := (16731234921461 / 20000000000000 : ℝ)) (b := (160185120559 / 100000000000000 : ℝ)) (q := (223264320651 / 10000000000000 : ℝ))
      (E := (cell12857 ⟨12, by decide⟩).energy) (xi := (164950635505767 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12857 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12857]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12857])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12857) (a := (16731234921461 / 20000000000000 : ℝ)) (b := (160185120559 / 100000000000000 : ℝ)) (q := (223264320651 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12857])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12857])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12857]

theorem cert12857_13 : CellCertificate 12857 (220588975400047 / 2500000000000000 : ℝ) (102105586313581 / 62500000000000000 : ℝ) (164950635505767 / 5000000000000000 : ℝ)
    (cell12857 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · have h := gap_lower (n := 12857) (a := (16724309078853 / 20000000000000 : ℝ)) (b := (160185120559 / 100000000000000 : ℝ)) (q := (2232647213553 / 100000000000000 : ℝ))
      (E := (cell12857 ⟨13, by decide⟩).energy) (xi := (164950635505767 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12857 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12857]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12857])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12857) (a := (16724309078853 / 20000000000000 : ℝ)) (b := (160185120559 / 100000000000000 : ℝ)) (q := (2232647213553 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12857])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12857])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12857]

theorem cert12857_14 : CellCertificate 12857 (220588975400047 / 2500000000000000 : ℝ) (102105586313581 / 62500000000000000 : ℝ) (164950635505767 / 5000000000000000 : ℝ)
    (cell12857 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · have h := gap_lower (n := 12857) (a := (83586940621341 / 100000000000000 : ℝ)) (b := (160185120559 / 100000000000000 : ℝ)) (q := (69770350549 / 3125000000000 : ℝ))
      (E := (cell12857 ⟨14, by decide⟩).energy) (xi := (164950635505767 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12857 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12857]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12857])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12857) (a := (83586940621341 / 100000000000000 : ℝ)) (b := (160185120559 / 100000000000000 : ℝ)) (q := (69770350549 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12857])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12857])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12857]

theorem cert12857_15 : CellCertificate 12857 (220588975400047 / 2500000000000000 : ℝ) (102105586313581 / 62500000000000000 : ℝ) (164950635505767 / 5000000000000000 : ℝ)
    (cell12857 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · have h := gap_lower (n := 12857) (a := (41776180127201 / 50000000000000 : ℝ)) (b := (160185120559 / 100000000000000 : ℝ)) (q := (89306208961 / 4000000000000 : ℝ))
      (E := (cell12857 ⟨15, by decide⟩).energy) (xi := (164950635505767 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12857 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12857]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12857])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12857) (a := (41776180127201 / 50000000000000 : ℝ)) (b := (160185120559 / 100000000000000 : ℝ)) (q := (89306208961 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12857])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12857])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12857]

theorem cert12857_16 : CellCertificate 12857 (220588975400047 / 2500000000000000 : ℝ) (102105586313581 / 62500000000000000 : ℝ) (164950635505767 / 5000000000000000 : ℝ)
    (cell12857 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · have h := gap_lower (n := 12857) (a := (41758902129747 / 50000000000000 : ℝ)) (b := (160185120559 / 100000000000000 : ℝ)) (q := (2232659179947 / 100000000000000 : ℝ))
      (E := (cell12857 ⟨16, by decide⟩).energy) (xi := (164950635505767 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12857 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12857]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12857])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12857) (a := (41758902129747 / 50000000000000 : ℝ)) (b := (160185120559 / 100000000000000 : ℝ)) (q := (2232659179947 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12857])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12857])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12857]

theorem cert12857_17 : CellCertificate 12857 (220588975400047 / 2500000000000000 : ℝ) (102105586313581 / 62500000000000000 : ℝ) (164950635505767 / 5000000000000000 : ℝ)
    (cell12857 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · have h := gap_lower (n := 12857) (a := (20870818150709 / 25000000000000 : ℝ)) (b := (160185120559 / 100000000000000 : ℝ)) (q := (1116331603349 / 50000000000000 : ℝ))
      (E := (cell12857 ⟨17, by decide⟩).energy) (xi := (164950635505767 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12857 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12857]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12857])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12857) (a := (20870818150709 / 25000000000000 : ℝ)) (b := (160185120559 / 100000000000000 : ℝ)) (q := (1116331603349 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12857])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12857])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12857]

theorem cert12857_18 : CellCertificate 12857 (220588975400047 / 2500000000000000 : ℝ) (102105586313581 / 62500000000000000 : ℝ) (164950635505767 / 5000000000000000 : ℝ)
    (cell12857 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · have h := gap_lower (n := 12857) (a := (3337950610033 / 4000000000000 : ℝ)) (b := (160185120559 / 100000000000000 : ℝ)) (q := (139541699537 / 6250000000000 : ℝ))
      (E := (cell12857 ⟨18, by decide⟩).energy) (xi := (164950635505767 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12857 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12857]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12857])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12857) (a := (3337950610033 / 4000000000000 : ℝ)) (b := (160185120559 / 100000000000000 : ℝ)) (q := (139541699537 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12857])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12857])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12857]

theorem cert12857_19 : CellCertificate 12857 (220588975400047 / 2500000000000000 : ℝ) (102105586313581 / 62500000000000000 : ℝ) (164950635505767 / 5000000000000000 : ℝ)
    (cell12857 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · have h := gap_lower (n := 12857) (a := (8341428217003 / 10000000000000 : ℝ)) (b := (160185120559 / 100000000000000 : ℝ)) (q := (2232671200331 / 100000000000000 : ℝ))
      (E := (cell12857 ⟨19, by decide⟩).energy) (xi := (164950635505767 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12857 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12857]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12857])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12857) (a := (8341428217003 / 10000000000000 : ℝ)) (b := (160185120559 / 100000000000000 : ℝ)) (q := (2232671200331 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12857])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12857])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12857]

theorem cert12858_0 : CellCertificate 12858 (441164308964399 / 5000000000000000 : ℝ) (1633562283496339 / 1000000000000000000 : ℝ) (41234375471149 / 1250000000000000 : ℝ)
    (cell12858 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · have h := gap_lower (n := 12858) (a := (2627300918841 / 3125000000000 : ℝ)) (b := (160172514461 / 100000000000000 : ℝ)) (q := (1116238633529 / 50000000000000 : ℝ))
      (E := (cell12858 ⟨0, by decide⟩).energy) (xi := (41234375471149 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12858 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12858]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12858])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12858) (a := (2627300918841 / 3125000000000 : ℝ)) (b := (160172514461 / 100000000000000 : ℝ)) (q := (1116238633529 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12858])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12858])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12858]

theorem cert12858_1 : CellCertificate 12858 (441164308964399 / 5000000000000000 : ℝ) (1633562283496339 / 1000000000000000000 : ℝ) (41234375471149 / 1250000000000000 : ℝ)
    (cell12858 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · have h := gap_lower (n := 12858) (a := (5252419030891 / 6250000000000 : ℝ)) (b := (160172514461 / 100000000000000 : ℝ)) (q := (17859850257 / 800000000000 : ℝ))
      (E := (cell12858 ⟨1, by decide⟩).energy) (xi := (41234375471149 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12858 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12858]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12858])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12858) (a := (5252419030891 / 6250000000000 : ℝ)) (b := (160172514461 / 100000000000000 : ℝ)) (q := (17859850257 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12858])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12858])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12858]

theorem cert12858_2 : CellCertificate 12858 (441164308964399 / 5000000000000000 : ℝ) (1633562283496339 / 1000000000000000000 : ℝ) (41234375471149 / 1250000000000000 : ℝ)
    (cell12858 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · have h := gap_lower (n := 12858) (a := (84003804449077 / 100000000000000 : ℝ)) (b := (160172514461 / 100000000000000 : ℝ)) (q := (2232485267273 / 100000000000000 : ℝ))
      (E := (cell12858 ⟨2, by decide⟩).energy) (xi := (41234375471149 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12858 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12858]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12858])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12858) (a := (84003804449077 / 100000000000000 : ℝ)) (b := (160172514461 / 100000000000000 : ℝ)) (q := (2232485267273 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12858])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12858])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12858]

theorem cert12858_3 : CellCertificate 12858 (441164308964399 / 5000000000000000 : ℝ) (1633562283496339 / 1000000000000000000 : ℝ) (41234375471149 / 1250000000000000 : ℝ)
    (cell12858 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · have h := gap_lower (n := 12858) (a := (20992232307757 / 25000000000000 : ℝ)) (b := (160172514461 / 100000000000000 : ℝ)) (q := (2232489288951 / 100000000000000 : ℝ))
      (E := (cell12858 ⟨3, by decide⟩).energy) (xi := (41234375471149 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12858 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12858]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12858])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12858) (a := (20992232307757 / 25000000000000 : ℝ)) (b := (160172514461 / 100000000000000 : ℝ)) (q := (2232489288951 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12858])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12858])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12858]

theorem cert12858_4 : CellCertificate 12858 (441164308964399 / 5000000000000000 : ℝ) (1633562283496339 / 1000000000000000000 : ℝ) (41234375471149 / 1250000000000000 : ℝ)
    (cell12858 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · have h := gap_lower (n := 12858) (a := (83934078803957 / 100000000000000 : ℝ)) (b := (160172514461 / 100000000000000 : ℝ)) (q := (558123324401 / 25000000000000 : ℝ))
      (E := (cell12858 ⟨4, by decide⟩).energy) (xi := (41234375471149 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12858 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12858]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12858])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12858) (a := (83934078803957 / 100000000000000 : ℝ)) (b := (160172514461 / 100000000000000 : ℝ)) (q := (558123324401 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12858])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12858])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12858]

theorem cert12858_5 : CellCertificate 12858 (441164308964399 / 5000000000000000 : ℝ) (1633562283496339 / 1000000000000000000 : ℝ) (41234375471149 / 1250000000000000 : ℝ)
    (cell12858 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · have h := gap_lower (n := 12858) (a := (41949626565949 / 50000000000000 : ℝ)) (b := (160172514461 / 100000000000000 : ℝ)) (q := (279062162659 / 12500000000000 : ℝ))
      (E := (cell12858 ⟨5, by decide⟩).energy) (xi := (41234375471149 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12858 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12858]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12858])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12858) (a := (41949626565949 / 50000000000000 : ℝ)) (b := (160172514461 / 100000000000000 : ℝ)) (q := (279062162659 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12858])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12858])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12858]

theorem cert12858_6 : CellCertificate 12858 (441164308964399 / 5000000000000000 : ℝ) (1633562283496339 / 1000000000000000000 : ℝ) (41234375471149 / 1250000000000000 : ℝ)
    (cell12858 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · have h := gap_lower (n := 12858) (a := (83864452179077 / 100000000000000 : ℝ)) (b := (160172514461 / 100000000000000 : ℝ)) (q := (2232501307737 / 100000000000000 : ℝ))
      (E := (cell12858 ⟨6, by decide⟩).energy) (xi := (41234375471149 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12858 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12858]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12858])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12858) (a := (83864452179077 / 100000000000000 : ℝ)) (b := (160172514461 / 100000000000000 : ℝ)) (q := (2232501307737 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12858])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12858])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12858]

theorem cert12858_7 : CellCertificate 12858 (441164308964399 / 5000000000000000 : ℝ) (1633562283496339 / 1000000000000000000 : ℝ) (41234375471149 / 1250000000000000 : ℝ)
    (cell12858 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · have h := gap_lower (n := 12858) (a := (16765935181981 / 20000000000000 : ℝ)) (b := (160172514461 / 100000000000000 : ℝ)) (q := (2232505324531 / 100000000000000 : ℝ))
      (E := (cell12858 ⟨7, by decide⟩).energy) (xi := (41234375471149 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12858 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12858]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12858])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12858) (a := (16765935181981 / 20000000000000 : ℝ)) (b := (160172514461 / 100000000000000 : ℝ)) (q := (2232505324531 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12858])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12858])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12858]

theorem cert12858_8 : CellCertificate 12858 (441164308964399 / 5000000000000000 : ℝ) (1633562283496339 / 1000000000000000000 : ℝ) (41234375471149 / 1250000000000000 : ℝ)
    (cell12858 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · have h := gap_lower (n := 12858) (a := (83794924288981 / 100000000000000 : ℝ)) (b := (160172514461 / 100000000000000 : ℝ)) (q := (558127325229 / 25000000000000 : ℝ))
      (E := (cell12858 ⟨8, by decide⟩).energy) (xi := (41234375471149 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12858 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12858]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12858])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12858) (a := (83794924288981 / 100000000000000 : ℝ)) (b := (160172514461 / 100000000000000 : ℝ)) (q := (558127325229 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12858])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12858])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12858]

theorem cert12858_9 : CellCertificate 12858 (441164308964399 / 5000000000000000 : ℝ) (1633562283496339 / 1000000000000000000 : ℝ) (41234375471149 / 1250000000000000 : ℝ)
    (cell12858 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · have h := gap_lower (n := 12858) (a := (83760197281089 / 100000000000000 : ℝ)) (b := (160172514461 / 100000000000000 : ℝ)) (q := (2232513301883 / 100000000000000 : ℝ))
      (E := (cell12858 ⟨9, by decide⟩).energy) (xi := (41234375471149 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12858 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12858]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12858])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12858) (a := (83760197281089 / 100000000000000 : ℝ)) (b := (160172514461 / 100000000000000 : ℝ)) (q := (2232513301883 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12858])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12858])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12858]

theorem cert12858_10 : CellCertificate 12858 (441164308964399 / 5000000000000000 : ℝ) (1633562283496339 / 1000000000000000000 : ℝ) (41234375471149 / 1250000000000000 : ℝ)
    (cell12858 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · have h := gap_lower (n := 12858) (a := (20931373712799 / 25000000000000 : ℝ)) (b := (160172514461 / 100000000000000 : ℝ)) (q := (2232517334207 / 100000000000000 : ℝ))
      (E := (cell12858 ⟨10, by decide⟩).energy) (xi := (41234375471149 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12858 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12858]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12858])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12858) (a := (20931373712799 / 25000000000000 : ℝ)) (b := (160172514461 / 100000000000000 : ℝ)) (q := (2232517334207 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12858])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12858])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12858]

theorem cert12858_11 : CellCertificate 12858 (441164308964399 / 5000000000000000 : ℝ) (1633562283496339 / 1000000000000000000 : ℝ) (41234375471149 / 1250000000000000 : ℝ)
    (cell12858 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · have h := gap_lower (n := 12858) (a := (83690816964453 / 100000000000000 : ℝ)) (b := (160172514461 / 100000000000000 : ℝ)) (q := (2232521288247 / 100000000000000 : ℝ))
      (E := (cell12858 ⟨11, by decide⟩).energy) (xi := (41234375471149 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12858 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12858]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12858])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12858) (a := (83690816964453 / 100000000000000 : ℝ)) (b := (160172514461 / 100000000000000 : ℝ)) (q := (2232521288247 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12858])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12858])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12858]

theorem cert12858_12 : CellCertificate 12858 (441164308964399 / 5000000000000000 : ℝ) (1633562283496339 / 1000000000000000000 : ℝ) (41234375471149 / 1250000000000000 : ℝ)
    (cell12858 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · have h := gap_lower (n := 12858) (a := (8365616358619 / 10000000000000 : ℝ)) (b := (160172514461 / 100000000000000 : ℝ)) (q := (111626267223 / 5000000000000 : ℝ))
      (E := (cell12858 ⟨12, by decide⟩).energy) (xi := (41234375471149 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12858 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12858]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12858])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12858) (a := (8365616358619 / 10000000000000 : ℝ)) (b := (160172514461 / 100000000000000 : ℝ)) (q := (111626267223 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12858])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12858])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12858]

theorem cert12858_13 : CellCertificate 12858 (441164308964399 / 5000000000000000 : ℝ) (1633562283496339 / 1000000000000000000 : ℝ) (41234375471149 / 1250000000000000 : ℝ)
    (cell12858 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · have h := gap_lower (n := 12858) (a := (83621534681921 / 100000000000000 : ℝ)) (b := (160172514461 / 100000000000000 : ℝ)) (q := (446505866911 / 20000000000000 : ℝ))
      (E := (cell12858 ⟨13, by decide⟩).energy) (xi := (41234375471149 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12858 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12858]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12858])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12858) (a := (83621534681921 / 100000000000000 : ℝ)) (b := (160172514461 / 100000000000000 : ℝ)) (q := (446505866911 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12858])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12858])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12858]

theorem cert12858_14 : CellCertificate 12858 (441164308964399 / 5000000000000000 : ℝ) (1633562283496339 / 1000000000000000000 : ℝ) (41234375471149 / 1250000000000000 : ℝ)
    (cell12858 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · have h := gap_lower (n := 12858) (a := (16717386043467 / 20000000000000 : ℝ)) (b := (160172514461 / 100000000000000 : ℝ)) (q := (223253332233 / 10000000000000 : ℝ))
      (E := (cell12858 ⟨14, by decide⟩).energy) (xi := (41234375471149 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12858 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12858]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12858])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12858) (a := (16717386043467 / 20000000000000 : ℝ)) (b := (160172514461 / 100000000000000 : ℝ)) (q := (223253332233 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12858])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12858])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12858]

theorem cert12858_15 : CellCertificate 12858 (441164308964399 / 5000000000000000 : ℝ) (1633562283496339 / 1000000000000000000 : ℝ) (41234375471149 / 1250000000000000 : ℝ)
    (cell12858 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · have h := gap_lower (n := 12858) (a := (83552350158303 / 100000000000000 : ℝ)) (b := (160172514461 / 100000000000000 : ℝ)) (q := (558134328313 / 25000000000000 : ℝ))
      (E := (cell12858 ⟨15, by decide⟩).energy) (xi := (41234375471149 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12858 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12858]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12858])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12858) (a := (83552350158303 / 100000000000000 : ℝ)) (b := (160172514461 / 100000000000000 : ℝ)) (q := (558134328313 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12858])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12858])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12858]

theorem cert12858_16 : CellCertificate 12858 (441164308964399 / 5000000000000000 : ℝ) (1633562283496339 / 1000000000000000000 : ℝ) (41234375471149 / 1250000000000000 : ℝ)
    (cell12858 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · have h := gap_lower (n := 12858) (a := (83517794470871 / 100000000000000 : ℝ)) (b := (160172514461 / 100000000000000 : ℝ)) (q := (2232541312547 / 100000000000000 : ℝ))
      (E := (cell12858 ⟨16, by decide⟩).energy) (xi := (41234375471149 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12858 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12858]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12858])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12858) (a := (83517794470871 / 100000000000000 : ℝ)) (b := (160172514461 / 100000000000000 : ℝ)) (q := (2232541312547 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12858])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12858])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12858]

theorem cert12858_17 : CellCertificate 12858 (441164308964399 / 5000000000000000 : ℝ) (1633562283496339 / 1000000000000000000 : ℝ) (41234375471149 / 1250000000000000 : ℝ)
    (cell12858 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · have h := gap_lower (n := 12858) (a := (83483263121261 / 100000000000000 : ℝ)) (b := (160172514461 / 100000000000000 : ℝ)) (q := (558136331299 / 25000000000000 : ℝ))
      (E := (cell12858 ⟨17, by decide⟩).energy) (xi := (41234375471149 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12858 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12858]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12858])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12858) (a := (83483263121261 / 100000000000000 : ℝ)) (b := (160172514461 / 100000000000000 : ℝ)) (q := (558136331299 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12858])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12858])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12858]

theorem cert12858_18 : CellCertificate 12858 (441164308964399 / 5000000000000000 : ℝ) (1633562283496339 / 1000000000000000000 : ℝ) (41234375471149 / 1250000000000000 : ℝ)
    (cell12858 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · have h := gap_lower (n := 12858) (a := (20862189018967 / 25000000000000 : ℝ)) (b := (160172514461 / 100000000000000 : ℝ)) (q := (2232549355941 / 100000000000000 : ℝ))
      (E := (cell12858 ⟨18, by decide⟩).energy) (xi := (41234375471149 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12858 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12858]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12858])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12858) (a := (20862189018967 / 25000000000000 : ℝ)) (b := (160172514461 / 100000000000000 : ℝ)) (q := (2232549355941 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12858])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12858])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12858]

theorem cert12858_19 : CellCertificate 12858 (441164308964399 / 5000000000000000 : ℝ) (1633562283496339 / 1000000000000000000 : ℝ) (41234375471149 / 1250000000000000 : ℝ)
    (cell12858 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · have h := gap_lower (n := 12858) (a := (83414273301263 / 100000000000000 : ℝ)) (b := (160172514461 / 100000000000000 : ℝ)) (q := (223255335101 / 10000000000000 : ℝ))
      (E := (cell12858 ⟨19, by decide⟩).energy) (xi := (41234375471149 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12858 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12858]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12858])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12858) (a := (83414273301263 / 100000000000000 : ℝ)) (b := (160172514461 / 100000000000000 : ℝ)) (q := (223255335101 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12858])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12858])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12858]

theorem cert12859_0 : CellCertificate 12859 (8823013383269 / 100000000000000 : ℝ) (1633435205749669 / 1000000000000000000 : ℝ) (164924370377479 / 5000000000000000 : ℝ)
    (cell12859 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · have h := gap_lower (n := 12859) (a := (21018403661199 / 25000000000000 : ℝ)) (b := (80079955179 / 50000000000000 : ℝ)) (q := (2232359428041 / 100000000000000 : ℝ))
      (E := (cell12859 ⟨0, by decide⟩).energy) (xi := (164924370377479 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12859 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12859]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12859])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12859) (a := (21018403661199 / 25000000000000 : ℝ)) (b := (80079955179 / 50000000000000 : ℝ)) (q := (2232359428041 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12859])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12859])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12859]

theorem cert12859_1 : CellCertificate 12859 (8823013383269 / 100000000000000 : ℝ) (1633435205749669 / 1000000000000000000 : ℝ) (164924370377479 / 5000000000000000 : ℝ)
    (cell12859 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · have h := gap_lower (n := 12859) (a := (84038690050133 / 100000000000000 : ℝ)) (b := (80079955179 / 50000000000000 : ℝ)) (q := (2232363417547 / 100000000000000 : ℝ))
      (E := (cell12859 ⟨1, by decide⟩).energy) (xi := (164924370377479 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12859 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12859]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12859])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12859) (a := (84038690050133 / 100000000000000 : ℝ)) (b := (80079955179 / 50000000000000 : ℝ)) (q := (2232363417547 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12859])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12859])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12859]

theorem cert12859_2 : CellCertificate 12859 (8823013383269 / 100000000000000 : ℝ) (1633435205749669 / 1000000000000000000 : ℝ) (164924370377479 / 5000000000000000 : ℝ)
    (cell12859 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · have h := gap_lower (n := 12859) (a := (84003790318503 / 100000000000000 : ℝ)) (b := (80079955179 / 50000000000000 : ℝ)) (q := (558091858931 / 25000000000000 : ℝ))
      (E := (cell12859 ⟨2, by decide⟩).energy) (xi := (164924370377479 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12859 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12859]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12859])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12859) (a := (84003790318503 / 100000000000000 : ℝ)) (b := (80079955179 / 50000000000000 : ℝ)) (q := (558091858931 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12859])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12859])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12859]

theorem cert12859_3 : CellCertificate 12859 (8823013383269 / 100000000000000 : ℝ) (1633435205749669 / 1000000000000000000 : ℝ) (164924370377479 / 5000000000000000 : ℝ)
    (cell12859 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · have h := gap_lower (n := 12859) (a := (83968915413561 / 100000000000000 : ℝ)) (b := (80079955179 / 50000000000000 : ℝ)) (q := (22323714333 / 1000000000000 : ℝ))
      (E := (cell12859 ⟨3, by decide⟩).energy) (xi := (164924370377479 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12859 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12859]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12859])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12859) (a := (83968915413561 / 100000000000000 : ℝ)) (b := (80079955179 / 50000000000000 : ℝ)) (q := (22323714333 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12859])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12859])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12859]

theorem cert12859_4 : CellCertificate 12859 (8823013383269 / 100000000000000 : ℝ) (1633435205749669 / 1000000000000000000 : ℝ) (164924370377479 / 5000000000000000 : ℝ)
    (cell12859 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · have h := gap_lower (n := 12859) (a := (41967032649577 / 50000000000000 : ℝ)) (b := (80079955179 / 50000000000000 : ℝ)) (q := (2232375476487 / 100000000000000 : ℝ))
      (E := (cell12859 ⟨4, by decide⟩).energy) (xi := (164924370377479 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12859 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12859]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12859])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12859) (a := (41967032649577 / 50000000000000 : ℝ)) (b := (80079955179 / 50000000000000 : ℝ)) (q := (2232375476487 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12859])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12859])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12859]

theorem cert12859_5 : CellCertificate 12859 (8823013383269 / 100000000000000 : ℝ) (1633435205749669 / 1000000000000000000 : ℝ) (164924370377479 / 5000000000000000 : ℝ)
    (cell12859 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · have h := gap_lower (n := 12859) (a := (2097480998483 / 2500000000000 : ℝ)) (b := (80079955179 / 50000000000000 : ℝ)) (q := (2232379457507 / 100000000000000 : ℝ))
      (E := (cell12859 ⟨5, by decide⟩).energy) (xi := (164924370377479 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12859 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12859]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12859])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12859) (a := (2097480998483 / 2500000000000 : ℝ)) (b := (80079955179 / 50000000000000 : ℝ)) (q := (2232379457507 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12859])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12859])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12859]

theorem cert12859_6 : CellCertificate 12859 (8823013383269 / 100000000000000 : ℝ) (1633435205749669 / 1000000000000000000 : ℝ) (164924370377479 / 5000000000000000 : ℝ)
    (cell12859 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · have h := gap_lower (n := 12859) (a := (83864439298283 / 100000000000000 : ℝ)) (b := (80079955179 / 50000000000000 : ℝ)) (q := (55809586051 / 2500000000000 : ℝ))
      (E := (cell12859 ⟨6, by decide⟩).energy) (xi := (164924370377479 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12859 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12859]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12859])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12859) (a := (83864439298283 / 100000000000000 : ℝ)) (b := (80079955179 / 50000000000000 : ℝ)) (q := (55809586051 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12859])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12859])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12859]

theorem cert12859_7 : CellCertificate 12859 (8823013383269 / 100000000000000 : ℝ) (1633435205749669 / 1000000000000000000 : ℝ) (164924370377479 / 5000000000000000 : ℝ)
    (cell12859 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · have h := gap_lower (n := 12859) (a := (83829663340457 / 100000000000000 : ℝ)) (b := (80079955179 / 50000000000000 : ℝ)) (q := (1116193718807 / 50000000000000 : ℝ))
      (E := (cell12859 ⟨7, by decide⟩).energy) (xi := (164924370377479 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12859 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12859]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12859])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12859) (a := (83829663340457 / 100000000000000 : ℝ)) (b := (80079955179 / 50000000000000 : ℝ)) (q := (1116193718807 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12859])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12859])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12859]

theorem cert12859_8 : CellCertificate 12859 (8823013383269 / 100000000000000 : ℝ) (1633435205749669 / 1000000000000000000 : ℝ) (164924370377479 / 5000000000000000 : ℝ)
    (cell12859 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · have h := gap_lower (n := 12859) (a := (41897456015221 / 50000000000000 : ℝ)) (b := (80079955179 / 50000000000000 : ℝ)) (q := (446478290301 / 20000000000000 : ℝ))
      (E := (cell12859 ⟨8, by decide⟩).energy) (xi := (164924370377479 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12859 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12859]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12859])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12859) (a := (41897456015221 / 50000000000000 : ℝ)) (b := (80079955179 / 50000000000000 : ℝ)) (q := (446478290301 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12859])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12859])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12859]

theorem cert12859_9 : CellCertificate 12859 (8823013383269 / 100000000000000 : ℝ) (1633435205749669 / 1000000000000000000 : ℝ) (164924370377479 / 5000000000000000 : ℝ)
    (cell12859 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · have h := gap_lower (n := 12859) (a := (83760185333021 / 100000000000000 : ℝ)) (b := (80079955179 / 50000000000000 : ℝ)) (q := (2232395432701 / 100000000000000 : ℝ))
      (E := (cell12859 ⟨9, by decide⟩).energy) (xi := (164924370377479 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12859 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12859]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12859])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12859) (a := (83760185333021 / 100000000000000 : ℝ)) (b := (80079955179 / 50000000000000 : ℝ)) (q := (2232395432701 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12859])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12859])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12859]

theorem cert12859_10 : CellCertificate 12859 (8823013383269 / 100000000000000 : ℝ) (1633435205749669 / 1000000000000000000 : ℝ) (164924370377479 / 5000000000000000 : ℝ)
    (cell12859 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · have h := gap_lower (n := 12859) (a := (20931370803291 / 25000000000000 : ℝ)) (b := (80079955179 / 50000000000000 : ℝ)) (q := (446479889193 / 20000000000000 : ℝ))
      (E := (cell12859 ⟨10, by decide⟩).energy) (xi := (164924370377479 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12859 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12859]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12859])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12859) (a := (20931370803291 / 25000000000000 : ℝ)) (b := (80079955179 / 50000000000000 : ℝ)) (q := (446479889193 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12859])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12859])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12859]

theorem cert12859_11 : CellCertificate 12859 (8823013383269 / 100000000000000 : ℝ) (1633435205749669 / 1000000000000000000 : ℝ) (164924370377479 / 5000000000000000 : ℝ)
    (cell12859 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · have h := gap_lower (n := 12859) (a := (83690805636021 / 100000000000000 : ℝ)) (b := (80079955179 / 50000000000000 : ℝ)) (q := (1116201719869 / 50000000000000 : ℝ))
      (E := (cell12859 ⟨11, by decide⟩).energy) (xi := (164924370377479 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12859 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12859]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12859])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12859) (a := (83690805636021 / 100000000000000 : ℝ)) (b := (80079955179 / 50000000000000 : ℝ)) (q := (1116201719869 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12859])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12859])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12859]

theorem cert12859_12 : CellCertificate 12859 (8823013383269 / 100000000000000 : ℝ) (1633435205749669 / 1000000000000000000 : ℝ) (164924370377479 / 5000000000000000 : ℝ)
    (cell12859 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · have h := gap_lower (n := 12859) (a := (3346246102677 / 4000000000000 : ℝ)) (b := (80079955179 / 50000000000000 : ℝ)) (q := (558101869583 / 25000000000000 : ℝ))
      (E := (cell12859 ⟨12, by decide⟩).energy) (xi := (164924370377479 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12859 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12859]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12859])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12859) (a := (3346246102677 / 4000000000000 : ℝ)) (b := (80079955179 / 50000000000000 : ℝ)) (q := (558101869583 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12859])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12859])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12859]

theorem cert12859_13 : CellCertificate 12859 (8823013383269 / 100000000000000 : ℝ) (1633435205749669 / 1000000000000000000 : ℝ) (164924370377479 / 5000000000000000 : ℝ)
    (cell12859 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · have h := gap_lower (n := 12859) (a := (83621523971389 / 100000000000000 : ℝ)) (b := (80079955179 / 50000000000000 : ℝ)) (q := (1116205725759 / 50000000000000 : ℝ))
      (E := (cell12859 ⟨13, by decide⟩).energy) (xi := (164924370377479 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12859 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12859]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12859])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12859) (a := (83621523971389 / 100000000000000 : ℝ)) (b := (80079955179 / 50000000000000 : ℝ)) (q := (1116205725759 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12859])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12859])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12859]

theorem cert12859_14 : CellCertificate 12859 (8823013383269 / 100000000000000 : ℝ) (1633435205749669 / 1000000000000000000 : ℝ) (164924370377479 / 5000000000000000 : ℝ)
    (cell12859 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · have h := gap_lower (n := 12859) (a := (16717383963021 / 20000000000000 : ℝ)) (b := (80079955179 / 50000000000000 : ℝ)) (q := (2232415481243 / 100000000000000 : ℝ))
      (E := (cell12859 ⟨14, by decide⟩).energy) (xi := (164924370377479 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12859 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12859]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12859])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12859) (a := (16717383963021 / 20000000000000 : ℝ)) (b := (80079955179 / 50000000000000 : ℝ)) (q := (2232415481243 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12859])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12859])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12859]

theorem cert12859_15 : CellCertificate 12859 (8823013383269 / 100000000000000 : ℝ) (1633435205749669 / 1000000000000000000 : ℝ) (164924370377479 / 5000000000000000 : ℝ)
    (cell12859 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · have h := gap_lower (n := 12859) (a := (83552340063943 / 100000000000000 : ℝ)) (b := (80079955179 / 50000000000000 : ℝ)) (q := (558104864173 / 25000000000000 : ℝ))
      (E := (cell12859 ⟨15, by decide⟩).energy) (xi := (164924370377479 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12859 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12859]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12859])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12859) (a := (83552340063943 / 100000000000000 : ℝ)) (b := (80079955179 / 50000000000000 : ℝ)) (q := (558104864173 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12859])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12859])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12859]

theorem cert12859_16 : CellCertificate 12859 (8823013383269 / 100000000000000 : ℝ) (1633435205749669 / 1000000000000000000 : ℝ) (164924370377479 / 5000000000000000 : ℝ)
    (cell12859 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · have h := gap_lower (n := 12859) (a := (83517784683951 / 100000000000000 : ℝ)) (b := (80079955179 / 50000000000000 : ℝ)) (q := (2232423499419 / 100000000000000 : ℝ))
      (E := (cell12859 ⟨16, by decide⟩).energy) (xi := (164924370377479 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12859 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12859]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12859])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12859) (a := (83517784683951 / 100000000000000 : ℝ)) (b := (80079955179 / 50000000000000 : ℝ)) (q := (2232423499419 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12859])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12859])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12859]

theorem cert12859_17 : CellCertificate 12859 (8823013383269 / 100000000000000 : ℝ) (1633435205749669 / 1000000000000000000 : ℝ) (164924370377479 / 5000000000000000 : ℝ)
    (cell12859 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · have h := gap_lower (n := 12859) (a := (1669665072827 / 2000000000000 : ℝ)) (b := (80079955179 / 50000000000000 : ℝ)) (q := (223242749803 / 10000000000000 : ℝ))
      (E := (cell12859 ⟨17, by decide⟩).energy) (xi := (164924370377479 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12859 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12859]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12859])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12859) (a := (1669665072827 / 2000000000000 : ℝ)) (b := (80079955179 / 50000000000000 : ℝ)) (q := (223242749803 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12859])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12859])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12859]

theorem cert12859_18 : CellCertificate 12859 (8823013383269 / 100000000000000 : ℝ) (1633435205749669 / 1000000000000000000 : ℝ) (164924370377479 / 5000000000000000 : ℝ)
    (cell12859 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · have h := gap_lower (n := 12859) (a := (83448746902539 / 100000000000000 : ℝ)) (b := (80079955179 / 50000000000000 : ℝ)) (q := (2232431515439 / 100000000000000 : ℝ))
      (E := (cell12859 ⟨18, by decide⟩).energy) (xi := (164924370377479 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12859 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12859]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12859])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12859) (a := (83448746902539 / 100000000000000 : ℝ)) (b := (80079955179 / 50000000000000 : ℝ)) (q := (2232431515439 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12859])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12859])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12859]

theorem cert12859_19 : CellCertificate 12859 (8823013383269 / 100000000000000 : ℝ) (1633435205749669 / 1000000000000000000 : ℝ) (164924370377479 / 5000000000000000 : ℝ)
    (cell12859 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · have h := gap_lower (n := 12859) (a := (10426783054261 / 12500000000000 : ℝ)) (b := (80079955179 / 50000000000000 : ℝ)) (q := (558108874469 / 25000000000000 : ℝ))
      (E := (cell12859 ⟨19, by decide⟩).energy) (xi := (164924370377479 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12859 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12859]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12859])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12859) (a := (10426783054261 / 12500000000000 : ℝ)) (b := (80079955179 / 50000000000000 : ℝ)) (q := (558108874469 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12859])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12859])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12859]

theorem cert12860_0 : CellCertificate 12860 (44113703139677 / 500000000000000 : ℝ) (6380109952237 / 3906250000000000 : ℝ) (329822481967737 / 10000000000000000 : ℝ)
    (cell12860 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · have h := gap_lower (n := 12860) (a := (84073599888979 / 100000000000000 : ℝ)) (b := (640589233 / 400000000000 : ℝ)) (q := (1116120821157 / 50000000000000 : ℝ))
      (E := (cell12860 ⟨0, by decide⟩).energy) (xi := (329822481967737 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12860 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12860]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12860])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12860) (a := (84073599888979 / 100000000000000 : ℝ)) (b := (640589233 / 400000000000 : ℝ)) (q := (1116120821157 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12860])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12860])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12860]

theorem cert12860_1 : CellCertificate 12860 (44113703139677 / 500000000000000 : ℝ) (6380109952237 / 3906250000000000 : ℝ) (329822481967737 / 10000000000000000 : ℝ)
    (cell12860 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · have h := gap_lower (n := 12860) (a := (84038675608271 / 100000000000000 : ℝ)) (b := (640589233 / 400000000000 : ℝ)) (q := (2232245606319 / 100000000000000 : ℝ))
      (E := (cell12860 ⟨1, by decide⟩).energy) (xi := (329822481967737 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12860 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12860]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12860])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12860) (a := (84038675608271 / 100000000000000 : ℝ)) (b := (640589233 / 400000000000 : ℝ)) (q := (2232245606319 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12860])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12860])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12860]

theorem cert12860_2 : CellCertificate 12860 (44113703139677 / 500000000000000 : ℝ) (6380109952237 / 3906250000000000 : ℝ) (329822481967737 / 10000000000000000 : ℝ)
    (cell12860 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · have h := gap_lower (n := 12860) (a := (10500472023769 / 12500000000000 : ℝ)) (b := (640589233 / 400000000000 : ℝ)) (q := (558062399929 / 25000000000000 : ℝ))
      (E := (cell12860 ⟨2, by decide⟩).energy) (xi := (329822481967737 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12860 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12860]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12860])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12860) (a := (10500472023769 / 12500000000000 : ℝ)) (b := (640589233 / 400000000000 : ℝ)) (q := (558062399929 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12860])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12860])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12860]

theorem cert12860_3 : CellCertificate 12860 (44113703139677 / 500000000000000 : ℝ) (6380109952237 / 3906250000000000 : ℝ) (329822481967737 / 10000000000000000 : ℝ)
    (cell12860 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · have h := gap_lower (n := 12860) (a := (83968901598279 / 100000000000000 : ℝ)) (b := (640589233 / 400000000000 : ℝ)) (q := (2232253631123 / 100000000000000 : ℝ))
      (E := (cell12860 ⟨3, by decide⟩).energy) (xi := (329822481967737 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12860 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12860]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12860])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12860) (a := (83968901598279 / 100000000000000 : ℝ)) (b := (640589233 / 400000000000 : ℝ)) (q := (2232253631123 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12860])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12860])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12860]

theorem cert12860_4 : CellCertificate 12860 (44113703139677 / 500000000000000 : ℝ) (6380109952237 / 3906250000000000 : ℝ) (329822481967737 / 10000000000000000 : ℝ)
    (cell12860 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · have h := gap_lower (n := 12860) (a := (167868103593 / 200000000000 : ℝ)) (b := (640589233 / 400000000000 : ℝ)) (q := (1116128825493 / 50000000000000 : ℝ))
      (E := (cell12860 ⟨4, by decide⟩).energy) (xi := (329822481967737 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12860 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12860]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12860])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12860) (a := (167868103593 / 200000000000 : ℝ)) (b := (640589233 / 400000000000 : ℝ)) (q := (1116128825493 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12860])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12860])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12860]

theorem cert12860_5 : CellCertificate 12860 (44113703139677 / 500000000000000 : ℝ) (6380109952237 / 3906250000000000 : ℝ) (329822481967737 / 10000000000000000 : ℝ)
    (cell12860 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · have h := gap_lower (n := 12860) (a := (20974806687213 / 25000000000000 : ℝ)) (b := (640589233 / 400000000000 : ℝ)) (q := (1116130804699 / 50000000000000 : ℝ))
      (E := (cell12860 ⟨5, by decide⟩).energy) (xi := (329822481967737 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12860 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12860]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12860])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12860) (a := (20974806687213 / 25000000000000 : ℝ)) (b := (640589233 / 400000000000 : ℝ)) (q := (1116130804699 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12860])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12860])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12860]

theorem cert12860_6 : CellCertificate 12860 (44113703139677 / 500000000000000 : ℝ) (6380109952237 / 3906250000000000 : ℝ) (329822481967737 / 10000000000000000 : ℝ)
    (cell12860 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · have h := gap_lower (n := 12860) (a := (41932213209781 / 50000000000000 : ℝ)) (b := (640589233 / 400000000000 : ℝ)) (q := (2232265630003 / 100000000000000 : ℝ))
      (E := (cell12860 ⟨6, by decide⟩).energy) (xi := (329822481967737 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12860 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12860]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12860])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12860) (a := (41932213209781 / 50000000000000 : ℝ)) (b := (640589233 / 400000000000 : ℝ)) (q := (2232265630003 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12860])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12860])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12860]

theorem cert12860_7 : CellCertificate 12860 (44113703139677 / 500000000000000 : ℝ) (6380109952237 / 3906250000000000 : ℝ) (329822481967737 / 10000000000000000 : ℝ)
    (cell12860 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · have h := gap_lower (n := 12860) (a := (16765930154609 / 20000000000000 : ℝ)) (b := (640589233 / 400000000000 : ℝ)) (q := (2232269662409 / 100000000000000 : ℝ))
      (E := (cell12860 ⟨7, by decide⟩).energy) (xi := (329822481967737 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12860 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12860]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12860])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12860) (a := (16765930154609 / 20000000000000 : ℝ)) (b := (640589233 / 400000000000 : ℝ)) (q := (2232269662409 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12860])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12860])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12860]

theorem cert12860_8 : CellCertificate 12860 (44113703139677 / 500000000000000 : ℝ) (6380109952237 / 3906250000000000 : ℝ) (329822481967737 / 10000000000000000 : ℝ)
    (cell12860 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · have h := gap_lower (n := 12860) (a := (83794899773901 / 100000000000000 : ℝ)) (b := (640589233 / 400000000000 : ℝ)) (q := (1116136827939 / 50000000000000 : ℝ))
      (E := (cell12860 ⟨8, by decide⟩).energy) (xi := (329822481967737 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12860 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12860]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12860])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12860) (a := (83794899773901 / 100000000000000 : ℝ)) (b := (640589233 / 400000000000 : ℝ)) (q := (1116136827939 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12860])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12860])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12860]

theorem cert12860_9 : CellCertificate 12860 (44113703139677 / 500000000000000 : ℝ) (6380109952237 / 3906250000000000 : ℝ) (329822481967737 / 10000000000000000 : ℝ)
    (cell12860 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · have h := gap_lower (n := 12860) (a := (41880086693457 / 50000000000000 : ℝ)) (b := (640589233 / 400000000000 : ℝ)) (q := (446455523473 / 20000000000000 : ℝ))
      (E := (cell12860 ⟨9, by decide⟩).energy) (xi := (329822481967737 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12860 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12860]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12860])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12860) (a := (41880086693457 / 50000000000000 : ℝ)) (b := (640589233 / 400000000000 : ℝ)) (q := (446455523473 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12860])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12860])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12860]

theorem cert12860_10 : CellCertificate 12860 (44113703139677 / 500000000000000 : ℝ) (6380109952237 / 3906250000000000 : ℝ) (329822481967737 / 10000000000000000 : ℝ)
    (cell12860 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · have h := gap_lower (n := 12860) (a := (16745094315411 / 20000000000000 : ℝ)) (b := (640589233 / 400000000000 : ℝ)) (q := (2232281669689 / 100000000000000 : ℝ))
      (E := (cell12860 ⟨10, by decide⟩).energy) (xi := (329822481967737 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12860 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12860]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12860])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12860) (a := (16745094315411 / 20000000000000 : ℝ)) (b := (640589233 / 400000000000 : ℝ)) (q := (2232281669689 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12860])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12860])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12860]

theorem cert12860_11 : CellCertificate 12860 (44113703139677 / 500000000000000 : ℝ) (6380109952237 / 3906250000000000 : ℝ) (329822481967737 / 10000000000000000 : ℝ)
    (cell12860 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · have h := gap_lower (n := 12860) (a := (20922698577369 / 25000000000000 : ℝ)) (b := (640589233 / 400000000000 : ℝ)) (q := (558071411299 / 25000000000000 : ℝ))
      (E := (cell12860 ⟨11, by decide⟩).energy) (xi := (329822481967737 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12860 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12860]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12860])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12860) (a := (20922698577369 / 25000000000000 : ℝ)) (b := (640589233 / 400000000000 : ℝ)) (q := (558071411299 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12860])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12860])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12860]

theorem cert12860_12 : CellCertificate 12860 (44113703139677 / 500000000000000 : ℝ) (6380109952237 / 3906250000000000 : ℝ) (329822481967737 / 10000000000000000 : ℝ)
    (cell12860 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · have h := gap_lower (n := 12860) (a := (83656141549509 / 100000000000000 : ℝ)) (b := (640589233 / 400000000000 : ℝ)) (q := (446457933247 / 20000000000000 : ℝ))
      (E := (cell12860 ⟨12, by decide⟩).energy) (xi := (329822481967737 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12860 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12860]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12860])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12860) (a := (83656141549509 / 100000000000000 : ℝ)) (b := (640589233 / 400000000000 : ℝ)) (q := (446457933247 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12860])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12860])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12860]

theorem cert12860_13 : CellCertificate 12860 (44113703139677 / 500000000000000 : ℝ) (6380109952237 / 3906250000000000 : ℝ) (329822481967737 / 10000000000000000 : ℝ)
    (cell12860 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · have h := gap_lower (n := 12860) (a := (8362151326267 / 10000000000000 : ℝ)) (b := (640589233 / 400000000000 : ℝ)) (q := (2232293680701 / 100000000000000 : ℝ))
      (E := (cell12860 ⟨13, by decide⟩).energy) (xi := (329822481967737 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12860 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12860]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12860])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12860) (a := (8362151326267 / 10000000000000 : ℝ)) (b := (640589233 / 400000000000 : ℝ)) (q := (2232293680701 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12860])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12860])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12860]

theorem cert12860_14 : CellCertificate 12860 (44113703139677 / 500000000000000 : ℝ) (6380109952237 / 3906250000000000 : ℝ) (329822481967737 / 10000000000000000 : ℝ)
    (cell12860 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · have h := gap_lower (n := 12860) (a := (1671738188293 / 2000000000000 : ℝ)) (b := (640589233 / 400000000000 : ℝ)) (q := (446459527231 / 20000000000000 : ℝ))
      (E := (cell12860 ⟨14, by decide⟩).energy) (xi := (329822481967737 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12860 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12860]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12860])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12860) (a := (1671738188293 / 2000000000000 : ℝ)) (b := (640589233 / 400000000000 : ℝ)) (q := (446459527231 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12860])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12860])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12860]

theorem cert12860_15 : CellCertificate 12860 (44113703139677 / 500000000000000 : ℝ) (6380109952237 / 3906250000000000 : ℝ) (329822481967737 / 10000000000000000 : ℝ)
    (cell12860 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · have h := gap_lower (n := 12860) (a := (83552329971321 / 100000000000000 : ℝ)) (b := (640589233 / 400000000000 : ℝ)) (q := (1116150827173 / 50000000000000 : ℝ))
      (E := (cell12860 ⟨15, by decide⟩).energy) (xi := (329822481967737 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12860 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12860]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12860])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12860) (a := (83552329971321 / 100000000000000 : ℝ)) (b := (640589233 / 400000000000 : ℝ)) (q := (1116150827173 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12860])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12860])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12860]

theorem cert12860_16 : CellCertificate 12860 (44113703139677 / 500000000000000 : ℝ) (6380109952237 / 3906250000000000 : ℝ) (329822481967737 / 10000000000000000 : ℝ)
    (cell12860 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · have h := gap_lower (n := 12860) (a := (83517774898731 / 100000000000000 : ℝ)) (b := (640589233 / 400000000000 : ℝ)) (q := (34879776287 / 1562500000000 : ℝ))
      (E := (cell12860 ⟨16, by decide⟩).energy) (xi := (329822481967737 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12860 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12860]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12860])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12860) (a := (83517774898731 / 100000000000000 : ℝ)) (b := (640589233 / 400000000000 : ℝ)) (q := (34879776287 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12860])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12860])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12860]

theorem cert12860_17 : CellCertificate 12860 (44113703139677 / 500000000000000 : ℝ) (6380109952237 / 3906250000000000 : ℝ) (329822481967737 / 10000000000000000 : ℝ)
    (cell12860 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · have h := gap_lower (n := 12860) (a := (2608851380097 / 3125000000000 : ℝ)) (b := (640589233 / 400000000000 : ℝ)) (q := (2232309666977 / 100000000000000 : ℝ))
      (E := (cell12860 ⟨17, by decide⟩).energy) (xi := (329822481967737 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12860 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12860]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12860])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12860) (a := (2608851380097 / 3125000000000 : ℝ)) (b := (640589233 / 400000000000 : ℝ)) (q := (2232309666977 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12860])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12860])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12860]

theorem cert12860_18 : CellCertificate 12860 (44113703139677 / 500000000000000 : ℝ) (6380109952237 / 3906250000000000 : ℝ) (329822481967737 / 10000000000000000 : ℝ)
    (cell12860 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · have h := gap_lower (n := 12860) (a := (83448737730837 / 100000000000000 : ℝ)) (b := (640589233 / 400000000000 : ℝ)) (q := (2232313671089 / 100000000000000 : ℝ))
      (E := (cell12860 ⟨18, by decide⟩).energy) (xi := (329822481967737 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12860 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12860]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12860])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12860) (a := (83448737730837 / 100000000000000 : ℝ)) (b := (640589233 / 400000000000 : ℝ)) (q := (2232313671089 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12860])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12860])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12860]

theorem cert12860_19 : CellCertificate 12860 (44113703139677 / 500000000000000 : ℝ) (6380109952237 / 3906250000000000 : ℝ) (329822481967737 / 10000000000000000 : ℝ)
    (cell12860 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · have h := gap_lower (n := 12860) (a := (10426781946063 / 12500000000000 : ℝ)) (b := (640589233 / 400000000000 : ℝ)) (q := (697599281 / 31250000000 : ℝ))
      (E := (cell12860 ⟨19, by decide⟩).energy) (xi := (329822481967737 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12860 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12860]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12860])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12860) (a := (10426781946063 / 12500000000000 : ℝ)) (b := (640589233 / 400000000000 : ℝ)) (q := (697599281 / 31250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12860])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12860])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12860]

theorem cert12861_0 : CellCertificate 12861 (220561697831941 / 2500000000000000 : ℝ) (326636221912147 / 200000000000000000 : ℝ) (329796227406431 / 10000000000000000 : ℝ)
    (cell12861 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · have h := gap_lower (n := 12861) (a := (84073585135459 / 100000000000000 : ℝ)) (b := (20016838517 / 12500000000000 : ℝ)) (q := (2232123852051 / 100000000000000 : ℝ))
      (E := (cell12861 ⟨0, by decide⟩).energy) (xi := (329796227406431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12861 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12861]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12861])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12861) (a := (84073585135459 / 100000000000000 : ℝ)) (b := (20016838517 / 12500000000000 : ℝ)) (q := (2232123852051 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12861])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12861])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12861]

theorem cert12861_1 : CellCertificate 12861 (220561697831941 / 2500000000000000 : ℝ) (326636221912147 / 200000000000000000 : ℝ) (329796227406431 / 10000000000000000 : ℝ)
    (cell12861 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · have h := gap_lower (n := 12861) (a := (21009665292167 / 25000000000000 : ℝ)) (b := (20016838517 / 12500000000000 : ℝ)) (q := (1116063924223 / 50000000000000 : ℝ))
      (E := (cell12861 ⟨1, by decide⟩).energy) (xi := (329796227406431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12861 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12861]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12861])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12861) (a := (21009665292167 / 25000000000000 : ℝ)) (b := (20016838517 / 12500000000000 : ℝ)) (q := (1116063924223 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12861])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12861])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12861]

theorem cert12861_2 : CellCertificate 12861 (220561697831941 / 2500000000000000 : ℝ) (326636221912147 / 200000000000000000 : ℝ) (329796227406431 / 10000000000000000 : ℝ)
    (cell12861 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · have h := gap_lower (n := 12861) (a := (84003762064023 / 100000000000000 : ℝ)) (b := (20016838517 / 12500000000000 : ℝ)) (q := (1116065908561 / 50000000000000 : ℝ))
      (E := (cell12861 ⟨2, by decide⟩).energy) (xi := (329796227406431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12861 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12861]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12861])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12861) (a := (84003762064023 / 100000000000000 : ℝ)) (b := (20016838517 / 12500000000000 : ℝ)) (q := (1116065908561 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12861])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12861])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12861]

theorem cert12861_3 : CellCertificate 12861 (220561697831941 / 2500000000000000 : ℝ) (326636221912147 / 200000000000000000 : ℝ) (329796227406431 / 10000000000000000 : ℝ)
    (cell12861 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · have h := gap_lower (n := 12861) (a := (83968887785181 / 100000000000000 : ℝ)) (b := (20016838517 / 12500000000000 : ℝ)) (q := (139508489033 / 6250000000000 : ℝ))
      (E := (cell12861 ⟨3, by decide⟩).energy) (xi := (329796227406431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12861 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12861]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12861])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12861) (a := (83968887785181 / 100000000000000 : ℝ)) (b := (20016838517 / 12500000000000 : ℝ)) (q := (139508489033 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12861])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12861])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12861]

theorem cert12861_4 : CellCertificate 12861 (220561697831941 / 2500000000000000 : ℝ) (326636221912147 / 200000000000000000 : ℝ) (329796227406431 / 10000000000000000 : ℝ)
    (cell12861 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · have h := gap_lower (n := 12861) (a := (10491754786999 / 12500000000000 : ℝ)) (b := (20016838517 / 12500000000000 : ℝ)) (q := (446427964221 / 20000000000000 : ℝ))
      (E := (cell12861 ⟨4, by decide⟩).energy) (xi := (329796227406431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12861 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12861]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12861])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12861) (a := (10491754786999 / 12500000000000 : ℝ)) (b := (20016838517 / 12500000000000 : ℝ)) (q := (446427964221 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12861])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12861])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12861]

theorem cert12861_5 : CellCertificate 12861 (220561697831941 / 2500000000000000 : ℝ) (326636221912147 / 200000000000000000 : ℝ) (329796227406431 / 10000000000000000 : ℝ)
    (cell12861 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · have h := gap_lower (n := 12861) (a := (83899213560493 / 100000000000000 : ℝ)) (b := (20016838517 / 12500000000000 : ℝ)) (q := (2232143814889 / 100000000000000 : ℝ))
      (E := (cell12861 ⟨5, by decide⟩).energy) (xi := (329796227406431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12861 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12861]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12861])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12861) (a := (83899213560493 / 100000000000000 : ℝ)) (b := (20016838517 / 12500000000000 : ℝ)) (q := (2232143814889 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12861])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12861])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12861]

theorem cert12861_6 : CellCertificate 12861 (220561697831941 / 2500000000000000 : ℝ) (326636221912147 / 200000000000000000 : ℝ) (329796227406431 / 10000000000000000 : ℝ)
    (cell12861 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · have h := gap_lower (n := 12861) (a := (41932206771457 / 50000000000000 : ℝ)) (b := (20016838517 / 12500000000000 : ℝ)) (q := (2232147813661 / 100000000000000 : ℝ))
      (E := (cell12861 ⟨6, by decide⟩).energy) (xi := (329796227406431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12861 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12861]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12861])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12861) (a := (41932206771457 / 50000000000000 : ℝ)) (b := (20016838517 / 12500000000000 : ℝ)) (q := (2232147813661 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12861])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12861])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12861]

theorem cert12861_7 : CellCertificate 12861 (220561697831941 / 2500000000000000 : ℝ) (326636221912147 / 200000000000000000 : ℝ) (329796227406431 / 10000000000000000 : ℝ)
    (cell12861 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · have h := gap_lower (n := 12861) (a := (20957409551917 / 25000000000000 : ℝ)) (b := (20016838517 / 12500000000000 : ℝ)) (q := (558037956237 / 25000000000000 : ℝ))
      (E := (cell12861 ⟨7, by decide⟩).energy) (xi := (329796227406431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12861 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12861]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12861])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12861) (a := (20957409551917 / 25000000000000 : ℝ)) (b := (20016838517 / 12500000000000 : ℝ)) (q := (558037956237 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12861])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12861])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12861]

theorem cert12861_8 : CellCertificate 12861 (220561697831941 / 2500000000000000 : ℝ) (326636221912147 / 200000000000000000 : ℝ) (329796227406431 / 10000000000000000 : ℝ)
    (cell12861 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · have h := gap_lower (n := 12861) (a := (83794887519357 / 100000000000000 : ℝ)) (b := (20016838517 / 12500000000000 : ℝ)) (q := (279019482003 / 12500000000000 : ℝ))
      (E := (cell12861 ⟨8, by decide⟩).energy) (xi := (329796227406431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12861 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12861]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12861])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12861) (a := (83794887519357 / 100000000000000 : ℝ)) (b := (20016838517 / 12500000000000 : ℝ)) (q := (279019482003 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12861])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12861])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12861]

theorem cert12861_9 : CellCertificate 12861 (220561697831941 / 2500000000000000 : ℝ) (326636221912147 / 200000000000000000 : ℝ) (329796227406431 / 10000000000000000 : ℝ)
    (cell12861 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · have h := gap_lower (n := 12861) (a := (83760161442767 / 100000000000000 : ℝ)) (b := (20016838517 / 12500000000000 : ℝ)) (q := (558039963969 / 25000000000000 : ℝ))
      (E := (cell12861 ⟨9, by decide⟩).energy) (xi := (329796227406431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12861 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12861]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12861])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12861) (a := (83760161442767 / 100000000000000 : ℝ)) (b := (20016838517 / 12500000000000 : ℝ)) (q := (558039963969 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12861])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12861])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12861]

theorem cert12861_10 : CellCertificate 12861 (220561697831941 / 2500000000000000 : ℝ) (326636221912147 / 200000000000000000 : ℝ) (329796227406431 / 10000000000000000 : ℝ)
    (cell12861 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · have h := gap_lower (n := 12861) (a := (83725459942869 / 100000000000000 : ℝ)) (b := (20016838517 / 12500000000000 : ℝ)) (q := (2232163831203 / 100000000000000 : ℝ))
      (E := (cell12861 ⟨10, by decide⟩).energy) (xi := (329796227406431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12861 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12861]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12861])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12861) (a := (83725459942869 / 100000000000000 : ℝ)) (b := (20016838517 / 12500000000000 : ℝ)) (q := (2232163831203 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12861])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12861])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12861]

theorem cert12861_11 : CellCertificate 12861 (220561697831941 / 2500000000000000 : ℝ) (326636221912147 / 200000000000000000 : ℝ) (329796227406431 / 10000000000000000 : ℝ)
    (cell12861 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · have h := gap_lower (n := 12861) (a := (5230673936551 / 6250000000000 : ℝ)) (b := (20016838517 / 12500000000000 : ℝ)) (q := (1116083923271 / 50000000000000 : ℝ))
      (E := (cell12861 ⟨11, by decide⟩).energy) (xi := (329796227406431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12861 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12861]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12861])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12861) (a := (5230673936551 / 6250000000000 : ℝ)) (b := (20016838517 / 12500000000000 : ℝ)) (q := (1116083923271 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12861])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12861])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12861]

theorem cert12861_12 : CellCertificate 12861 (220561697831941 / 2500000000000000 : ℝ) (326636221912147 / 200000000000000000 : ℝ) (329796227406431 / 10000000000000000 : ℝ)
    (cell12861 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · have h := gap_lower (n := 12861) (a := (41828065266971 / 50000000000000 : ℝ)) (b := (20016838517 / 12500000000000 : ℝ)) (q := (1116085925031 / 50000000000000 : ℝ))
      (E := (cell12861 ⟨12, by decide⟩).energy) (xi := (329796227406431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12861 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12861]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12861])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12861) (a := (41828065266971 / 50000000000000 : ℝ)) (b := (20016838517 / 12500000000000 : ℝ)) (q := (1116085925031 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12861])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12861])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12861]

theorem cert12861_13 : CellCertificate 12861 (220561697831941 / 2500000000000000 : ℝ) (326636221912147 / 200000000000000000 : ℝ) (329796227406431 / 10000000000000000 : ℝ)
    (cell12861 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · have h := gap_lower (n := 12861) (a := (41810751277881 / 50000000000000 : ℝ)) (b := (20016838517 / 12500000000000 : ℝ)) (q := (2232175847717 / 100000000000000 : ℝ))
      (E := (cell12861 ⟨13, by decide⟩).energy) (xi := (329796227406431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12861 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12861]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12861])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12861) (a := (41810751277881 / 50000000000000 : ℝ)) (b := (20016838517 / 12500000000000 : ℝ)) (q := (2232175847717 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12861])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12861])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12861]

theorem cert12861_14 : CellCertificate 12861 (220561697831941 / 2500000000000000 : ℝ) (326636221912147 / 200000000000000000 : ℝ) (329796227406431 / 10000000000000000 : ℝ)
    (cell12861 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · have h := gap_lower (n := 12861) (a := (8358689901597 / 10000000000000 : ℝ)) (b := (20016838517 / 12500000000000 : ℝ)) (q := (2232179845221 / 100000000000000 : ℝ))
      (E := (cell12861 ⟨14, by decide⟩).energy) (xi := (329796227406431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12861 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12861]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12861])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12861) (a := (8358689901597 / 10000000000000 : ℝ)) (b := (20016838517 / 12500000000000 : ℝ)) (q := (2232179845221 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12861])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12861])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12861]

theorem cert12861_15 : CellCertificate 12861 (220561697831941 / 2500000000000000 : ℝ) (326636221912147 / 200000000000000000 : ℝ) (329796227406431 / 10000000000000000 : ℝ)
    (cell12861 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · have h := gap_lower (n := 12861) (a := (83552319880437 / 100000000000000 : ℝ)) (b := (20016838517 / 12500000000000 : ℝ)) (q := (2232183848039 / 100000000000000 : ℝ))
      (E := (cell12861 ⟨15, by decide⟩).energy) (xi := (329796227406431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12861 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12861]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12861])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12861) (a := (83552319880437 / 100000000000000 : ℝ)) (b := (20016838517 / 12500000000000 : ℝ)) (q := (2232183848039 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12861])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12861])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12861]

theorem cert12861_16 : CellCertificate 12861 (220561697831941 / 2500000000000000 : ℝ) (326636221912147 / 200000000000000000 : ℝ) (329796227406431 / 10000000000000000 : ℝ)
    (cell12861 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · have h := gap_lower (n := 12861) (a := (83517765115213 / 100000000000000 : ℝ)) (b := (20016838517 / 12500000000000 : ℝ)) (q := (139511741337 / 6250000000000 : ℝ))
      (E := (cell12861 ⟨16, by decide⟩).energy) (xi := (329796227406431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12861 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12861]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12861])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12861) (a := (83517765115213 / 100000000000000 : ℝ)) (b := (20016838517 / 12500000000000 : ℝ)) (q := (139511741337 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12861])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12861])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12861]

theorem cert12861_17 : CellCertificate 12861 (220561697831941 / 2500000000000000 : ℝ) (326636221912147 / 200000000000000000 : ℝ) (329796227406431 / 10000000000000000 : ℝ)
    (cell12861 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · have h := gap_lower (n := 12861) (a := (41741617343261 / 50000000000000 : ℝ)) (b := (20016838517 / 12500000000000 : ℝ)) (q := (2232191890261 / 100000000000000 : ℝ))
      (E := (cell12861 ⟨17, by decide⟩).energy) (xi := (329796227406431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12861 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12861]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12861])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12861) (a := (41741617343261 / 50000000000000 : ℝ)) (b := (20016838517 / 12500000000000 : ℝ)) (q := (2232191890261 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12861])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12861])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12861]

theorem cert12861_18 : CellCertificate 12861 (220561697831941 / 2500000000000000 : ℝ) (326636221912147 / 200000000000000000 : ℝ) (329796227406431 / 10000000000000000 : ℝ)
    (cell12861 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · have h := gap_lower (n := 12861) (a := (83448728560763 / 100000000000000 : ℝ)) (b := (20016838517 / 12500000000000 : ℝ)) (q := (2232195881137 / 100000000000000 : ℝ))
      (E := (cell12861 ⟨18, by decide⟩).energy) (xi := (329796227406431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12861 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12861]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12861])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12861) (a := (83448728560763 / 100000000000000 : ℝ)) (b := (20016838517 / 12500000000000 : ℝ)) (q := (2232195881137 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12861])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12861])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12861]

theorem cert12861_19 : CellCertificate 12861 (220561697831941 / 2500000000000000 : ℝ) (326636221912147 / 200000000000000000 : ℝ) (329796227406431 / 10000000000000000 : ℝ)
    (cell12861 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · have h := gap_lower (n := 12861) (a := (8341424670451 / 10000000000000 : ℝ)) (b := (20016838517 / 12500000000000 : ℝ)) (q := (446439979343 / 20000000000000 : ℝ))
      (E := (cell12861 ⟨19, by decide⟩).energy) (xi := (329796227406431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12861 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12861]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12861])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12861) (a := (8341424670451 / 10000000000000 : ℝ)) (b := (20016838517 / 12500000000000 : ℝ)) (q := (446439979343 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12861])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12861])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12861]

theorem cert12862_0 : CellCertificate 12862 (882219523928617 / 10000000000000000 : ℝ) (816527045554623 / 500000000000000000 : ℝ) (82442494267487 / 2500000000000000 : ℝ)
    (cell12862 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · have h := gap_lower (n := 12862) (a := (84073570384237 / 100000000000000 : ℝ)) (b := (2501907969 / 1562500000000 : ℝ)) (q := (2232006057253 / 100000000000000 : ℝ))
      (E := (cell12862 ⟨0, by decide⟩).energy) (xi := (82442494267487 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12862 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12862]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12862])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12862) (a := (84073570384237 / 100000000000000 : ℝ)) (b := (2501907969 / 1562500000000 : ℝ)) (q := (2232006057253 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12862])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12862])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12862]

theorem cert12862_1 : CellCertificate 12862 (882219523928617 / 10000000000000000 : ℝ) (816527045554623 / 500000000000000000 : ℝ) (82442494267487 / 2500000000000000 : ℝ)
    (cell12862 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · have h := gap_lower (n := 12862) (a := (3361545869253 / 4000000000000 : ℝ)) (b := (2501907969 / 1562500000000 : ℝ)) (q := (89280403443 / 4000000000000 : ℝ))
      (E := (cell12862 ⟨1, by decide⟩).energy) (xi := (82442494267487 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12862 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12862]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12862])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12862) (a := (3361545869253 / 4000000000000 : ℝ)) (b := (2501907969 / 1562500000000 : ℝ)) (q := (89280403443 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12862])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12862])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12862]

theorem cert12862_2 : CellCertificate 12862 (882219523928617 / 10000000000000000 : ℝ) (816527045554623 / 500000000000000000 : ℝ) (82442494267487 / 2500000000000000 : ℝ)
    (cell12862 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · have h := gap_lower (n := 12862) (a := (21000936985029 / 25000000000000 : ℝ)) (b := (2501907969 / 1562500000000 : ℝ)) (q := (279001760993 / 12500000000000 : ℝ))
      (E := (cell12862 ⟨2, by decide⟩).energy) (xi := (82442494267487 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12862 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12862]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12862])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12862) (a := (21000936985029 / 25000000000000 : ℝ)) (b := (2501907969 / 1562500000000 : ℝ)) (q := (279001760993 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12862])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12862])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12862]

theorem cert12862_3 : CellCertificate 12862 (882219523928617 / 10000000000000000 : ℝ) (816527045554623 / 500000000000000000 : ℝ) (82442494267487 / 2500000000000000 : ℝ)
    (cell12862 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · have h := gap_lower (n := 12862) (a := (20992218493567 / 25000000000000 : ℝ)) (b := (2501907969 / 1562500000000 : ℝ)) (q := (223201807141 / 10000000000000 : ℝ))
      (E := (cell12862 ⟨3, by decide⟩).energy) (xi := (82442494267487 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12862 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12862]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12862])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12862) (a := (20992218493567 / 25000000000000 : ℝ)) (b := (2501907969 / 1562500000000 : ℝ)) (q := (223201807141 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12862])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12862])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12862]

theorem cert12862_4 : CellCertificate 12862 (882219523928617 / 10000000000000000 : ℝ) (816527045554623 / 500000000000000000 : ℝ) (82442494267487 / 2500000000000000 : ℝ)
    (cell12862 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · have h := gap_lower (n := 12862) (a := (8393402479763 / 10000000000000 : ℝ)) (b := (2501907969 / 1562500000000 : ℝ)) (q := (2232022044763 / 100000000000000 : ℝ))
      (E := (cell12862 ⟨4, by decide⟩).energy) (xi := (82442494267487 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12862 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12862]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12862])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12862) (a := (8393402479763 / 10000000000000 : ℝ)) (b := (2501907969 / 1562500000000 : ℝ)) (q := (2232022044763 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12862])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12862])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12862]

theorem cert12862_5 : CellCertificate 12862 (882219523928617 / 10000000000000000 : ℝ) (816527045554623 / 500000000000000000 : ℝ) (82442494267487 / 2500000000000000 : ℝ)
    (cell12862 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · have h := gap_lower (n := 12862) (a := (20974800093561 / 25000000000000 : ℝ)) (b := (2501907969 / 1562500000000 : ℝ)) (q := (2232026073981 / 100000000000000 : ℝ))
      (E := (cell12862 ⟨5, by decide⟩).energy) (xi := (82442494267487 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12862 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12862]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12862])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12862) (a := (20974800093561 / 25000000000000 : ℝ)) (b := (2501907969 / 1562500000000 : ℝ)) (q := (2232026073981 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12862])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12862])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12862]

theorem cert12862_6 : CellCertificate 12862 (882219523928617 / 10000000000000000 : ℝ) (816527045554623 / 500000000000000000 : ℝ) (82442494267487 / 2500000000000000 : ℝ)
    (cell12862 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · have h := gap_lower (n := 12862) (a := (83864400668337 / 100000000000000 : ℝ)) (b := (2501907969 / 1562500000000 : ℝ)) (q := (1116015025491 / 50000000000000 : ℝ))
      (E := (cell12862 ⟨6, by decide⟩).energy) (xi := (82442494267487 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12862 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12862]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12862])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12862) (a := (83864400668337 / 100000000000000 : ℝ)) (b := (2501907969 / 1562500000000 : ℝ)) (q := (1116015025491 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12862])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12862])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12862]

theorem cert12862_7 : CellCertificate 12862 (882219523928617 / 10000000000000000 : ℝ) (816527045554623 / 500000000000000000 : ℝ) (82442494267487 / 2500000000000000 : ℝ)
    (cell12862 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · have h := gap_lower (n := 12862) (a := (3353185025773 / 4000000000000 : ℝ)) (b := (2501907969 / 1562500000000 : ℝ)) (q := (1116017049601 / 50000000000000 : ℝ))
      (E := (cell12862 ⟨7, by decide⟩).energy) (xi := (82442494267487 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12862 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12862]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12862])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12862) (a := (3353185025773 / 4000000000000 : ℝ)) (b := (2501907969 / 1562500000000 : ℝ)) (q := (1116017049601 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12862])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12862])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12862]

theorem cert12862_8 : CellCertificate 12862 (882219523928617 / 10000000000000000 : ℝ) (816527045554623 / 500000000000000000 : ℝ) (82442494267487 / 2500000000000000 : ℝ)
    (cell12862 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · have h := gap_lower (n := 12862) (a := (8379487526681 / 10000000000000 : ℝ)) (b := (2501907969 / 1562500000000 : ℝ)) (q := (2232038051943 / 100000000000000 : ℝ))
      (E := (cell12862 ⟨8, by decide⟩).energy) (xi := (82442494267487 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12862 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12862]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12862])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12862) (a := (8379487526681 / 10000000000000 : ℝ)) (b := (2501907969 / 1562500000000 : ℝ)) (q := (2232038051943 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12862])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12862])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12862]

theorem cert12862_9 : CellCertificate 12862 (882219523928617 / 10000000000000000 : ℝ) (816527045554623 / 500000000000000000 : ℝ) (82442494267487 / 2500000000000000 : ℝ)
    (cell12862 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · have h := gap_lower (n := 12862) (a := (4188007475029 / 5000000000000 : ℝ)) (b := (2501907969 / 1562500000000 : ℝ)) (q := (2232042090197 / 100000000000000 : ℝ))
      (E := (cell12862 ⟨9, by decide⟩).energy) (xi := (82442494267487 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12862 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12862]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12862])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12862) (a := (4188007475029 / 5000000000000 : ℝ)) (b := (2501907969 / 1562500000000 : ℝ)) (q := (2232042090197 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12862])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12862])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12862]

theorem cert12862_10 : CellCertificate 12862 (882219523928617 / 10000000000000000 : ℝ) (816527045554623 / 500000000000000000 : ℝ) (82442494267487 / 2500000000000000 : ℝ)
    (cell12862 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · have h := gap_lower (n := 12862) (a := (41862724155303 / 50000000000000 : ℝ)) (b := (2501907969 / 1562500000000 : ℝ)) (q := (446409220937 / 20000000000000 : ℝ))
      (E := (cell12862 ⟨10, by decide⟩).energy) (xi := (82442494267487 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12862 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12862]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12862])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12862) (a := (41862724155303 / 50000000000000 : ℝ)) (b := (2501907969 / 1562500000000 : ℝ)) (q := (446409220937 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12862])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12862])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12862]

theorem cert12862_11 : CellCertificate 12862 (882219523928617 / 10000000000000000 : ℝ) (816527045554623 / 500000000000000000 : ℝ) (82442494267487 / 2500000000000000 : ℝ)
    (cell12862 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · have h := gap_lower (n := 12862) (a := (41845385831021 / 50000000000000 : ℝ)) (b := (2501907969 / 1562500000000 : ℝ)) (q := (2232050101859 / 100000000000000 : ℝ))
      (E := (cell12862 ⟨11, by decide⟩).energy) (xi := (82442494267487 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12862 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12862]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12862])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12862) (a := (41845385831021 / 50000000000000 : ℝ)) (b := (2501907969 / 1562500000000 : ℝ)) (q := (2232050101859 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12862])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12862])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12862]

theorem cert12862_12 : CellCertificate 12862 (882219523928617 / 10000000000000000 : ℝ) (816527045554623 / 500000000000000000 : ℝ) (82442494267487 / 2500000000000000 : ℝ)
    (cell12862 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · have h := gap_lower (n := 12862) (a := (2614253735007 / 3125000000000 : ℝ)) (b := (2501907969 / 1562500000000 : ℝ)) (q := (27900676099 / 1250000000000 : ℝ))
      (E := (cell12862 ⟨12, by decide⟩).energy) (xi := (82442494267487 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12862 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12862]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12862])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12862) (a := (2614253735007 / 3125000000000 : ℝ)) (b := (2501907969 / 1562500000000 : ℝ)) (q := (27900676099 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12862])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12862])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12862]

theorem cert12862_13 : CellCertificate 12862 (882219523928617 / 10000000000000000 : ℝ) (816527045554623 / 500000000000000000 : ℝ) (82442494267487 / 2500000000000000 : ℝ)
    (cell12862 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · have h := gap_lower (n := 12862) (a := (41810745925333 / 50000000000000 : ℝ)) (b := (2501907969 / 1562500000000 : ℝ)) (q := (2232058068827 / 100000000000000 : ℝ))
      (E := (cell12862 ⟨13, by decide⟩).energy) (xi := (82442494267487 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12862 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12862]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12862])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12862) (a := (41810745925333 / 50000000000000 : ℝ)) (b := (2501907969 / 1562500000000 : ℝ)) (q := (2232058068827 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12862])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12862])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12862]

theorem cert12862_14 : CellCertificate 12862 (882219523928617 / 10000000000000000 : ℝ) (816527045554623 / 500000000000000000 : ℝ) (82442494267487 / 2500000000000000 : ℝ)
    (cell12862 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · have h := gap_lower (n := 12862) (a := (10448361077383 / 12500000000000 : ℝ)) (b := (2501907969 / 1562500000000 : ℝ)) (q := (1116031054221 / 50000000000000 : ℝ))
      (E := (cell12862 ⟨14, by decide⟩).energy) (xi := (82442494267487 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12862 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12862]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12862])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12862) (a := (10448361077383 / 12500000000000 : ℝ)) (b := (2501907969 / 1562500000000 : ℝ)) (q := (1116031054221 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12862])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12862])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12862]

theorem cert12862_15 : CellCertificate 12862 (882219523928617 / 10000000000000000 : ℝ) (816527045554623 / 500000000000000000 : ℝ) (82442494267487 / 2500000000000000 : ℝ)
    (cell12862 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · have h := gap_lower (n := 12862) (a := (8355230979129 / 10000000000000 : ℝ)) (b := (2501907969 / 1562500000000 : ℝ)) (q := (558016523987 / 25000000000000 : ℝ))
      (E := (cell12862 ⟨15, by decide⟩).energy) (xi := (82442494267487 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12862 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12862]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12862])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12862) (a := (8355230979129 / 10000000000000 : ℝ)) (b := (2501907969 / 1562500000000 : ℝ)) (q := (558016523987 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12862])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12862])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12862]

theorem cert12862_16 : CellCertificate 12862 (882219523928617 / 10000000000000000 : ℝ) (816527045554623 / 500000000000000000 : ℝ) (82442494267487 / 2500000000000000 : ℝ)
    (cell12862 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · have h := gap_lower (n := 12862) (a := (16703551066679 / 20000000000000 : ℝ)) (b := (2501907969 / 1562500000000 : ℝ)) (q := (1116035047347 / 50000000000000 : ℝ))
      (E := (cell12862 ⟨16, by decide⟩).energy) (xi := (82442494267487 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12862 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12862]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12862])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12862) (a := (16703551066679 / 20000000000000 : ℝ)) (b := (2501907969 / 1562500000000 : ℝ)) (q := (1116035047347 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12862])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12862])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12862]

theorem cert12862_17 : CellCertificate 12862 (882219523928617 / 10000000000000000 : ℝ) (816527045554623 / 500000000000000000 : ℝ) (82442494267487 / 2500000000000000 : ℝ)
    (cell12862 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · have h := gap_lower (n := 12862) (a := (20870806302901 / 25000000000000 : ℝ)) (b := (2501907969 / 1562500000000 : ℝ)) (q := (111603705483 / 5000000000000 : ℝ))
      (E := (cell12862 ⟨17, by decide⟩).energy) (xi := (82442494267487 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12862 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12862]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12862])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12862) (a := (20870806302901 / 25000000000000 : ℝ)) (b := (2501907969 / 1562500000000 : ℝ)) (q := (111603705483 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12862])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12862])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12862]

theorem cert12862_18 : CellCertificate 12862 (882219523928617 / 10000000000000000 : ℝ) (816527045554623 / 500000000000000000 : ℝ) (82442494267487 / 2500000000000000 : ℝ)
    (cell12862 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · have h := gap_lower (n := 12862) (a := (20862179848079 / 25000000000000 : ℝ)) (b := (2501907969 / 1562500000000 : ℝ)) (q := (279009760917 / 12500000000000 : ℝ))
      (E := (cell12862 ⟨18, by decide⟩).energy) (xi := (82442494267487 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12862 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12862]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12862])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12862) (a := (20862179848079 / 25000000000000 : ℝ)) (b := (2501907969 / 1562500000000 : ℝ)) (q := (279009760917 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12862])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12862])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12862]

theorem cert12862_19 : CellCertificate 12862 (882219523928617 / 10000000000000000 : ℝ) (816527045554623 / 500000000000000000 : ℝ) (82442494267487 / 2500000000000000 : ℝ)
    (cell12862 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · have h := gap_lower (n := 12862) (a := (41707118921053 / 50000000000000 : ℝ)) (b := (2501907969 / 1562500000000 : ℝ)) (q := (2232082090419 / 100000000000000 : ℝ))
      (E := (cell12862 ⟨19, by decide⟩).energy) (xi := (82442494267487 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12862 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12862]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12862])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12862) (a := (41707118921053 / 50000000000000 : ℝ)) (b := (2501907969 / 1562500000000 : ℝ)) (q := (2232082090419 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12862])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12862])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12862]

theorem cert12863_0 : CellCertificate 12863 (441096130297573 / 5000000000000000 : ℝ) (408231773103399 / 250000000000000000 : ℝ) (41217966369649 / 1250000000000000 : ℝ)
    (cell12863 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · have h := gap_lower (n := 12863) (a := (84073555635311 / 100000000000000 : ℝ)) (b := (160109513889 / 100000000000000 : ℝ)) (q := (2231888315749 / 100000000000000 : ℝ))
      (E := (cell12863 ⟨0, by decide⟩).energy) (xi := (41217966369649 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12863 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12863]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12863])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12863) (a := (84073555635311 / 100000000000000 : ℝ)) (b := (160109513889 / 100000000000000 : ℝ)) (q := (2231888315749 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12863])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12863])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12863]

theorem cert12863_1 : CellCertificate 12863 (441096130297573 / 5000000000000000 : ℝ) (408231773103399 / 250000000000000000 : ℝ) (41217966369649 / 1250000000000000 : ℝ)
    (cell12863 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · have h := gap_lower (n := 12863) (a := (84038632296241 / 100000000000000 : ℝ)) (b := (160109513889 / 100000000000000 : ℝ)) (q := (223189231921 / 10000000000000 : ℝ))
      (E := (cell12863 ⟨1, by decide⟩).energy) (xi := (41217966369649 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12863 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12863]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12863])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12863) (a := (84038632296241 / 100000000000000 : ℝ)) (b := (160109513889 / 100000000000000 : ℝ)) (q := (223189231921 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12863])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12863])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12863]

theorem cert12863_2 : CellCertificate 12863 (441096130297573 / 5000000000000000 : ℝ) (408231773103399 / 250000000000000000 : ℝ) (41217966369649 / 1250000000000000 : ℝ)
    (cell12863 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · have h := gap_lower (n := 12863) (a := (8400373381843 / 10000000000000 : ℝ)) (b := (160109513889 / 100000000000000 : ℝ)) (q := (1115948148219 / 50000000000000 : ℝ))
      (E := (cell12863 ⟨2, by decide⟩).energy) (xi := (41217966369649 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12863 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12863]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12863])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12863) (a := (8400373381843 / 10000000000000 : ℝ)) (b := (160109513889 / 100000000000000 : ℝ)) (q := (1115948148219 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12863])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12863])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12863]

theorem cert12863_3 : CellCertificate 12863 (441096130297573 / 5000000000000000 : ℝ) (408231773103399 / 250000000000000000 : ℝ) (41217966369649 / 1250000000000000 : ℝ)
    (cell12863 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · have h := gap_lower (n := 12863) (a := (41984430082769 / 50000000000000 : ℝ)) (b := (160109513889 / 100000000000000 : ℝ)) (q := (1115950156937 / 50000000000000 : ℝ))
      (E := (cell12863 ⟨3, by decide⟩).energy) (xi := (41217966369649 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12863 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12863]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12863])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12863) (a := (41984430082769 / 50000000000000 : ℝ)) (b := (160109513889 / 100000000000000 : ℝ)) (q := (1115950156937 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12863])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12863])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12863]

theorem cert12863_4 : CellCertificate 12863 (441096130297573 / 5000000000000000 : ℝ) (408231773103399 / 250000000000000000 : ℝ) (41217966369649 / 1250000000000000 : ℝ)
    (cell12863 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · have h := gap_lower (n := 12863) (a := (16786802260283 / 20000000000000 : ℝ)) (b := (160109513889 / 100000000000000 : ℝ)) (q := (1115952160981 / 50000000000000 : ℝ))
      (E := (cell12863 ⟨4, by decide⟩).energy) (xi := (41217966369649 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12863 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12863]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12863])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12863) (a := (16786802260283 / 20000000000000 : ℝ)) (b := (160109513889 / 100000000000000 : ℝ)) (q := (1115952160981 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12863])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12863])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12863]

theorem cert12863_5 : CellCertificate 12863 (441096130297573 / 5000000000000000 : ℝ) (408231773103399 / 250000000000000000 : ℝ) (41217966369649 / 1250000000000000 : ℝ)
    (cell12863 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · have h := gap_lower (n := 12863) (a := (83899187190103 / 100000000000000 : ℝ)) (b := (160109513889 / 100000000000000 : ℝ)) (q := (1115954164367 / 50000000000000 : ℝ))
      (E := (cell12863 ⟨5, by decide⟩).energy) (xi := (41217966369649 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12863 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12863]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12863])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12863) (a := (83899187190103 / 100000000000000 : ℝ)) (b := (160109513889 / 100000000000000 : ℝ)) (q := (1115954164367 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12863])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12863])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12863]

theorem cert12863_6 : CellCertificate 12863 (441096130297573 / 5000000000000000 : ℝ) (408231773103399 / 250000000000000000 : ℝ) (41217966369649 / 1250000000000000 : ℝ)
    (cell12863 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · have h := gap_lower (n := 12863) (a := (83864387795831 / 100000000000000 : ℝ)) (b := (160109513889 / 100000000000000 : ℝ)) (q := (2231912341969 / 100000000000000 : ℝ))
      (E := (cell12863 ⟨6, by decide⟩).energy) (xi := (41217966369649 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12863 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12863]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12863])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12863) (a := (83864387795831 / 100000000000000 : ℝ)) (b := (160109513889 / 100000000000000 : ℝ)) (q := (2231912341969 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12863])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12863])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12863]

theorem cert12863_7 : CellCertificate 12863 (441096130297573 / 5000000000000000 : ℝ) (408231773103399 / 250000000000000000 : ℝ) (41217966369649 / 1250000000000000 : ℝ)
    (cell12863 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · have h := gap_lower (n := 12863) (a := (16765922616603 / 20000000000000 : ℝ)) (b := (160109513889 / 100000000000000 : ℝ)) (q := (2231916311203 / 100000000000000 : ℝ))
      (E := (cell12863 ⟨7, by decide⟩).energy) (xi := (41217966369649 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12863 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12863]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12863])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12863) (a := (16765922616603 / 20000000000000 : ℝ)) (b := (160109513889 / 100000000000000 : ℝ)) (q := (2231916311203 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12863])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12863])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12863]

theorem cert12863_8 : CellCertificate 12863 (441096130297573 / 5000000000000000 : ℝ) (408231773103399 / 250000000000000000 : ℝ) (41217966369649 / 1250000000000000 : ℝ)
    (cell12863 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · have h := gap_lower (n := 12863) (a := (83794863016259 / 100000000000000 : ℝ)) (b := (160109513889 / 100000000000000 : ℝ)) (q := (139495022479 / 6250000000000 : ℝ))
      (E := (cell12863 ⟨8, by decide⟩).energy) (xi := (41217966369649 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12863 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12863]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12863])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12863) (a := (83794863016259 / 100000000000000 : ℝ)) (b := (160109513889 / 100000000000000 : ℝ)) (q := (139495022479 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12863])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12863])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12863]

theorem cert12863_9 : CellCertificate 12863 (441096130297573 / 5000000000000000 : ℝ) (408231773103399 / 250000000000000000 : ℝ) (41217966369649 / 1250000000000000 : ℝ)
    (cell12863 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · have h := gap_lower (n := 12863) (a := (2617504298761 / 3125000000000 : ℝ)) (b := (160109513889 / 100000000000000 : ℝ)) (q := (557981080083 / 25000000000000 : ℝ))
      (E := (cell12863 ⟨9, by decide⟩).energy) (xi := (41217966369649 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12863 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12863]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12863])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12863) (a := (2617504298761 / 3125000000000 : ℝ)) (b := (160109513889 / 100000000000000 : ℝ)) (q := (557981080083 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12863])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12863])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12863]

theorem cert12863_10 : CellCertificate 12863 (441096130297573 / 5000000000000000 : ℝ) (408231773103399 / 250000000000000000 : ℝ) (41217966369649 / 1250000000000000 : ℝ)
    (cell12863 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · have h := gap_lower (n := 12863) (a := (16745087336053 / 20000000000000 : ℝ)) (b := (160109513889 / 100000000000000 : ℝ)) (q := (2231928374019 / 100000000000000 : ℝ))
      (E := (cell12863 ⟨10, by decide⟩).energy) (xi := (41217966369649 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12863 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12863]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12863])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12863) (a := (16745087336053 / 20000000000000 : ℝ)) (b := (160109513889 / 100000000000000 : ℝ)) (q := (2231928374019 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12863])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12863])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12863]

theorem cert12863_11 : CellCertificate 12863 (441096130297573 / 5000000000000000 : ℝ) (408231773103399 / 250000000000000000 : ℝ) (41217966369649 / 1250000000000000 : ℝ)
    (cell12863 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · have h := gap_lower (n := 12863) (a := (83690760341153 / 100000000000000 : ℝ)) (b := (160109513889 / 100000000000000 : ℝ)) (q := (278991544133 / 12500000000000 : ℝ))
      (E := (cell12863 ⟨11, by decide⟩).energy) (xi := (41217966369649 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12863 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12863]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12863])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12863) (a := (83690760341153 / 100000000000000 : ℝ)) (b := (160109513889 / 100000000000000 : ℝ)) (q := (278991544133 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12863])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12863])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12863]

theorem cert12863_12 : CellCertificate 12863 (441096130297573 / 5000000000000000 : ℝ) (408231773103399 / 250000000000000000 : ℝ) (41217966369649 / 1250000000000000 : ℝ)
    (cell12863 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · have h := gap_lower (n := 12863) (a := (83656108508353 / 100000000000000 : ℝ)) (b := (160109513889 / 100000000000000 : ℝ)) (q := (2231936379813 / 100000000000000 : ℝ))
      (E := (cell12863 ⟨12, by decide⟩).energy) (xi := (41217966369649 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12863 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12863]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12863])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12863) (a := (83656108508353 / 100000000000000 : ℝ)) (b := (160109513889 / 100000000000000 : ℝ)) (q := (2231936379813 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12863])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12863])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12863]

theorem cert12863_13 : CellCertificate 12863 (441096130297573 / 5000000000000000 : ℝ) (408231773103399 / 250000000000000000 : ℝ) (41217966369649 / 1250000000000000 : ℝ)
    (cell12863 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · have h := gap_lower (n := 12863) (a := (4181074057369 / 5000000000000 : ℝ)) (b := (160109513889 / 100000000000000 : ℝ)) (q := (69748135751 / 3125000000000 : ℝ))
      (E := (cell12863 ⟨13, by decide⟩).energy) (xi := (41217966369649 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12863 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12863]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12863])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12863) (a := (4181074057369 / 5000000000000 : ℝ)) (b := (160109513889 / 100000000000000 : ℝ)) (q := (69748135751 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12863])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12863])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12863]

theorem cert12863_14 : CellCertificate 12863 (441096130297573 / 5000000000000000 : ℝ) (408231773103399 / 250000000000000000 : ℝ) (41217966369649 / 1250000000000000 : ℝ)
    (cell12863 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · have h := gap_lower (n := 12863) (a := (20896719555983 / 25000000000000 : ℝ)) (b := (160109513889 / 100000000000000 : ℝ)) (q := (1115972183833 / 50000000000000 : ℝ))
      (E := (cell12863 ⟨14, by decide⟩).energy) (xi := (41217966369649 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12863 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12863]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12863])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12863) (a := (20896719555983 / 25000000000000 : ℝ)) (b := (160109513889 / 100000000000000 : ℝ)) (q := (1115972183833 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12863])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12863])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12863]

theorem cert12863_15 : CellCertificate 12863 (441096130297573 / 5000000000000000 : ℝ) (408231773103399 / 250000000000000000 : ℝ) (41217966369649 / 1250000000000000 : ℝ)
    (cell12863 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · have h := gap_lower (n := 12863) (a := (83552299703881 / 100000000000000 : ℝ)) (b := (160109513889 / 100000000000000 : ℝ)) (q := (278993542487 / 12500000000000 : ℝ))
      (E := (cell12863 ⟨15, by decide⟩).energy) (xi := (41217966369649 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12863 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12863]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12863])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12863) (a := (83552299703881 / 100000000000000 : ℝ)) (b := (160109513889 / 100000000000000 : ℝ)) (q := (278993542487 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12863])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12863])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12863]

theorem cert12863_16 : CellCertificate 12863 (441096130297573 / 5000000000000000 : ℝ) (408231773103399 / 250000000000000000 : ℝ) (41217966369649 / 1250000000000000 : ℝ)
    (cell12863 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · have h := gap_lower (n := 12863) (a := (41758872776639 / 50000000000000 : ℝ)) (b := (160109513889 / 100000000000000 : ℝ)) (q := (2231952382273 / 100000000000000 : ℝ))
      (E := (cell12863 ⟨16, by decide⟩).energy) (xi := (41217966369649 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12863 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12863]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12863])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12863) (a := (41758872776639 / 50000000000000 : ℝ)) (b := (160109513889 / 100000000000000 : ℝ)) (q := (2231952382273 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12863])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12863])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12863]

theorem cert12863_17 : CellCertificate 12863 (441096130297573 / 5000000000000000 : ℝ) (408231773103399 / 250000000000000000 : ℝ) (41217966369649 / 1250000000000000 : ℝ)
    (cell12863 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · have h := gap_lower (n := 12863) (a := (83483215738349 / 100000000000000 : ℝ)) (b := (160109513889 / 100000000000000 : ℝ)) (q := (2231956383399 / 100000000000000 : ℝ))
      (E := (cell12863 ⟨17, by decide⟩).energy) (xi := (41217966369649 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12863 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12863]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12863])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12863) (a := (83483215738349 / 100000000000000 : ℝ)) (b := (160109513889 / 100000000000000 : ℝ)) (q := (2231956383399 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12863])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12863])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12863]

theorem cert12863_18 : CellCertificate 12863 (441096130297573 / 5000000000000000 : ℝ) (408231773103399 / 250000000000000000 : ℝ) (41217966369649 / 1250000000000000 : ℝ)
    (cell12863 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · have h := gap_lower (n := 12863) (a := (10431088778187 / 12500000000000 : ℝ)) (b := (160109513889 / 100000000000000 : ℝ)) (q := (2231960347937 / 100000000000000 : ℝ))
      (E := (cell12863 ⟨18, by decide⟩).energy) (xi := (41217966369649 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12863 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12863]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12863])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12863) (a := (10431088778187 / 12500000000000 : ℝ)) (b := (160109513889 / 100000000000000 : ℝ)) (q := (2231960347937 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12863])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12863])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12863]

theorem cert12863_19 : CellCertificate 12863 (441096130297573 / 5000000000000000 : ℝ) (408231773103399 / 250000000000000000 : ℝ) (41217966369649 / 1250000000000000 : ℝ)
    (cell12863 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · have h := gap_lower (n := 12863) (a := (20853557245323 / 25000000000000 : ℝ)) (b := (160109513889 / 100000000000000 : ℝ)) (q := (278995549607 / 12500000000000 : ℝ))
      (E := (cell12863 ⟨19, by decide⟩).energy) (xi := (41217966369649 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12863 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12863]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12863])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12863) (a := (20853557245323 / 25000000000000 : ℝ)) (b := (160109513889 / 100000000000000 : ℝ)) (q := (278995549607 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12863])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12863])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12863]

theorem cert12864_0 : CellCertificate 12864 (441082500663199 / 5000000000000000 : ℝ) (65312004538767 / 40000000000000000 : ℝ) (329717489067069 / 10000000000000000 : ℝ)
    (cell12864 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · have h := gap_lower (n := 12864) (a := (84073540888681 / 100000000000000 : ℝ)) (b := (32019383951 / 20000000000000 : ℝ)) (q := (2231770627539 / 100000000000000 : ℝ))
      (E := (cell12864 ⟨0, by decide⟩).energy) (xi := (329717489067069 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12864 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12864]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12864])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12864) (a := (84073540888681 / 100000000000000 : ℝ)) (b := (32019383951 / 20000000000000 : ℝ)) (q := (2231770627539 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12864])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12864])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12864]

theorem cert12864_1 : CellCertificate 12864 (441082500663199 / 5000000000000000 : ℝ) (65312004538767 / 40000000000000000 : ℝ) (329717489067069 / 10000000000000000 : ℝ)
    (cell12864 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · have h := gap_lower (n := 12864) (a := (42019308931707 / 50000000000000 : ℝ)) (b := (32019383951 / 20000000000000 : ℝ)) (q := (2231774605703 / 100000000000000 : ℝ))
      (E := (cell12864 ⟨1, by decide⟩).energy) (xi := (329717489067069 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12864 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12864]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12864])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12864) (a := (42019308931707 / 50000000000000 : ℝ)) (b := (32019383951 / 20000000000000 : ℝ)) (q := (2231774605703 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12864])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12864])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12864]

theorem cert12864_2 : CellCertificate 12864 (441082500663199 / 5000000000000000 : ℝ) (65312004538767 / 40000000000000000 : ℝ) (329717489067069 / 10000000000000000 : ℝ)
    (cell12864 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · have h := gap_lower (n := 12864) (a := (21000929924741 / 25000000000000 : ℝ)) (b := (32019383951 / 20000000000000 : ℝ)) (q := (2231778616223 / 100000000000000 : ℝ))
      (E := (cell12864 ⟨2, by decide⟩).energy) (xi := (329717489067069 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12864 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12864]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12864])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12864) (a := (21000929924741 / 25000000000000 : ℝ)) (b := (32019383951 / 20000000000000 : ℝ)) (q := (2231778616223 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12864])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12864])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12864]

theorem cert12864_3 : CellCertificate 12864 (441082500663199 / 5000000000000000 : ℝ) (65312004538767 / 40000000000000000 : ℝ) (329717489067069 / 10000000000000000 : ℝ)
    (cell12864 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · have h := gap_lower (n := 12864) (a := (83968846358991 / 100000000000000 : ℝ)) (b := (32019383951 / 20000000000000 : ℝ)) (q := (2231782609819 / 100000000000000 : ℝ))
      (E := (cell12864 ⟨3, by decide⟩).energy) (xi := (329717489067069 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12864 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12864]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12864])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12864) (a := (83968846358991 / 100000000000000 : ℝ)) (b := (32019383951 / 20000000000000 : ℝ)) (q := (2231782609819 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12864])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12864])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12864]

theorem cert12864_4 : CellCertificate 12864 (441082500663199 / 5000000000000000 : ℝ) (65312004538767 / 40000000000000000 : ℝ) (329717489067069 / 10000000000000000 : ℝ)
    (cell12864 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · have h := gap_lower (n := 12864) (a := (41966998903673 / 50000000000000 : ℝ)) (b := (32019383951 / 20000000000000 : ℝ)) (q := (1115893297391 / 50000000000000 : ℝ))
      (E := (cell12864 ⟨4, by decide⟩).energy) (xi := (329717489067069 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12864 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12864]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12864])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12864) (a := (41966998903673 / 50000000000000 : ℝ)) (b := (32019383951 / 20000000000000 : ℝ)) (q := (1115893297391 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12864])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12864])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12864]

theorem cert12864_5 : CellCertificate 12864 (441082500663199 / 5000000000000000 : ℝ) (65312004538767 / 40000000000000000 : ℝ) (329717489067069 / 10000000000000000 : ℝ)
    (cell12864 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · have h := gap_lower (n := 12864) (a := (8389917400807 / 10000000000000 : ℝ)) (b := (32019383951 / 20000000000000 : ℝ)) (q := (223179063709 / 10000000000000 : ℝ))
      (E := (cell12864 ⟨5, by decide⟩).energy) (xi := (329717489067069 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12864 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12864]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12864])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12864) (a := (8389917400807 / 10000000000000 : ℝ)) (b := (32019383951 / 20000000000000 : ℝ)) (q := (223179063709 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12864])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12864])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12864]

theorem cert12864_6 : CellCertificate 12864 (441082500663199 / 5000000000000000 : ℝ) (65312004538767 / 40000000000000000 : ℝ) (329717489067069 / 10000000000000000 : ℝ)
    (cell12864 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · have h := gap_lower (n := 12864) (a := (20966093731349 / 25000000000000 : ℝ)) (b := (32019383951 / 20000000000000 : ℝ)) (q := (2231794628653 / 100000000000000 : ℝ))
      (E := (cell12864 ⟨6, by decide⟩).energy) (xi := (329717489067069 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12864 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12864]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12864])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12864) (a := (20966093731349 / 25000000000000 : ℝ)) (b := (32019383951 / 20000000000000 : ℝ)) (q := (2231794628653 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12864])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12864])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12864]

theorem cert12864_7 : CellCertificate 12864 (441082500663199 / 5000000000000000 : ℝ) (65312004538767 / 40000000000000000 : ℝ) (329717489067069 / 10000000000000000 : ℝ)
    (cell12864 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · have h := gap_lower (n := 12864) (a := (83829600523739 / 100000000000000 : ℝ)) (b := (32019383951 / 20000000000000 : ℝ)) (q := (55794965873 / 2500000000000 : ℝ))
      (E := (cell12864 ⟨7, by decide⟩).energy) (xi := (329717489067069 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12864 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12864]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12864])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12864) (a := (83829600523739 / 100000000000000 : ℝ)) (b := (32019383951 / 20000000000000 : ℝ)) (q := (55794965873 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12864])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12864])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12864]

theorem cert12864_8 : CellCertificate 12864 (441082500663199 / 5000000000000000 : ℝ) (65312004538767 / 40000000000000000 : ℝ) (329717489067069 / 10000000000000000 : ℝ)
    (cell12864 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · have h := gap_lower (n := 12864) (a := (16758970153541 / 20000000000000 : ℝ)) (b := (32019383951 / 20000000000000 : ℝ)) (q := (446360521029 / 20000000000000 : ℝ))
      (E := (cell12864 ⟨8, by decide⟩).energy) (xi := (329717489067069 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12864 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12864]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12864])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12864) (a := (16758970153541 / 20000000000000 : ℝ)) (b := (32019383951 / 20000000000000 : ℝ)) (q := (446360521029 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12864])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12864])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12864]

theorem cert12864_9 : CellCertificate 12864 (441082500663199 / 5000000000000000 : ℝ) (65312004538767 / 40000000000000000 : ℝ) (329717489067069 / 10000000000000000 : ℝ)
    (cell12864 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · have h := gap_lower (n := 12864) (a := (83760125622083 / 100000000000000 : ℝ)) (b := (32019383951 / 20000000000000 : ℝ)) (q := (2231806604317 / 100000000000000 : ℝ))
      (E := (cell12864 ⟨9, by decide⟩).energy) (xi := (329717489067069 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12864 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12864]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12864])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12864) (a := (83760125622083 / 100000000000000 : ℝ)) (b := (32019383951 / 20000000000000 : ℝ)) (q := (2231806604317 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12864])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12864])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12864]

theorem cert12864_10 : CellCertificate 12864 (441082500663199 / 5000000000000000 : ℝ) (65312004538767 / 40000000000000000 : ℝ) (329717489067069 / 10000000000000000 : ℝ)
    (cell12864 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · have h := gap_lower (n := 12864) (a := (16745085010369 / 20000000000000 : ℝ)) (b := (32019383951 / 20000000000000 : ℝ)) (q := (557952659801 / 25000000000000 : ℝ))
      (E := (cell12864 ⟨10, by decide⟩).energy) (xi := (329717489067069 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12864 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12864]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12864])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12864) (a := (16745085010369 / 20000000000000 : ℝ)) (b := (32019383951 / 20000000000000 : ℝ)) (q := (557952659801 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12864])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12864])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12864]

theorem cert12864_11 : CellCertificate 12864 (441082500663199 / 5000000000000000 : ℝ) (65312004538767 / 40000000000000000 : ℝ) (329717489067069 / 10000000000000000 : ℝ)
    (cell12864 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · have h := gap_lower (n := 12864) (a := (20922687255537 / 25000000000000 : ℝ)) (b := (32019383951 / 20000000000000 : ℝ)) (q := (2231814658243 / 100000000000000 : ℝ))
      (E := (cell12864 ⟨11, by decide⟩).energy) (xi := (329717489067069 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12864 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12864]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12864])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12864) (a := (20922687255537 / 25000000000000 : ℝ)) (b := (32019383951 / 20000000000000 : ℝ)) (q := (2231814658243 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12864])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12864])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12864]

theorem cert12864_12 : CellCertificate 12864 (441082500663199 / 5000000000000000 : ℝ) (65312004538767 / 40000000000000000 : ℝ) (329717489067069 / 10000000000000000 : ℝ)
    (cell12864 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · have h := gap_lower (n := 12864) (a := (83656097498329 / 100000000000000 : ℝ)) (b := (32019383951 / 20000000000000 : ℝ)) (q := (1115909333817 / 50000000000000 : ℝ))
      (E := (cell12864 ⟨12, by decide⟩).energy) (xi := (329717489067069 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12864 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12864]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12864])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12864) (a := (83656097498329 / 100000000000000 : ℝ)) (b := (32019383951 / 20000000000000 : ℝ)) (q := (1115909333817 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12864])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12864])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12864]

theorem cert12864_13 : CellCertificate 12864 (441082500663199 / 5000000000000000 : ℝ) (65312004538767 / 40000000000000000 : ℝ) (329717489067069 / 10000000000000000 : ℝ)
    (cell12864 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · have h := gap_lower (n := 12864) (a := (16724294089181 / 20000000000000 : ℝ)) (b := (32019383951 / 20000000000000 : ℝ)) (q := (1115911307601 / 50000000000000 : ℝ))
      (E := (cell12864 ⟨13, by decide⟩).energy) (xi := (329717489067069 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12864 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12864]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12864])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12864) (a := (16724294089181 / 20000000000000 : ℝ)) (b := (32019383951 / 20000000000000 : ℝ)) (q := (1115911307601 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12864])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12864])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12864]

theorem cert12864_14 : CellCertificate 12864 (441082500663199 / 5000000000000000 : ℝ) (65312004538767 / 40000000000000000 : ℝ) (329717489067069 / 10000000000000000 : ℝ)
    (cell12864 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · have h := gap_lower (n := 12864) (a := (83586867830573 / 100000000000000 : ℝ)) (b := (32019383951 / 20000000000000 : ℝ)) (q := (2231826622893 / 100000000000000 : ℝ))
      (E := (cell12864 ⟨14, by decide⟩).energy) (xi := (329717489067069 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12864 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12864]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12864])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12864) (a := (83586867830573 / 100000000000000 : ℝ)) (b := (32019383951 / 20000000000000 : ℝ)) (q := (2231826622893 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12864])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12864])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12864]

theorem cert12864_15 : CellCertificate 12864 (441082500663199 / 5000000000000000 : ℝ) (65312004538767 / 40000000000000000 : ℝ) (329717489067069 / 10000000000000000 : ℝ)
    (cell12864 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · have h := gap_lower (n := 12864) (a := (83552289618207 / 100000000000000 : ℝ)) (b := (32019383951 / 20000000000000 : ℝ)) (q := (139489414879 / 6250000000000 : ℝ))
      (E := (cell12864 ⟨15, by decide⟩).energy) (xi := (329717489067069 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12864 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12864]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12864])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12864) (a := (83552289618207 / 100000000000000 : ℝ)) (b := (32019383951 / 20000000000000 : ℝ)) (q := (139489414879 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12864])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12864])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12864]

theorem cert12864_16 : CellCertificate 12864 (441082500663199 / 5000000000000000 : ℝ) (65312004538767 / 40000000000000000 : ℝ) (329717489067069 / 10000000000000000 : ℝ)
    (cell12864 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · have h := gap_lower (n := 12864) (a := (83517735774859 / 100000000000000 : ℝ)) (b := (32019383951 / 20000000000000 : ℝ)) (q := (2231834665933 / 100000000000000 : ℝ))
      (E := (cell12864 ⟨16, by decide⟩).energy) (xi := (329717489067069 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12864 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12864]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12864])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12864) (a := (83517735774859 / 100000000000000 : ℝ)) (b := (32019383951 / 20000000000000 : ℝ)) (q := (2231834665933 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12864])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12864])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12864]

theorem cert12864_17 : CellCertificate 12864 (441082500663199 / 5000000000000000 : ℝ) (65312004538767 / 40000000000000000 : ℝ) (329717489067069 / 10000000000000000 : ℝ)
    (cell12864 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · have h := gap_lower (n := 12864) (a := (83483206266757 / 100000000000000 : ℝ)) (b := (32019383951 / 20000000000000 : ℝ)) (q := (1115919326627 / 50000000000000 : ℝ))
      (E := (cell12864 ⟨17, by decide⟩).energy) (xi := (329717489067069 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12864 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12864]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12864])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12864) (a := (83483206266757 / 100000000000000 : ℝ)) (b := (32019383951 / 20000000000000 : ℝ)) (q := (1115919326627 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12864])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12864])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12864]

theorem cert12864_18 : CellCertificate 12864 (441082500663199 / 5000000000000000 : ℝ) (65312004538767 / 40000000000000000 : ℝ) (329717489067069 / 10000000000000000 : ℝ)
    (cell12864 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · have h := gap_lower (n := 12864) (a := (83448701060301 / 100000000000000 : ℝ)) (b := (32019383951 / 20000000000000 : ℝ)) (q := (111592133147 / 5000000000000 : ℝ))
      (E := (cell12864 ⟨18, by decide⟩).energy) (xi := (329717489067069 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12864 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12864]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12864])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12864) (a := (83448701060301 / 100000000000000 : ℝ)) (b := (32019383951 / 20000000000000 : ℝ)) (q := (111592133147 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12864])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12864])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12864]

theorem cert12864_19 : CellCertificate 12864 (441082500663199 / 5000000000000000 : ℝ) (65312004538767 / 40000000000000000 : ℝ) (329717489067069 / 10000000000000000 : ℝ)
    (cell12864 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · have h := gap_lower (n := 12864) (a := (20853555030517 / 25000000000000 : ℝ)) (b := (32019383951 / 20000000000000 : ℝ)) (q := (2231846641213 / 100000000000000 : ℝ))
      (E := (cell12864 ⟨19, by decide⟩).energy) (xi := (329717489067069 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12864 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12864]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12864])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12864) (a := (20853555030517 / 25000000000000 : ℝ)) (b := (32019383951 / 20000000000000 : ℝ)) (q := (2231846641213 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12864])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12864])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12864]

theorem cert12865_0 : CellCertificate 12865 (882137746121419 / 10000000000000000 : ℝ) (102042072141961 / 62500000000000000 : ℝ) (329691251398487 / 10000000000000000 : ℝ)
    (cell12865 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · have h := gap_lower (n := 12865) (a := (42036763072173 / 50000000000000 : ℝ)) (b := (160084327613 / 100000000000000 : ℝ)) (q := (1115826467399 / 50000000000000 : ℝ))
      (E := (cell12865 ⟨0, by decide⟩).energy) (xi := (329691251398487 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12865 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12865]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12865])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12865) (a := (42036763072173 / 50000000000000 : ℝ)) (b := (160084327613 / 100000000000000 : ℝ)) (q := (1115826467399 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12865])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12865])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12865]

theorem cert12865_1 : CellCertificate 12865 (882137746121419 / 10000000000000000 : ℝ) (102042072141961 / 62500000000000000 : ℝ) (329691251398487 / 10000000000000000 : ℝ)
    (cell12865 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · have h := gap_lower (n := 12865) (a := (42019301716423 / 50000000000000 : ℝ)) (b := (160084327613 / 100000000000000 : ℝ)) (q := (139478559097 / 6250000000000 : ℝ))
      (E := (cell12865 ⟨1, by decide⟩).energy) (xi := (329691251398487 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12865 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12865]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12865])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12865) (a := (42019301716423 / 50000000000000 : ℝ)) (b := (160084327613 / 100000000000000 : ℝ)) (q := (139478559097 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12865])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12865])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12865]

theorem cert12865_2 : CellCertificate 12865 (882137746121419 / 10000000000000000 : ℝ) (102042072141961 / 62500000000000000 : ℝ) (329691251398487 / 10000000000000000 : ℝ)
    (cell12865 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · have h := gap_lower (n := 12865) (a := (84003705581719 / 100000000000000 : ℝ)) (b := (160084327613 / 100000000000000 : ℝ)) (q := (1115830465777 / 50000000000000 : ℝ))
      (E := (cell12865 ⟨2, by decide⟩).energy) (xi := (329691251398487 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12865 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12865]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12865])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12865) (a := (84003705581719 / 100000000000000 : ℝ)) (b := (160084327613 / 100000000000000 : ℝ)) (q := (1115830465777 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12865])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12865])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12865]

theorem cert12865_3 : CellCertificate 12865 (882137746121419 / 10000000000000000 : ℝ) (102042072141961 / 62500000000000000 : ℝ) (329691251398487 / 10000000000000000 : ℝ)
    (cell12865 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · have h := gap_lower (n := 12865) (a := (41984416277313 / 50000000000000 : ℝ)) (b := (160084327613 / 100000000000000 : ℝ)) (q := (1115832479623 / 50000000000000 : ℝ))
      (E := (cell12865 ⟨3, by decide⟩).energy) (xi := (329691251398487 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12865 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12865]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12865])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12865) (a := (41984416277313 / 50000000000000 : ℝ)) (b := (160084327613 / 100000000000000 : ℝ)) (q := (1115832479623 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12865])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12865])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12865]

theorem cert12865_4 : CellCertificate 12865 (882137746121419 / 10000000000000000 : ℝ) (102042072141961 / 62500000000000000 : ℝ) (329691251398487 / 10000000000000000 : ℝ)
    (cell12865 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · have h := gap_lower (n := 12865) (a := (83933984315421 / 100000000000000 : ℝ)) (b := (160084327613 / 100000000000000 : ℝ)) (q := (2231668921147 / 100000000000000 : ℝ))
      (E := (cell12865 ⟨4, by decide⟩).energy) (xi := (329691251398487 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12865 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12865]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12865])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12865) (a := (83933984315421 / 100000000000000 : ℝ)) (b := (160084327613 / 100000000000000 : ℝ)) (q := (2231668921147 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12865])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12865])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12865]

theorem cert12865_5 : CellCertificate 12865 (882137746121419 / 10000000000000000 : ℝ) (102042072141961 / 62500000000000000 : ℝ) (329691251398487 / 10000000000000000 : ℝ)
    (cell12865 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · have h := gap_lower (n := 12865) (a := (16779832165629 / 20000000000000 : ℝ)) (b := (160084327613 / 100000000000000 : ℝ)) (q := (2231672941107 / 100000000000000 : ℝ))
      (E := (cell12865 ⟨5, by decide⟩).energy) (xi := (329691251398487 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12865 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12865]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12865])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12865) (a := (16779832165629 / 20000000000000 : ℝ)) (b := (160084327613 / 100000000000000 : ℝ)) (q := (2231672941107 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12865])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12865])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12865]

theorem cert12865_6 : CellCertificate 12865 (882137746121419 / 10000000000000000 : ℝ) (102042072141961 / 62500000000000000 : ℝ) (329691251398487 / 10000000000000000 : ℝ)
    (cell12865 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · have h := gap_lower (n := 12865) (a := (83864362057031 / 100000000000000 : ℝ)) (b := (160084327613 / 100000000000000 : ℝ)) (q := (1115838455519 / 50000000000000 : ℝ))
      (E := (cell12865 ⟨6, by decide⟩).energy) (xi := (329691251398487 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12865 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12865]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12865])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12865) (a := (83864362057031 / 100000000000000 : ℝ)) (b := (160084327613 / 100000000000000 : ℝ)) (q := (1115838455519 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12865])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12865])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12865]

theorem cert12865_7 : CellCertificate 12865 (882137746121419 / 10000000000000000 : ℝ) (102042072141961 / 62500000000000000 : ℝ) (329691251398487 / 10000000000000000 : ℝ)
    (cell12865 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · have h := gap_lower (n := 12865) (a := (2619674623953 / 3125000000000 : ℝ)) (b := (160084327613 / 100000000000000 : ℝ)) (q := (3570689527 / 160000000000 : ℝ))
      (E := (cell12865 ⟨7, by decide⟩).energy) (xi := (329691251398487 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12865 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12865]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12865])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12865) (a := (2619674623953 / 3125000000000 : ℝ)) (b := (160084327613 / 100000000000000 : ℝ)) (q := (3570689527 / 160000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12865])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12865])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12865]

theorem cert12865_8 : CellCertificate 12865 (882137746121419 / 10000000000000000 : ℝ) (102042072141961 / 62500000000000000 : ℝ) (329691251398487 / 10000000000000000 : ℝ)
    (cell12865 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · have h := gap_lower (n := 12865) (a := (41897419260573 / 50000000000000 : ℝ)) (b := (160084327613 / 100000000000000 : ℝ)) (q := (2231684962431 / 100000000000000 : ℝ))
      (E := (cell12865 ⟨8, by decide⟩).energy) (xi := (329691251398487 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12865 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12865]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12865])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12865) (a := (41897419260573 / 50000000000000 : ℝ)) (b := (160084327613 / 100000000000000 : ℝ)) (q := (2231684962431 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12865])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12865])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12865]

theorem cert12865_9 : CellCertificate 12865 (882137746121419 / 10000000000000000 : ℝ) (102042072141961 / 62500000000000000 : ℝ) (329691251398487 / 10000000000000000 : ℝ)
    (cell12865 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · have h := gap_lower (n := 12865) (a := (20940028421443 / 25000000000000 : ℝ)) (b := (160084327613 / 100000000000000 : ℝ)) (q := (1115844471077 / 50000000000000 : ℝ))
      (E := (cell12865 ⟨9, by decide⟩).energy) (xi := (329691251398487 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12865 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12865]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12865])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12865) (a := (20940028421443 / 25000000000000 : ℝ)) (b := (160084327613 / 100000000000000 : ℝ)) (q := (1115844471077 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12865])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12865])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12865]

theorem cert12865_10 : CellCertificate 12865 (882137746121419 / 10000000000000000 : ℝ) (102042072141961 / 62500000000000000 : ℝ) (329691251398487 / 10000000000000000 : ℝ)
    (cell12865 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · have h := gap_lower (n := 12865) (a := (83725413425347 / 100000000000000 : ℝ)) (b := (160084327613 / 100000000000000 : ℝ)) (q := (1115846479151 / 50000000000000 : ℝ))
      (E := (cell12865 ⟨10, by decide⟩).energy) (xi := (329691251398487 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12865 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12865]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12865])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12865) (a := (83725413425347 / 100000000000000 : ℝ)) (b := (160084327613 / 100000000000000 : ℝ)) (q := (1115846479151 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12865])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12865])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12865]

theorem cert12865_11 : CellCertificate 12865 (882137746121419 / 10000000000000000 : ℝ) (102042072141961 / 62500000000000000 : ℝ) (329691251398487 / 10000000000000000 : ℝ)
    (cell12865 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · have h := gap_lower (n := 12865) (a := (20922684426257 / 25000000000000 : ℝ)) (b := (160084327613 / 100000000000000 : ℝ)) (q := (139481059957 / 6250000000000 : ℝ))
      (E := (cell12865 ⟨11, by decide⟩).energy) (xi := (329691251398487 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12865 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12865]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12865])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12865) (a := (20922684426257 / 25000000000000 : ℝ)) (b := (160084327613 / 100000000000000 : ℝ)) (q := (139481059957 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12865])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12865])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12865]

theorem cert12865_12 : CellCertificate 12865 (882137746121419 / 10000000000000000 : ℝ) (102042072141961 / 62500000000000000 : ℝ) (329691251398487 / 10000000000000000 : ℝ)
    (cell12865 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · have h := gap_lower (n := 12865) (a := (83656086490153 / 100000000000000 : ℝ)) (b := (160084327613 / 100000000000000 : ℝ)) (q := (2231700951383 / 100000000000000 : ℝ))
      (E := (cell12865 ⟨12, by decide⟩).energy) (xi := (329691251398487 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12865 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12865]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12865])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12865) (a := (83656086490153 / 100000000000000 : ℝ)) (b := (160084327613 / 100000000000000 : ℝ)) (q := (2231700951383 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12865])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12865])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12865]

theorem cert12865_13 : CellCertificate 12865 (882137746121419 / 10000000000000000 : ℝ) (102042072141961 / 62500000000000000 : ℝ) (329691251398487 / 10000000000000000 : ℝ)
    (cell12865 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · have h := gap_lower (n := 12865) (a := (261317061707 / 312500000000 : ℝ)) (b := (160084327613 / 100000000000000 : ℝ)) (q := (223170494047 / 10000000000000 : ℝ))
      (E := (cell12865 ⟨13, by decide⟩).energy) (xi := (329691251398487 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12865 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12865]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12865])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12865) (a := (261317061707 / 312500000000 : ℝ)) (b := (160084327613 / 100000000000000 : ℝ)) (q := (223170494047 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12865])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12865])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12865]

theorem cert12865_14 : CellCertificate 12865 (882137746121419 / 10000000000000000 : ℝ) (102042072141961 / 62500000000000000 : ℝ) (329691251398487 / 10000000000000000 : ℝ)
    (cell12865 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · have h := gap_lower (n := 12865) (a := (83586857438987 / 100000000000000 : ℝ)) (b := (160084327613 / 100000000000000 : ℝ)) (q := (2231708990433 / 100000000000000 : ℝ))
      (E := (cell12865 ⟨14, by decide⟩).energy) (xi := (329691251398487 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12865 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12865]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12865])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12865) (a := (83586857438987 / 100000000000000 : ℝ)) (b := (160084327613 / 100000000000000 : ℝ)) (q := (2231708990433 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12865])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12865])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12865]

theorem cert12865_15 : CellCertificate 12865 (882137746121419 / 10000000000000000 : ℝ) (102042072141961 / 62500000000000000 : ℝ) (329691251398487 / 10000000000000000 : ℝ)
    (cell12865 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · have h := gap_lower (n := 12865) (a := (8355227953427 / 10000000000000 : ℝ)) (b := (160084327613 / 100000000000000 : ℝ)) (q := (2231712990451 / 100000000000000 : ℝ))
      (E := (cell12865 ⟨15, by decide⟩).energy) (xi := (329691251398487 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12865 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12865]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12865])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12865) (a := (8355227953427 / 10000000000000 : ℝ)) (b := (160084327613 / 100000000000000 : ℝ)) (q := (2231712990451 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12865])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12865])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12865]

theorem cert12865_16 : CellCertificate 12865 (882137746121419 / 10000000000000000 : ℝ) (102042072141961 / 62500000000000000 : ℝ) (329691251398487 / 10000000000000000 : ℝ)
    (cell12865 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · have h := gap_lower (n := 12865) (a := (83517725998141 / 100000000000000 : ℝ)) (b := (160084327613 / 100000000000000 : ℝ)) (q := (278964618209 / 12500000000000 : ℝ))
      (E := (cell12865 ⟨16, by decide⟩).energy) (xi := (329691251398487 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12865 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12865]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12865])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12865) (a := (83517725998141 / 100000000000000 : ℝ)) (b := (160084327613 / 100000000000000 : ℝ)) (q := (278964618209 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12865])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12865])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12865]

theorem cert12865_17 : CellCertificate 12865 (882137746121419 / 10000000000000000 : ℝ) (102042072141961 / 62500000000000000 : ℝ) (329691251398487 / 10000000000000000 : ℝ)
    (cell12865 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · have h := gap_lower (n := 12865) (a := (83483196796827 / 100000000000000 : ℝ)) (b := (160084327613 / 100000000000000 : ℝ)) (q := (557930244363 / 25000000000000 : ℝ))
      (E := (cell12865 ⟨17, by decide⟩).energy) (xi := (329691251398487 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12865 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12865]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12865])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12865) (a := (83483196796827 / 100000000000000 : ℝ)) (b := (160084327613 / 100000000000000 : ℝ)) (q := (557930244363 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12865])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12865])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12865]

theorem cert12865_18 : CellCertificate 12865 (882137746121419 / 10000000000000000 : ℝ) (102042072141961 / 62500000000000000 : ℝ) (329691251398487 / 10000000000000000 : ℝ)
    (cell12865 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · have h := gap_lower (n := 12865) (a := (83448691896733 / 100000000000000 : ℝ)) (b := (160084327613 / 100000000000000 : ℝ)) (q := (2231724974097 / 100000000000000 : ℝ))
      (E := (cell12865 ⟨18, by decide⟩).energy) (xi := (329691251398487 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12865 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12865]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12865])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12865) (a := (83448691896733 / 100000000000000 : ℝ)) (b := (160084327613 / 100000000000000 : ℝ)) (q := (2231724974097 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12865])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12865])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12865]

theorem cert12865_19 : CellCertificate 12865 (882137746121419 / 10000000000000000 : ℝ) (102042072141961 / 62500000000000000 : ℝ) (329691251398487 / 10000000000000000 : ℝ)
    (cell12865 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · have h := gap_lower (n := 12865) (a := (83414211264433 / 100000000000000 : ℝ)) (b := (160084327613 / 100000000000000 : ℝ)) (q := (446345799661 / 20000000000000 : ℝ))
      (E := (cell12865 ⟨19, by decide⟩).energy) (xi := (329691251398487 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12865 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12865]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12865])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12865) (a := (83414211264433 / 100000000000000 : ℝ)) (b := (160084327613 / 100000000000000 : ℝ)) (q := (446345799661 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12865])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12865])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12865]

theorem cert12866_0 : CellCertificate 12866 (882110494979257 / 10000000000000000 : ℝ) (816273107407797 / 500000000000000000 : ℝ) (329665017950351 / 10000000000000000 : ℝ)
    (cell12866 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · have h := gap_lower (n := 12866) (a := (42036755701153 / 50000000000000 : ℝ)) (b := (80035868731 / 50000000000000 : ℝ)) (q := (446307059071 / 20000000000000 : ℝ))
      (E := (cell12866 ⟨0, by decide⟩).energy) (xi := (329665017950351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12866 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12866]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12866])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12866) (a := (42036755701153 / 50000000000000 : ℝ)) (b := (80035868731 / 50000000000000 : ℝ)) (q := (446307059071 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12866])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12866])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12866]

theorem cert12866_1 : CellCertificate 12866 (882110494979257 / 10000000000000000 : ℝ) (816273107407797 / 500000000000000000 : ℝ) (329665017950351 / 10000000000000000 : ℝ)
    (cell12866 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · have h := gap_lower (n := 12866) (a := (16807717800907 / 20000000000000 : ℝ)) (b := (80035868731 / 50000000000000 : ℝ)) (q := (2231539280911 / 100000000000000 : ℝ))
      (E := (cell12866 ⟨1, by decide⟩).energy) (xi := (329665017950351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12866 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12866]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12866])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12866) (a := (16807717800907 / 20000000000000 : ℝ)) (b := (80035868731 / 50000000000000 : ℝ)) (q := (2231539280911 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12866])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12866])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12866]

theorem cert12866_2 : CellCertificate 12866 (882110494979257 / 10000000000000000 : ℝ) (816273107407797 / 500000000000000000 : ℝ) (329665017950351 / 10000000000000000 : ℝ)
    (cell12866 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · have h := gap_lower (n := 12866) (a := (84003691466693 / 100000000000000 : ℝ)) (b := (80035868731 / 50000000000000 : ℝ)) (q := (2231543300307 / 100000000000000 : ℝ))
      (E := (cell12866 ⟨2, by decide⟩).energy) (xi := (329665017950351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12866 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12866]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12866])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12866) (a := (84003691466693 / 100000000000000 : ℝ)) (b := (80035868731 / 50000000000000 : ℝ)) (q := (2231543300307 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12866])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12866])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12866]

theorem cert12866_3 : CellCertificate 12866 (882110494979257 / 10000000000000000 : ℝ) (816273107407797 / 500000000000000000 : ℝ) (329665017950351 / 10000000000000000 : ℝ)
    (cell12866 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · have h := gap_lower (n := 12866) (a := (20992204688111 / 25000000000000 : ℝ)) (b := (80035868731 / 50000000000000 : ℝ)) (q := (2231547304259 / 100000000000000 : ℝ))
      (E := (cell12866 ⟨3, by decide⟩).energy) (xi := (329665017950351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12866 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12866]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12866])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12866) (a := (20992204688111 / 25000000000000 : ℝ)) (b := (80035868731 / 50000000000000 : ℝ)) (q := (2231547304259 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12866])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12866])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12866]

theorem cert12866_4 : CellCertificate 12866 (882110494979257 / 10000000000000000 : ℝ) (816273107407797 / 500000000000000000 : ℝ) (329665017950351 / 10000000000000000 : ℝ)
    (cell12866 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · have h := gap_lower (n := 12866) (a := (83933970825641 / 100000000000000 : ℝ)) (b := (80035868731 / 50000000000000 : ℝ)) (q := (2231551301057 / 100000000000000 : ℝ))
      (E := (cell12866 ⟨4, by decide⟩).energy) (xi := (329665017950351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12866 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12866]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12866])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12866) (a := (83933970825641 / 100000000000000 : ℝ)) (b := (80035868731 / 50000000000000 : ℝ)) (q := (2231551301057 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12866])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12866])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12866]

theorem cert12866_5 : CellCertificate 12866 (882110494979257 / 10000000000000000 : ℝ) (816273107407797 / 500000000000000000 : ℝ) (329665017950351 / 10000000000000000 : ℝ)
    (cell12866 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · have h := gap_lower (n := 12866) (a := (83899147650327 / 100000000000000 : ℝ)) (b := (80035868731 / 50000000000000 : ℝ)) (q := (557888824683 / 25000000000000 : ℝ))
      (E := (cell12866 ⟨5, by decide⟩).energy) (xi := (329665017950351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12866 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12866]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12866])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12866) (a := (83899147650327 / 100000000000000 : ℝ)) (b := (80035868731 / 50000000000000 : ℝ)) (q := (557888824683 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12866])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12866])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12866]

theorem cert12866_6 : CellCertificate 12866 (882110494979257 / 10000000000000000 : ℝ) (816273107407797 / 500000000000000000 : ℝ) (329665017950351 / 10000000000000000 : ℝ)
    (cell12866 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · have h := gap_lower (n := 12866) (a := (16772869838147 / 20000000000000 : ℝ)) (b := (80035868731 / 50000000000000 : ℝ)) (q := (2231559305059 / 100000000000000 : ℝ))
      (E := (cell12866 ⟨6, by decide⟩).energy) (xi := (329665017950351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12866 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12866]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12866])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12866) (a := (16772869838147 / 20000000000000 : ℝ)) (b := (80035868731 / 50000000000000 : ℝ)) (q := (2231559305059 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12866])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12866])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12866]

theorem cert12866_7 : CellCertificate 12866 (882110494979257 / 10000000000000000 : ℝ) (816273107407797 / 500000000000000000 : ℝ) (329665017950351 / 10000000000000000 : ℝ)
    (cell12866 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · have h := gap_lower (n := 12866) (a := (16765915082257 / 20000000000000 : ℝ)) (b := (80035868731 / 50000000000000 : ℝ)) (q := (2231563269571 / 100000000000000 : ℝ))
      (E := (cell12866 ⟨7, by decide⟩).energy) (xi := (329665017950351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12866 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12866]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12866])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12866) (a := (16765915082257 / 20000000000000 : ℝ)) (b := (80035868731 / 50000000000000 : ℝ)) (q := (2231563269571 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12866])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12866])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12866]

theorem cert12866_8 : CellCertificate 12866 (882110494979257 / 10000000000000000 : ℝ) (816273107407797 / 500000000000000000 : ℝ) (329665017950351 / 10000000000000000 : ℝ)
    (cell12866 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · have h := gap_lower (n := 12866) (a := (83794826276583 / 100000000000000 : ℝ)) (b := (80035868731 / 50000000000000 : ℝ)) (q := (1115783657747 / 50000000000000 : ℝ))
      (E := (cell12866 ⟨8, by decide⟩).energy) (xi := (329665017950351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12866 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12866]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12866])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12866) (a := (83794826276583 / 100000000000000 : ℝ)) (b := (80035868731 / 50000000000000 : ℝ)) (q := (1115783657747 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12866])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12866])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12866]

theorem cert12866_9 : CellCertificate 12866 (882110494979257 / 10000000000000000 : ℝ) (816273107407797 / 500000000000000000 : ℝ) (329665017950351 / 10000000000000000 : ℝ)
    (cell12866 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · have h := gap_lower (n := 12866) (a := (83760101751419 / 100000000000000 : ℝ)) (b := (80035868731 / 50000000000000 : ℝ)) (q := (2231571275807 / 100000000000000 : ℝ))
      (E := (cell12866 ⟨9, by decide⟩).energy) (xi := (329665017950351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12866 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12866]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12866])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12866) (a := (83760101751419 / 100000000000000 : ℝ)) (b := (80035868731 / 50000000000000 : ℝ)) (q := (2231571275807 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12866])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12866])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12866]

theorem cert12866_10 : CellCertificate 12866 (882110494979257 / 10000000000000000 : ℝ) (816273107407797 / 500000000000000000 : ℝ) (329665017950351 / 10000000000000000 : ℝ)
    (cell12866 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · have h := gap_lower (n := 12866) (a := (83725401800769 / 100000000000000 : ℝ)) (b := (80035868731 / 50000000000000 : ℝ)) (q := (446315054651 / 20000000000000 : ℝ))
      (E := (cell12866 ⟨10, by decide⟩).energy) (xi := (329665017950351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12866 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12866]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12866])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12866) (a := (83725401800769 / 100000000000000 : ℝ)) (b := (80035868731 / 50000000000000 : ℝ)) (q := (446315054651 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12866])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12866])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12866]

theorem cert12866_11 : CellCertificate 12866 (882110494979257 / 10000000000000000 : ℝ) (816273107407797 / 500000000000000000 : ℝ) (329665017950351 / 10000000000000000 : ℝ)
    (cell12866 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · have h := gap_lower (n := 12866) (a := (83690726389791 / 100000000000000 : ℝ)) (b := (80035868731 / 50000000000000 : ℝ)) (q := (1115789657179 / 50000000000000 : ℝ))
      (E := (cell12866 ⟨11, by decide⟩).energy) (xi := (329665017950351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12866 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12866]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12866])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12866) (a := (83690726389791 / 100000000000000 : ℝ)) (b := (80035868731 / 50000000000000 : ℝ)) (q := (1115789657179 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12866])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12866])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12866]

theorem cert12866_12 : CellCertificate 12866 (882110494979257 / 10000000000000000 : ℝ) (816273107407797 / 500000000000000000 : ℝ) (329665017950351 / 10000000000000000 : ℝ)
    (cell12866 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · have h := gap_lower (n := 12866) (a := (83656075483823 / 100000000000000 : ℝ)) (b := (80035868731 / 50000000000000 : ℝ)) (q := (223158328917 / 10000000000000 : ℝ))
      (E := (cell12866 ⟨12, by decide⟩).energy) (xi := (329665017950351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12866 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12866]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12866])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12866) (a := (83656075483823 / 100000000000000 : ℝ)) (b := (80035868731 / 50000000000000 : ℝ)) (q := (223158328917 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12866])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12866])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12866]

theorem cert12866_13 : CellCertificate 12866 (882110494979257 / 10000000000000000 : ℝ) (816273107407797 / 500000000000000000 : ℝ) (329665017950351 / 10000000000000000 : ℝ)
    (cell12866 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · have h := gap_lower (n := 12866) (a := (1306585141381 / 1562500000000 : ℝ)) (b := (80035868731 / 50000000000000 : ℝ)) (q := (2231587319837 / 100000000000000 : ℝ))
      (E := (cell12866 ⟨13, by decide⟩).energy) (xi := (329665017950351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12866 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12866]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12866])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12866) (a := (1306585141381 / 1562500000000 : ℝ)) (b := (80035868731 / 50000000000000 : ℝ)) (q := (2231587319837 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12866])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12866])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12866]

theorem cert12866_14 : CellCertificate 12866 (882110494979257 / 10000000000000000 : ℝ) (816273107407797 / 500000000000000000 : ℝ) (329665017950351 / 10000000000000000 : ℝ)
    (cell12866 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · have h := gap_lower (n := 12866) (a := (41793423524587 / 50000000000000 : ℝ)) (b := (80035868731 / 50000000000000 : ℝ)) (q := (89263651833 / 4000000000000 : ℝ))
      (E := (cell12866 ⟨14, by decide⟩).energy) (xi := (329665017950351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12866 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12866]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12866])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12866) (a := (41793423524587 / 50000000000000 : ℝ)) (b := (80035868731 / 50000000000000 : ℝ)) (q := (89263651833 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12866])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12866])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12866]

theorem cert12866_15 : CellCertificate 12866 (882110494979257 / 10000000000000000 : ℝ) (816273107407797 / 500000000000000000 : ℝ) (329665017950351 / 10000000000000000 : ℝ)
    (cell12866 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · have h := gap_lower (n := 12866) (a := (20888067363017 / 25000000000000 : ℝ)) (b := (80035868731 / 50000000000000 : ℝ)) (q := (2231595338883 / 100000000000000 : ℝ))
      (E := (cell12866 ⟨15, by decide⟩).energy) (xi := (329665017950351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12866 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12866]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12866])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12866) (a := (20888067363017 / 25000000000000 : ℝ)) (b := (80035868731 / 50000000000000 : ℝ)) (q := (2231595338883 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12866])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12866])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12866]

theorem cert12866_16 : CellCertificate 12866 (882110494979257 / 10000000000000000 : ℝ) (816273107407797 / 500000000000000000 : ℝ) (329665017950351 / 10000000000000000 : ℝ)
    (cell12866 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · have h := gap_lower (n := 12866) (a := (83517716223121 / 100000000000000 : ℝ)) (b := (80035868731 / 50000000000000 : ℝ)) (q := (446319867579 / 20000000000000 : ℝ))
      (E := (cell12866 ⟨16, by decide⟩).energy) (xi := (329665017950351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12866 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12866]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12866])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12866) (a := (83517716223121 / 100000000000000 : ℝ)) (b := (80035868731 / 50000000000000 : ℝ)) (q := (446319867579 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12866])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12866])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12866]

theorem cert12866_17 : CellCertificate 12866 (882110494979257 / 10000000000000000 : ℝ) (816273107407797 / 500000000000000000 : ℝ) (329665017950351 / 10000000000000000 : ℝ)
    (cell12866 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · have h := gap_lower (n := 12866) (a := (1043539841607 / 1250000000000 : ℝ)) (b := (80035868731 / 50000000000000 : ℝ)) (q := (278950412221 / 12500000000000 : ℝ))
      (E := (cell12866 ⟨17, by decide⟩).energy) (xi := (329665017950351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12866 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12866]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12866])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12866) (a := (1043539841607 / 1250000000000 : ℝ)) (b := (80035868731 / 50000000000000 : ℝ)) (q := (278950412221 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12866])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12866])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12866]

theorem cert12866_18 : CellCertificate 12866 (882110494979257 / 10000000000000000 : ℝ) (816273107407797 / 500000000000000000 : ℝ) (329665017950351 / 10000000000000000 : ℝ)
    (cell12866 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · have h := gap_lower (n := 12866) (a := (83448682734789 / 100000000000000 : ℝ)) (b := (80035868731 / 50000000000000 : ℝ)) (q := (2231607339661 / 100000000000000 : ℝ))
      (E := (cell12866 ⟨18, by decide⟩).energy) (xi := (329665017950351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12866 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12866]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12866])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12866) (a := (83448682734789 / 100000000000000 : ℝ)) (b := (80035868731 / 50000000000000 : ℝ)) (q := (2231607339661 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12866])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12866])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12866]

theorem cert12866_19 : CellCertificate 12866 (882110494979257 / 10000000000000000 : ℝ) (816273107407797 / 500000000000000000 : ℝ) (329665017950351 / 10000000000000000 : ℝ)
    (cell12866 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · have h := gap_lower (n := 12866) (a := (41707101204193 / 50000000000000 : ℝ)) (b := (80035868731 / 50000000000000 : ℝ)) (q := (2231611351593 / 100000000000000 : ℝ))
      (E := (cell12866 ⟨19, by decide⟩).energy) (xi := (329665017950351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12866 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12866]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12866])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12866) (a := (41707101204193 / 50000000000000 : ℝ)) (b := (80035868731 / 50000000000000 : ℝ)) (q := (2231611351593 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12866])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12866])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12866]

theorem cert12867_0 : CellCertificate 12867 (11026040598737 / 125000000000000 : ℝ) (1632419295097223 / 1000000000000000000 : ℝ) (329638788721569 / 10000000000000000 : ℝ)
    (cell12867 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · have h := gap_lower (n := 12867) (a := (84073496662561 / 100000000000000 : ℝ)) (b := (160059149303 / 100000000000000 : ℝ)) (q := (1115708825691 / 50000000000000 : ℝ))
      (E := (cell12867 ⟨0, by decide⟩).energy) (xi := (329638788721569 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12867 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12867]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12867])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12867) (a := (84073496662561 / 100000000000000 : ℝ)) (b := (160059149303 / 100000000000000 : ℝ)) (q := (1115708825691 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12867])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12867])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12867]

theorem cert12867_1 : CellCertificate 12867 (11026040598737 / 125000000000000 : ℝ) (1632419295097223 / 1000000000000000000 : ℝ) (329638788721569 / 10000000000000000 : ℝ)
    (cell12867 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · have h := gap_lower (n := 12867) (a := (84038574578481 / 100000000000000 : ℝ)) (b := (160059149303 / 100000000000000 : ℝ)) (q := (2231421669629 / 100000000000000 : ℝ))
      (E := (cell12867 ⟨1, by decide⟩).energy) (xi := (329638788721569 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12867 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12867]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12867])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12867) (a := (84038574578481 / 100000000000000 : ℝ)) (b := (160059149303 / 100000000000000 : ℝ)) (q := (2231421669629 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12867])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12867])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12867]

theorem cert12867_2 : CellCertificate 12867 (11026040598737 / 125000000000000 : ℝ) (1632419295097223 / 1000000000000000000 : ℝ) (329638788721569 / 10000000000000000 : ℝ)
    (cell12867 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · have h := gap_lower (n := 12867) (a := (84003677353887 / 100000000000000 : ℝ)) (b := (160059149303 / 100000000000000 : ℝ)) (q := (2231425664607 / 100000000000000 : ℝ))
      (E := (cell12867 ⟨2, by decide⟩).energy) (xi := (329638788721569 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12867 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12867]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12867])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12867) (a := (84003677353887 / 100000000000000 : ℝ)) (b := (160059149303 / 100000000000000 : ℝ)) (q := (2231425664607 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12867])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12867])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12867]

theorem cert12867_3 : CellCertificate 12867 (11026040598737 / 125000000000000 : ℝ) (1632419295097223 / 1000000000000000000 : ℝ) (329638788721569 / 10000000000000000 : ℝ)
    (cell12867 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · have h := gap_lower (n := 12867) (a := (83968804952443 / 100000000000000 : ℝ)) (b := (160059149303 / 100000000000000 : ℝ)) (q := (2231429644859 / 100000000000000 : ℝ))
      (E := (cell12867 ⟨3, by decide⟩).energy) (xi := (329638788721569 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12867 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12867]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12867])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12867) (a := (83968804952443 / 100000000000000 : ℝ)) (b := (160059149303 / 100000000000000 : ℝ)) (q := (2231429644859 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12867])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12867])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12867]

theorem cert12867_4 : CellCertificate 12867 (11026040598737 / 125000000000000 : ℝ) (1632419295097223 / 1000000000000000000 : ℝ) (329638788721569 / 10000000000000000 : ℝ)
    (cell12867 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · have h := gap_lower (n := 12867) (a := (16786791467601 / 20000000000000 : ℝ)) (b := (160059149303 / 100000000000000 : ℝ)) (q := (139464604787 / 6250000000000 : ℝ))
      (E := (cell12867 ⟨4, by decide⟩).energy) (xi := (329638788721569 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12867 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12867]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12867])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12867) (a := (16786791467601 / 20000000000000 : ℝ)) (b := (160059149303 / 100000000000000 : ℝ)) (q := (139464604787 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12867])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12867])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12867]

theorem cert12867_5 : CellCertificate 12867 (11026040598737 / 125000000000000 : ℝ) (1632419295097223 / 1000000000000000000 : ℝ) (329638788721569 / 10000000000000000 : ℝ)
    (cell12867 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · have h := gap_lower (n := 12867) (a := (10487391809327 / 12500000000000 : ℝ)) (b := (160059149303 / 100000000000000 : ℝ)) (q := (2231437652019 / 100000000000000 : ℝ))
      (E := (cell12867 ⟨5, by decide⟩).energy) (xi := (329638788721569 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12867 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12867]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12867])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12867) (a := (10487391809327 / 12500000000000 : ℝ)) (b := (160059149303 / 100000000000000 : ℝ)) (q := (2231437652019 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12867])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12867])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12867]

theorem cert12867_6 : CellCertificate 12867 (11026040598737 / 125000000000000 : ℝ) (1632419295097223 / 1000000000000000000 : ℝ) (329638788721569 / 10000000000000000 : ℝ)
    (cell12867 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · have h := gap_lower (n := 12867) (a := (83864336326509 / 100000000000000 : ℝ)) (b := (160059149303 / 100000000000000 : ℝ)) (q := (1115720818407 / 50000000000000 : ℝ))
      (E := (cell12867 ⟨6, by decide⟩).energy) (xi := (329638788721569 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12867 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12867]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12867])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12867) (a := (83864336326509 / 100000000000000 : ℝ)) (b := (160059149303 / 100000000000000 : ℝ)) (q := (1115720818407 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12867])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12867])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12867]

theorem cert12867_7 : CellCertificate 12867 (11026040598737 / 125000000000000 : ℝ) (1632419295097223 / 1000000000000000000 : ℝ) (329638788721569 / 10000000000000000 : ℝ)
    (cell12867 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · have h := gap_lower (n := 12867) (a := (41914781429053 / 50000000000000 : ℝ)) (b := (160059149303 / 100000000000000 : ℝ)) (q := (2231445638497 / 100000000000000 : ℝ))
      (E := (cell12867 ⟨7, by decide⟩).energy) (xi := (329638788721569 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12867 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12867]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12867])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12867) (a := (41914781429053 / 50000000000000 : ℝ)) (b := (160059149303 / 100000000000000 : ℝ)) (q := (2231445638497 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12867])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12867])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12867]

theorem cert12867_8 : CellCertificate 12867 (11026040598737 / 125000000000000 : ℝ) (1632419295097223 / 1000000000000000000 : ℝ) (329638788721569 / 10000000000000000 : ℝ)
    (cell12867 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · have h := gap_lower (n := 12867) (a := (83794814034013 / 100000000000000 : ℝ)) (b := (160059149303 / 100000000000000 : ℝ)) (q := (2231449664337 / 100000000000000 : ℝ))
      (E := (cell12867 ⟨8, by decide⟩).energy) (xi := (329638788721569 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12867 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12867]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12867])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12867) (a := (83794814034013 / 100000000000000 : ℝ)) (b := (160059149303 / 100000000000000 : ℝ)) (q := (2231449664337 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12867])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12867])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12867]

theorem cert12867_9 : CellCertificate 12867 (11026040598737 / 125000000000000 : ℝ) (1632419295097223 / 1000000000000000000 : ℝ) (329638788721569 / 10000000000000000 : ℝ)
    (cell12867 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · have h := gap_lower (n := 12867) (a := (83760089819023 / 100000000000000 : ℝ)) (b := (160059149303 / 100000000000000 : ℝ)) (q := (2231453663313 / 100000000000000 : ℝ))
      (E := (cell12867 ⟨9, by decide⟩).energy) (xi := (329638788721569 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12867 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12867]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12867])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12867) (a := (83760089819023 / 100000000000000 : ℝ)) (b := (160059149303 / 100000000000000 : ℝ)) (q := (2231453663313 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12867])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12867])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12867]

theorem cert12867_10 : CellCertificate 12867 (11026040598737 / 125000000000000 : ℝ) (1632419295097223 / 1000000000000000000 : ℝ) (329638788721569 / 10000000000000000 : ℝ)
    (cell12867 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · have h := gap_lower (n := 12867) (a := (1308209221533 / 1562500000000 : ℝ)) (b := (160059149303 / 100000000000000 : ℝ)) (q := (1115728821061 / 50000000000000 : ℝ))
      (E := (cell12867 ⟨10, by decide⟩).energy) (xi := (329638788721569 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12867 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12867]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12867])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12867) (a := (1308209221533 / 1562500000000 : ℝ)) (b := (160059149303 / 100000000000000 : ℝ)) (q := (1115728821061 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12867])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12867])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12867]

theorem cert12867_11 : CellCertificate 12867 (11026040598737 / 125000000000000 : ℝ) (1632419295097223 / 1000000000000000000 : ℝ) (329638788721569 / 10000000000000000 : ℝ)
    (cell12867 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · have h := gap_lower (n := 12867) (a := (83690715076437 / 100000000000000 : ℝ)) (b := (160059149303 / 100000000000000 : ℝ)) (q := (139466354081 / 6250000000000 : ℝ))
      (E := (cell12867 ⟨11, by decide⟩).energy) (xi := (329638788721569 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12867 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12867]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12867])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12867) (a := (83690715076437 / 100000000000000 : ℝ)) (b := (160059149303 / 100000000000000 : ℝ)) (q := (139466354081 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12867])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12867])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12867]

theorem cert12867_12 : CellCertificate 12867 (11026040598737 / 125000000000000 : ℝ) (1632419295097223 / 1000000000000000000 : ℝ) (329638788721569 / 10000000000000000 : ℝ)
    (cell12867 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · have h := gap_lower (n := 12867) (a := (83656064479339 / 100000000000000 : ℝ)) (b := (160059149303 / 100000000000000 : ℝ)) (q := (446293136199 / 20000000000000 : ℝ))
      (E := (cell12867 ⟨12, by decide⟩).energy) (xi := (329638788721569 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12867 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12867]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12867])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12867) (a := (83656064479339 / 100000000000000 : ℝ)) (b := (160059149303 / 100000000000000 : ℝ)) (q := (446293136199 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12867])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12867])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12867]

theorem cert12867_13 : CellCertificate 12867 (11026040598737 / 125000000000000 : ℝ) (1632419295097223 / 1000000000000000000 : ℝ) (329638788721569 / 10000000000000000 : ℝ)
    (cell12867 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · have h := gap_lower (n := 12867) (a := (41810719176169 / 50000000000000 : ℝ)) (b := (160059149303 / 100000000000000 : ℝ)) (q := (2231469695171 / 100000000000000 : ℝ))
      (E := (cell12867 ⟨13, by decide⟩).energy) (xi := (329638788721569 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12867 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12867]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12867])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12867) (a := (41810719176169 / 50000000000000 : ℝ)) (b := (160059149303 / 100000000000000 : ℝ)) (q := (2231469695171 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12867])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12867])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12867]

theorem cert12867_14 : CellCertificate 12867 (11026040598737 / 125000000000000 : ℝ) (1632419295097223 / 1000000000000000000 : ℝ) (329638788721569 / 10000000000000000 : ℝ)
    (cell12867 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · have h := gap_lower (n := 12867) (a := (83586836661133 / 100000000000000 : ℝ)) (b := (160059149303 / 100000000000000 : ℝ)) (q := (2231473655377 / 100000000000000 : ℝ))
      (E := (cell12867 ⟨14, by decide⟩).energy) (xi := (329638788721569 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12867 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12867]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12867])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12867) (a := (83586836661133 / 100000000000000 : ℝ)) (b := (160059149303 / 100000000000000 : ℝ)) (q := (2231473655377 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12867])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12867])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12867]

theorem cert12867_15 : CellCertificate 12867 (11026040598737 / 125000000000000 : ℝ) (1632419295097223 / 1000000000000000000 : ℝ) (329638788721569 / 10000000000000000 : ℝ)
    (cell12867 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · have h := gap_lower (n := 12867) (a := (41776129685801 / 50000000000000 : ℝ)) (b := (160059149303 / 100000000000000 : ℝ)) (q := (1115738841679 / 50000000000000 : ℝ))
      (E := (cell12867 ⟨15, by decide⟩).energy) (xi := (329638788721569 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12867 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12867]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12867])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12867) (a := (41776129685801 / 50000000000000 : ℝ)) (b := (160059149303 / 100000000000000 : ℝ)) (q := (1115738841679 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12867])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12867])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12867]

theorem cert12867_16 : CellCertificate 12867 (11026040598737 / 125000000000000 : ℝ) (1632419295097223 / 1000000000000000000 : ℝ) (329638788721569 / 10000000000000000 : ℝ)
    (cell12867 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · have h := gap_lower (n := 12867) (a := (83517706449799 / 100000000000000 : ℝ)) (b := (160059149303 / 100000000000000 : ℝ)) (q := (2231481667999 / 100000000000000 : ℝ))
      (E := (cell12867 ⟨16, by decide⟩).energy) (xi := (329638788721569 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12867 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12867]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12867])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12867) (a := (83517706449799 / 100000000000000 : ℝ)) (b := (160059149303 / 100000000000000 : ℝ)) (q := (2231481667999 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12867])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12867])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12867]

theorem cert12867_17 : CellCertificate 12867 (11026040598737 / 125000000000000 : ℝ) (1632419295097223 / 1000000000000000000 : ℝ) (329638788721569 / 10000000000000000 : ℝ)
    (cell12867 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · have h := gap_lower (n := 12867) (a := (41741588930977 / 50000000000000 : ℝ)) (b := (160059149303 / 100000000000000 : ℝ)) (q := (2231485672429 / 100000000000000 : ℝ))
      (E := (cell12867 ⟨17, by decide⟩).energy) (xi := (329638788721569 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12867 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12867]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12867])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12867) (a := (41741588930977 / 50000000000000 : ℝ)) (b := (160059149303 / 100000000000000 : ℝ)) (q := (2231485672429 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12867])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12867])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12867]

theorem cert12867_18 : CellCertificate 12867 (11026040598737 / 125000000000000 : ℝ) (1632419295097223 / 1000000000000000000 : ℝ) (329638788721569 / 10000000000000000 : ℝ)
    (cell12867 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · have h := gap_lower (n := 12867) (a := (83448673574471 / 100000000000000 : ℝ)) (b := (160059149303 / 100000000000000 : ℝ)) (q := (111574485069 / 5000000000000 : ℝ))
      (E := (cell12867 ⟨18, by decide⟩).energy) (xi := (329638788721569 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12867 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12867]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12867])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12867) (a := (83448673574471 / 100000000000000 : ℝ)) (b := (160059149303 / 100000000000000 : ℝ)) (q := (111574485069 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12867])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12867])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12867]

theorem cert12867_19 : CellCertificate 12867 (11026040598737 / 125000000000000 : ℝ) (1632419295097223 / 1000000000000000000 : ℝ) (329638788721569 / 10000000000000000 : ℝ)
    (cell12867 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · have h := gap_lower (n := 12867) (a := (10426774194241 / 12500000000000 : ℝ)) (b := (160059149303 / 100000000000000 : ℝ)) (q := (1115746850537 / 50000000000000 : ℝ))
      (E := (cell12867 ⟨19, by decide⟩).energy) (xi := (329638788721569 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12867 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12867]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12867])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12867) (a := (10426774194241 / 12500000000000 : ℝ)) (b := (160059149303 / 100000000000000 : ℝ)) (q := (1115746850537 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12867])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12867])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12867]

theorem cert12868_0 : CellCertificate 12868 (35282240195183 / 400000000000000 : ℝ) (816146197555831 / 500000000000000000 : ℝ) (6592251274221 / 200000000000000 : ℝ)
    (cell12868 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · have h := gap_lower (n := 12868) (a := (8407348192511 / 10000000000000 : ℝ)) (b := (32009312627 / 20000000000000 : ℝ)) (q := (557825015177 / 25000000000000 : ℝ))
      (E := (cell12868 ⟨0, by decide⟩).energy) (xi := (6592251274221 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12868 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12868]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12868])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12868) (a := (8407348192511 / 10000000000000 : ℝ)) (b := (32009312627 / 20000000000000 : ℝ)) (q := (557825015177 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12868])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12868])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12868]

theorem cert12868_1 : CellCertificate 12868 (35282240195183 / 400000000000000 : ℝ) (816146197555831 / 500000000000000000 : ℝ) (6592251274221 / 200000000000000 : ℝ)
    (cell12868 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · have h := gap_lower (n := 12868) (a := (42019280077341 / 50000000000000 : ℝ)) (b := (32009312627 / 20000000000000 : ℝ)) (q := (2231304053859 / 100000000000000 : ℝ))
      (E := (cell12868 ⟨1, by decide⟩).energy) (xi := (6592251274221 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12868 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12868]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12868])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12868) (a := (42019280077341 / 50000000000000 : ℝ)) (b := (32009312627 / 20000000000000 : ℝ)) (q := (2231304053859 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12868])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12868])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12868]

theorem cert12868_2 : CellCertificate 12868 (35282240195183 / 400000000000000 : ℝ) (816146197555831 / 500000000000000000 : ℝ) (6592251274221 / 200000000000000 : ℝ)
    (cell12868 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · have h := gap_lower (n := 12868) (a := (84003663243299 / 100000000000000 : ℝ)) (b := (32009312627 / 20000000000000 : ℝ)) (q := (2231308024457 / 100000000000000 : ℝ))
      (E := (cell12868 ⟨2, by decide⟩).energy) (xi := (6592251274221 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12868 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12868]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12868])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12868) (a := (84003663243299 / 100000000000000 : ℝ)) (b := (32009312627 / 20000000000000 : ℝ)) (q := (2231308024457 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12868])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12868])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12868]

theorem cert12868_3 : CellCertificate 12868 (35282240195183 / 400000000000000 : ℝ) (816146197555831 / 500000000000000000 : ℝ) (6592251274221 / 200000000000000 : ℝ)
    (cell12868 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · have h := gap_lower (n := 12868) (a := (1312012361791 / 1562500000000 : ℝ)) (b := (32009312627 / 20000000000000 : ℝ)) (q := (2231312038943 / 100000000000000 : ℝ))
      (E := (cell12868 ⟨3, by decide⟩).energy) (xi := (6592251274221 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12868 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12868]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12868])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12868) (a := (1312012361791 / 1562500000000 : ℝ)) (b := (32009312627 / 20000000000000 : ℝ)) (q := (2231312038943 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12868])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12868])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12868]

theorem cert12868_4 : CellCertificate 12868 (35282240195183 / 400000000000000 : ℝ) (816146197555831 / 500000000000000000 : ℝ) (6592251274221 / 200000000000000 : ℝ)
    (cell12868 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · have h := gap_lower (n := 12868) (a := (2622935745391 / 3125000000000 : ℝ)) (b := (32009312627 / 20000000000000 : ℝ)) (q := (2231316047753 / 100000000000000 : ℝ))
      (E := (cell12868 ⟨4, by decide⟩).energy) (xi := (6592251274221 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12868 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12868]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12868])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12868) (a := (2622935745391 / 3125000000000 : ℝ)) (b := (32009312627 / 20000000000000 : ℝ)) (q := (2231316047753 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12868])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12868])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12868]

theorem cert12868_5 : CellCertificate 12868 (35282240195183 / 400000000000000 : ℝ) (816146197555831 / 500000000000000000 : ℝ) (6592251274221 / 200000000000000 : ℝ)
    (cell12868 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · have h := gap_lower (n := 12868) (a := (8389912130101 / 10000000000000 : ℝ)) (b := (32009312627 / 20000000000000 : ℝ)) (q := (557830014729 / 25000000000000 : ℝ))
      (E := (cell12868 ⟨5, by decide⟩).energy) (xi := (6592251274221 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12868 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12868]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12868])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12868) (a := (8389912130101 / 10000000000000 : ℝ)) (b := (32009312627 / 20000000000000 : ℝ)) (q := (557830014729 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12868])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12868])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12868]

theorem cert12868_6 : CellCertificate 12868 (35282240195183 / 400000000000000 : ℝ) (816146197555831 / 500000000000000000 : ℝ) (6592251274221 / 200000000000000 : ℝ)
    (cell12868 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · have h := gap_lower (n := 12868) (a := (2620760108261 / 3125000000000 : ℝ)) (b := (32009312627 / 20000000000000 : ℝ)) (q := (1115662040103 / 50000000000000 : ℝ))
      (E := (cell12868 ⟨6, by decide⟩).energy) (xi := (6592251274221 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12868 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12868]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12868])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12868) (a := (2620760108261 / 3125000000000 : ℝ)) (b := (32009312627 / 20000000000000 : ℝ)) (q := (1115662040103 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12868])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12868])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12868]

theorem cert12868_7 : CellCertificate 12868 (35282240195183 / 400000000000000 : ℝ) (816146197555831 / 500000000000000000 : ℝ) (6592251274221 / 200000000000000 : ℝ)
    (cell12868 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · have h := gap_lower (n := 12868) (a := (41914775153479 / 50000000000000 : ℝ)) (b := (32009312627 / 20000000000000 : ℝ)) (q := (446265612231 / 20000000000000 : ℝ))
      (E := (cell12868 ⟨7, by decide⟩).energy) (xi := (6592251274221 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12868 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12868]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12868])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12868) (a := (41914775153479 / 50000000000000 : ℝ)) (b := (32009312627 / 20000000000000 : ℝ)) (q := (446265612231 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12868])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12868])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12868]

theorem cert12868_8 : CellCertificate 12868 (35282240195183 / 400000000000000 : ℝ) (816146197555831 / 500000000000000000 : ℝ) (6592251274221 / 200000000000000 : ℝ)
    (cell12868 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · have h := gap_lower (n := 12868) (a := (41897400896719 / 50000000000000 : ℝ)) (b := (32009312627 / 20000000000000 : ℝ)) (q := (557833016743 / 25000000000000 : ℝ))
      (E := (cell12868 ⟨8, by decide⟩).energy) (xi := (6592251274221 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12868 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12868]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12868])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12868) (a := (41897400896719 / 50000000000000 : ℝ)) (b := (32009312627 / 20000000000000 : ℝ)) (q := (557833016743 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12868])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12868])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12868]

theorem cert12868_9 : CellCertificate 12868 (35282240195183 / 400000000000000 : ℝ) (816146197555831 / 500000000000000000 : ℝ) (6592251274221 / 200000000000000 : ℝ)
    (cell12868 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · have h := gap_lower (n := 12868) (a := (16752015577717 / 20000000000000 : ℝ)) (b := (32009312627 / 20000000000000 : ℝ)) (q := (2231336046637 / 100000000000000 : ℝ))
      (E := (cell12868 ⟨9, by decide⟩).energy) (xi := (6592251274221 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12868 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12868]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12868])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12868) (a := (16752015577717 / 20000000000000 : ℝ)) (b := (32009312627 / 20000000000000 : ℝ)) (q := (2231336046637 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12868])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12868])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12868]

theorem cert12868_10 : CellCertificate 12868 (35282240195183 / 400000000000000 : ℝ) (816146197555831 / 500000000000000000 : ℝ) (6592251274221 / 200000000000000 : ℝ)
    (cell12868 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · have h := gap_lower (n := 12868) (a := (41862689278687 / 50000000000000 : ℝ)) (b := (32009312627 / 20000000000000 : ℝ)) (q := (1115670032453 / 50000000000000 : ℝ))
      (E := (cell12868 ⟨10, by decide⟩).energy) (xi := (6592251274221 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12868 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12868]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12868])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12868) (a := (41862689278687 / 50000000000000 : ℝ)) (b := (32009312627 / 20000000000000 : ℝ)) (q := (1115670032453 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12868])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12868])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12868]

theorem cert12868_11 : CellCertificate 12868 (35282240195183 / 400000000000000 : ℝ) (816146197555831 / 500000000000000000 : ℝ) (6592251274221 / 200000000000000 : ℝ)
    (cell12868 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · have h := gap_lower (n := 12868) (a := (16738140752993 / 20000000000000 : ℝ)) (b := (32009312627 / 20000000000000 : ℝ)) (q := (557836017553 / 25000000000000 : ℝ))
      (E := (cell12868 ⟨11, by decide⟩).energy) (xi := (6592251274221 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12868 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12868]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12868])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12868) (a := (16738140752993 / 20000000000000 : ℝ)) (b := (32009312627 / 20000000000000 : ℝ)) (q := (557836017553 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12868])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12868])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12868]

theorem cert12868_12 : CellCertificate 12868 (35282240195183 / 400000000000000 : ℝ) (816146197555831 / 500000000000000000 : ℝ) (6592251274221 / 200000000000000 : ℝ)
    (cell12868 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · have h := gap_lower (n := 12868) (a := (836560534767 / 1000000000000 : ℝ)) (b := (32009312627 / 20000000000000 : ℝ)) (q := (139459254297 / 6250000000000 : ℝ))
      (E := (cell12868 ⟨12, by decide⟩).energy) (xi := (6592251274221 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12868 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12868]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12868])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12868) (a := (836560534767 / 1000000000000 : ℝ)) (b := (32009312627 / 20000000000000 : ℝ)) (q := (139459254297 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12868])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12868])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12868]

theorem cert12868_13 : CellCertificate 12868 (35282240195183 / 400000000000000 : ℝ) (816146197555831 / 500000000000000000 : ℝ) (6592251274221 / 200000000000000 : ℝ)
    (cell12868 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · have h := gap_lower (n := 12868) (a := (836214276581 / 1000000000000 : ℝ)) (b := (32009312627 / 20000000000000 : ℝ)) (q := (557838016619 / 25000000000000 : ℝ))
      (E := (cell12868 ⟨13, by decide⟩).energy) (xi := (6592251274221 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12868 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12868]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12868])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12868) (a := (836214276581 / 1000000000000 : ℝ)) (b := (32009312627 / 20000000000000 : ℝ)) (q := (557838016619 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12868])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12868])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12868]

theorem cert12868_14 : CellCertificate 12868 (35282240195183 / 400000000000000 : ℝ) (816146197555831 / 500000000000000000 : ℝ) (6592251274221 / 200000000000000 : ℝ)
    (cell12868 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · have h := gap_lower (n := 12868) (a := (5224176642179 / 6250000000000 : ℝ)) (b := (32009312627 / 20000000000000 : ℝ)) (q := (2231356069091 / 100000000000000 : ℝ))
      (E := (cell12868 ⟨14, by decide⟩).energy) (xi := (6592251274221 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12868 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12868]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12868])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12868) (a := (5224176642179 / 6250000000000 : ℝ)) (b := (32009312627 / 20000000000000 : ℝ)) (q := (2231356069091 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12868])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12868])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12868]

theorem cert12868_15 : CellCertificate 12868 (35282240195183 / 400000000000000 : ℝ) (816146197555831 / 500000000000000000 : ℝ) (6592251274221 / 200000000000000 : ℝ)
    (cell12868 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · have h := gap_lower (n := 12868) (a := (83552249292871 / 100000000000000 : ℝ)) (b := (32009312627 / 20000000000000 : ℝ)) (q := (278920010257 / 12500000000000 : ℝ))
      (E := (cell12868 ⟨15, by decide⟩).energy) (xi := (6592251274221 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12868 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12868]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12868])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12868) (a := (83552249292871 / 100000000000000 : ℝ)) (b := (32009312627 / 20000000000000 : ℝ)) (q := (278920010257 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12868])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12868])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12868]

theorem cert12868_16 : CellCertificate 12868 (35282240195183 / 400000000000000 : ℝ) (816146197555831 / 500000000000000000 : ℝ) (6592251274221 / 200000000000000 : ℝ)
    (cell12868 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · have h := gap_lower (n := 12868) (a := (3340707867127 / 4000000000000 : ℝ)) (b := (32009312627 / 20000000000000 : ℝ)) (q := (557841027647 / 25000000000000 : ℝ))
      (E := (cell12868 ⟨16, by decide⟩).energy) (xi := (6592251274221 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12868 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12868]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12868])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12868) (a := (3340707867127 / 4000000000000 : ℝ)) (b := (32009312627 / 20000000000000 : ℝ)) (q := (557841027647 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12868])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12868])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12868]

theorem cert12868_17 : CellCertificate 12868 (35282240195183 / 400000000000000 : ℝ) (816146197555831 / 500000000000000000 : ℝ) (6592251274221 / 200000000000000 : ℝ)
    (cell12868 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · have h := gap_lower (n := 12868) (a := (83483168397009 / 100000000000000 : ℝ)) (b := (32009312627 / 20000000000000 : ℝ)) (q := (1115684050717 / 50000000000000 : ℝ))
      (E := (cell12868 ⟨17, by decide⟩).energy) (xi := (6592251274221 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12868 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12868]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12868])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12868) (a := (83483168397009 / 100000000000000 : ℝ)) (b := (32009312627 / 20000000000000 : ℝ)) (q := (1115684050717 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12868])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12868])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12868]

theorem cert12868_18 : CellCertificate 12868 (35282240195183 / 400000000000000 : ℝ) (816146197555831 / 500000000000000000 : ℝ) (6592251274221 / 200000000000000 : ℝ)
    (cell12868 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · have h := gap_lower (n := 12868) (a := (83448664415777 / 100000000000000 : ℝ)) (b := (32009312627 / 20000000000000 : ℝ)) (q := (1115686058753 / 50000000000000 : ℝ))
      (E := (cell12868 ⟨18, by decide⟩).energy) (xi := (6592251274221 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12868 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12868]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12868])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12868) (a := (83448664415777 / 100000000000000 : ℝ)) (b := (32009312627 / 20000000000000 : ℝ)) (q := (1115686058753 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12868])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12868])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12868]

theorem cert12868_19 : CellCertificate 12868 (35282240195183 / 400000000000000 : ℝ) (816146197555831 / 500000000000000000 : ℝ) (6592251274221 / 200000000000000 : ℝ)
    (cell12868 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · have h := gap_lower (n := 12868) (a := (83414184701057 / 100000000000000 : ℝ)) (b := (32009312627 / 20000000000000 : ℝ)) (q := (2231376105023 / 100000000000000 : ℝ))
      (E := (cell12868 ⟨19, by decide⟩).energy) (xi := (6592251274221 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12868 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12868]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12868])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12868) (a := (83414184701057 / 100000000000000 : ℝ)) (b := (32009312627 / 20000000000000 : ℝ)) (q := (2231376105023 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12868])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12868])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12868]

theorem cert12869_0 : CellCertificate 12869 (17640575318403 / 200000000000000 : ℝ) (1632165514854307 / 1000000000000000000 : ℝ) (329586342917701 / 10000000000000000 : ℝ)
    (cell12869 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · have h := gap_lower (n := 12869) (a := (1313647924843 / 1562500000000 : ℝ)) (b := (160033978957 / 100000000000000 : ℝ)) (q := (2231182465509 / 100000000000000 : ℝ))
      (E := (cell12869 ⟨0, by decide⟩).energy) (xi := (329586342917701 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12869 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12869]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12869])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12869) (a := (1313647924843 / 1562500000000 : ℝ)) (b := (160033978957 / 100000000000000 : ℝ)) (q := (2231182465509 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12869])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12869])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12869]

theorem cert12869_1 : CellCertificate 12869 (17640575318403 / 200000000000000 : ℝ) (1632165514854307 / 1000000000000000000 : ℝ) (329586342917701 / 10000000000000000 : ℝ)
    (cell12869 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · have h := gap_lower (n := 12869) (a := (4201927286657 / 5000000000000 : ℝ)) (b := (160033978957 / 100000000000000 : ℝ)) (q := (2231186491451 / 100000000000000 : ℝ))
      (E := (cell12869 ⟨1, by decide⟩).energy) (xi := (329586342917701 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12869 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12869]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12869])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12869) (a := (4201927286657 / 5000000000000 : ℝ)) (b := (160033978957 / 100000000000000 : ℝ)) (q := (2231186491451 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12869])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12869])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12869]

theorem cert12869_2 : CellCertificate 12869 (17640575318403 / 200000000000000 : ℝ) (1632165514854307 / 1000000000000000000 : ℝ) (329586342917701 / 10000000000000000 : ℝ)
    (cell12869 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · have h := gap_lower (n := 12869) (a := (84003649134929 / 100000000000000 : ℝ)) (b := (160033978957 / 100000000000000 : ℝ)) (q := (446238099121 / 20000000000000 : ℝ))
      (E := (cell12869 ⟨2, by decide⟩).energy) (xi := (329586342917701 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12869 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12869]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12869])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12869) (a := (84003649134929 / 100000000000000 : ℝ)) (b := (160033978957 / 100000000000000 : ℝ)) (q := (446238099121 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12869])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12869])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12869]

theorem cert12869_3 : CellCertificate 12869 (17640575318403 / 200000000000000 : ℝ) (1632165514854307 / 1000000000000000000 : ℝ) (329586342917701 / 10000000000000000 : ℝ)
    (cell12869 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · have h := gap_lower (n := 12869) (a := (16793755471797 / 20000000000000 : ℝ)) (b := (160033978957 / 100000000000000 : ℝ)) (q := (2231194486513 / 100000000000000 : ℝ))
      (E := (cell12869 ⟨3, by decide⟩).energy) (xi := (329586342917701 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12869 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12869]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12869])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12869) (a := (16793755471797 / 20000000000000 : ℝ)) (b := (160033978957 / 100000000000000 : ℝ)) (q := (2231194486513 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12869])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12869])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12869]

theorem cert12869_4 : CellCertificate 12869 (17640575318403 / 200000000000000 : ℝ) (1632165514854307 / 1000000000000000000 : ℝ) (329586342917701 / 10000000000000000 : ℝ)
    (cell12869 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · have h := gap_lower (n := 12869) (a := (83933930369163 / 100000000000000 : ℝ)) (b := (160033978957 / 100000000000000 : ℝ)) (q := (1115599236231 / 50000000000000 : ℝ))
      (E := (cell12869 ⟨4, by decide⟩).energy) (xi := (329586342917701 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12869 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12869]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12869])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12869) (a := (83933930369163 / 100000000000000 : ℝ)) (b := (160033978957 / 100000000000000 : ℝ)) (q := (1115599236231 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12869])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12869])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12869]

theorem cert12869_5 : CellCertificate 12869 (17640575318403 / 200000000000000 : ℝ) (1632165514854307 / 1000000000000000000 : ℝ) (329586342917701 / 10000000000000000 : ℝ)
    (cell12869 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · have h := gap_lower (n := 12869) (a := (8389910812951 / 10000000000000 : ℝ)) (b := (160033978957 / 100000000000000 : ℝ)) (q := (1115601230739 / 50000000000000 : ℝ))
      (E := (cell12869 ⟨5, by decide⟩).energy) (xi := (329586342917701 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12869 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12869]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12869])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12869) (a := (8389910812951 / 10000000000000 : ℝ)) (b := (160033978957 / 100000000000000 : ℝ)) (q := (1115601230739 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12869])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12869])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12869]

theorem cert12869_6 : CellCertificate 12869 (17640575318403 / 200000000000000 : ℝ) (1632165514854307 / 1000000000000000000 : ℝ) (329586342917701 / 10000000000000000 : ℝ)
    (cell12869 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · have h := gap_lower (n := 12869) (a := (83864310604263 / 100000000000000 : ℝ)) (b := (160033978957 / 100000000000000 : ℝ)) (q := (446241292267 / 20000000000000 : ℝ))
      (E := (cell12869 ⟨6, by decide⟩).energy) (xi := (329586342917701 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12869 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12869]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12869])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12869) (a := (83864310604263 / 100000000000000 : ℝ)) (b := (160033978957 / 100000000000000 : ℝ)) (q := (446241292267 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12869])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12869])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12869]

theorem cert12869_7 : CellCertificate 12869 (17640575318403 / 200000000000000 : ℝ) (1632165514854307 / 1000000000000000000 : ℝ) (329586342917701 / 10000000000000000 : ℝ)
    (cell12869 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · have h := gap_lower (n := 12869) (a := (41914768878921 / 50000000000000 : ℝ)) (b := (160033978957 / 100000000000000 : ℝ)) (q := (446242095911 / 20000000000000 : ℝ))
      (E := (cell12869 ⟨7, by decide⟩).energy) (xi := (329586342917701 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12869 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12869]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12869])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12869) (a := (41914768878921 / 50000000000000 : ℝ)) (b := (160033978957 / 100000000000000 : ℝ)) (q := (446242095911 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12869])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12869])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12869]

theorem cert12869_8 : CellCertificate 12869 (17640575318403 / 200000000000000 : ℝ) (1632165514854307 / 1000000000000000000 : ℝ) (329586342917701 / 10000000000000000 : ℝ)
    (cell12869 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · have h := gap_lower (n := 12869) (a := (83794789554857 / 100000000000000 : ℝ)) (b := (160033978957 / 100000000000000 : ℝ)) (q := (557803616347 / 25000000000000 : ℝ))
      (E := (cell12869 ⟨8, by decide⟩).energy) (xi := (329586342917701 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12869 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12869]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12869])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12869) (a := (83794789554857 / 100000000000000 : ℝ)) (b := (160033978957 / 100000000000000 : ℝ)) (q := (557803616347 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12869])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12869])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12869]

theorem cert12869_9 : CellCertificate 12869 (17640575318403 / 200000000000000 : ℝ) (1632165514854307 / 1000000000000000000 : ℝ) (329586342917701 / 10000000000000000 : ℝ)
    (cell12869 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · have h := gap_lower (n := 12869) (a := (41880032980051 / 50000000000000 : ℝ)) (b := (160033978957 / 100000000000000 : ℝ)) (q := (1115609241909 / 50000000000000 : ℝ))
      (E := (cell12869 ⟨9, by decide⟩).energy) (xi := (329586342917701 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12869 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12869]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12869])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12869) (a := (41880032980051 / 50000000000000 : ℝ)) (b := (160033978957 / 100000000000000 : ℝ)) (q := (1115609241909 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12869])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12869])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12869]

theorem cert12869_10 : CellCertificate 12869 (17640575318403 / 200000000000000 : ℝ) (1632165514854307 / 1000000000000000000 : ℝ) (329586342917701 / 10000000000000000 : ℝ)
    (cell12869 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · have h := gap_lower (n := 12869) (a := (16745073387711 / 20000000000000 : ℝ)) (b := (160033978957 / 100000000000000 : ℝ)) (q := (557805620887 / 25000000000000 : ℝ))
      (E := (cell12869 ⟨10, by decide⟩).energy) (xi := (329586342917701 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12869 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12869]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12869])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12869) (a := (16745073387711 / 20000000000000 : ℝ)) (b := (160033978957 / 100000000000000 : ℝ)) (q := (557805620887 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12869])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12869])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12869]

theorem cert12869_11 : CellCertificate 12869 (17640575318403 / 200000000000000 : ℝ) (1632165514854307 / 1000000000000000000 : ℝ) (329586342917701 / 10000000000000000 : ℝ)
    (cell12869 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · have h := gap_lower (n := 12869) (a := (5230668278461 / 6250000000000 : ℝ)) (b := (160033978957 / 100000000000000 : ℝ)) (q := (2231226471023 / 100000000000000 : ℝ))
      (E := (cell12869 ⟨11, by decide⟩).energy) (xi := (329586342917701 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12869 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12869]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12869])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12869) (a := (5230668278461 / 6250000000000 : ℝ)) (b := (160033978957 / 100000000000000 : ℝ)) (q := (2231226471023 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12869])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12869])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12869]

theorem cert12869_12 : CellCertificate 12869 (17640575318403 / 200000000000000 : ℝ) (1632165514854307 / 1000000000000000000 : ℝ) (329586342917701 / 10000000000000000 : ℝ)
    (cell12869 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · have h := gap_lower (n := 12869) (a := (83656042475907 / 100000000000000 : ℝ)) (b := (160033978957 / 100000000000000 : ℝ)) (q := (557807627637 / 25000000000000 : ℝ))
      (E := (cell12869 ⟨12, by decide⟩).energy) (xi := (329586342917701 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12869 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12869]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12869])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12869) (a := (83656042475907 / 100000000000000 : ℝ)) (b := (160033978957 / 100000000000000 : ℝ)) (q := (557807627637 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12869])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12869])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12869]

theorem cert12869_13 : CellCertificate 12869 (17640575318403 / 200000000000000 : ℝ) (1632165514854307 / 1000000000000000000 : ℝ) (329586342917701 / 10000000000000000 : ℝ)
    (cell12869 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · have h := gap_lower (n := 12869) (a := (8362141696567 / 10000000000000 : ℝ)) (b := (160033978957 / 100000000000000 : ℝ)) (q := (1115617245941 / 50000000000000 : ℝ))
      (E := (cell12869 ⟨13, by decide⟩).energy) (xi := (329586342917701 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12869 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12869]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12869])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12869) (a := (8362141696567 / 10000000000000 : ℝ)) (b := (160033978957 / 100000000000000 : ℝ)) (q := (1115617245941 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12869])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12869])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12869]

theorem cert12869_14 : CellCertificate 12869 (17640575318403 / 200000000000000 : ℝ) (1632165514854307 / 1000000000000000000 : ℝ) (329586342917701 / 10000000000000000 : ℝ)
    (cell12869 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · have h := gap_lower (n := 12869) (a := (16717363178073 / 20000000000000 : ℝ)) (b := (160033978957 / 100000000000000 : ℝ)) (q := (1115619239407 / 50000000000000 : ℝ))
      (E := (cell12869 ⟨14, by decide⟩).energy) (xi := (329586342917701 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12869 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12869]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12869])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12869) (a := (16717363178073 / 20000000000000 : ℝ)) (b := (160033978957 / 100000000000000 : ℝ)) (q := (1115619239407 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12869])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12869])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12869]

theorem cert12869_15 : CellCertificate 12869 (17640575318403 / 200000000000000 : ℝ) (1632165514854307 / 1000000000000000000 : ℝ) (329586342917701 / 10000000000000000 : ℝ)
    (cell12869 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · have h := gap_lower (n := 12869) (a := (83552239215873 / 100000000000000 : ℝ)) (b := (160033978957 / 100000000000000 : ℝ)) (q := (2231242534979 / 100000000000000 : ℝ))
      (E := (cell12869 ⟨15, by decide⟩).energy) (xi := (329586342917701 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12869 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12869]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12869])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12869) (a := (83552239215873 / 100000000000000 : ℝ)) (b := (160033978957 / 100000000000000 : ℝ)) (q := (2231242534979 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12869])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12869])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12869]

theorem cert12869_16 : CellCertificate 12869 (17640575318403 / 200000000000000 : ℝ) (1632165514854307 / 1000000000000000000 : ℝ) (329586342917701 / 10000000000000000 : ℝ)
    (cell12869 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · have h := gap_lower (n := 12869) (a := (83517686908249 / 100000000000000 : ℝ)) (b := (160033978957 / 100000000000000 : ℝ)) (q := (111562324553 / 5000000000000 : ℝ))
      (E := (cell12869 ⟨16, by decide⟩).energy) (xi := (329586342917701 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12869 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12869]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12869])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12869) (a := (83517686908249 / 100000000000000 : ℝ)) (b := (160033978957 / 100000000000000 : ℝ)) (q := (111562324553 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12869])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12869])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12869]

theorem cert12869_17 : CellCertificate 12869 (17640575318403 / 200000000000000 : ℝ) (1632165514854307 / 1000000000000000000 : ℝ) (329586342917701 / 10000000000000000 : ℝ)
    (cell12869 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · have h := gap_lower (n := 12869) (a := (3339326357349 / 4000000000000 : ℝ)) (b := (160033978957 / 100000000000000 : ℝ)) (q := (1115625263281 / 50000000000000 : ℝ))
      (E := (cell12869 ⟨17, by decide⟩).energy) (xi := (329586342917701 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12869 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12869]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12869])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12869) (a := (3339326357349 / 4000000000000 : ℝ)) (b := (160033978957 / 100000000000000 : ℝ)) (q := (1115625263281 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12869])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12869])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12869]

theorem cert12869_18 : CellCertificate 12869 (17640575318403 / 200000000000000 : ℝ) (1632165514854307 / 1000000000000000000 : ℝ) (329586342917701 / 10000000000000000 : ℝ)
    (cell12869 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · have h := gap_lower (n := 12869) (a := (83448655258707 / 100000000000000 : ℝ)) (b := (160033978957 / 100000000000000 : ℝ)) (q := (2231254529791 / 100000000000000 : ℝ))
      (E := (cell12869 ⟨18, by decide⟩).energy) (xi := (329586342917701 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12869 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12869]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12869])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12869) (a := (83448655258707 / 100000000000000 : ℝ)) (b := (160033978957 / 100000000000000 : ℝ)) (q := (2231254529791 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12869])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12869])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12869]

theorem cert12869_19 : CellCertificate 12869 (17640575318403 / 200000000000000 : ℝ) (1632165514854307 / 1000000000000000000 : ℝ) (329586342917701 / 10000000000000000 : ℝ)
    (cell12869 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · have h := gap_lower (n := 12869) (a := (41707087924887 / 50000000000000 : ℝ)) (b := (160033978957 / 100000000000000 : ℝ)) (q := (2231258505169 / 100000000000000 : ℝ))
      (E := (cell12869 ⟨19, by decide⟩).energy) (xi := (329586342917701 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12869 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12869]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12869])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12869) (a := (41707087924887 / 50000000000000 : ℝ)) (b := (160033978957 / 100000000000000 : ℝ)) (q := (2231258505169 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12869])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12869])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12869]

theorem cert12870_0 : CellCertificate 12870 (441000765509867 / 5000000000000000 : ℝ) (20400483179007 / 12500000000000000 : ℝ) (20597507896277 / 625000000000000 : ℝ)
    (cell12870 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · have h := gap_lower (n := 12870) (a := (42036726228543 / 50000000000000 : ℝ)) (b := (5000668649 / 3125000000000 : ℝ)) (q := (557766230903 / 25000000000000 : ℝ))
      (E := (cell12870 ⟨0, by decide⟩).energy) (xi := (20597507896277 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12870 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12870]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12870])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12870) (a := (42036726228543 / 50000000000000 : ℝ)) (b := (5000668649 / 3125000000000 : ℝ)) (q := (557766230903 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12870])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12870])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12870]

theorem cert12870_1 : CellCertificate 12870 (441000765509867 / 5000000000000000 : ℝ) (20400483179007 / 12500000000000000 : ℝ) (20597507896277 / 625000000000000 : ℝ)
    (cell12870 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · have h := gap_lower (n := 12870) (a := (21009632828463 / 25000000000000 : ℝ)) (b := (5000668649 / 3125000000000 : ℝ)) (q := (2231068924557 / 100000000000000 : ℝ))
      (E := (cell12870 ⟨1, by decide⟩).energy) (xi := (20597507896277 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12870 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12870]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12870])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12870) (a := (21009632828463 / 25000000000000 : ℝ)) (b := (5000668649 / 3125000000000 : ℝ)) (q := (2231068924557 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12870])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12870])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12870]

theorem cert12870_2 : CellCertificate 12870 (441000765509867 / 5000000000000000 : ℝ) (20400483179007 / 12500000000000000 : ℝ) (20597507896277 / 625000000000000 : ℝ)
    (cell12870 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · have h := gap_lower (n := 12870) (a := (84003635028777 / 100000000000000 : ℝ)) (b := (5000668649 / 3125000000000 : ℝ)) (q := (139442056527 / 6250000000000 : ℝ))
      (E := (cell12870 ⟨2, by decide⟩).energy) (xi := (20597507896277 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12870 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12870]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12870])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12870) (a := (84003635028777 / 100000000000000 : ℝ)) (b := (5000668649 / 3125000000000 : ℝ)) (q := (139442056527 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12870])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12870])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12870]

theorem cert12870_3 : CellCertificate 12870 (441000765509867 / 5000000000000000 : ℝ) (20400483179007 / 12500000000000000 : ℝ) (20597507896277 / 625000000000000 : ℝ)
    (cell12870 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · have h := gap_lower (n := 12870) (a := (3358750542621 / 4000000000000 : ℝ)) (b := (5000668649 / 3125000000000 : ℝ)) (q := (557769232419 / 25000000000000 : ℝ))
      (E := (cell12870 ⟨3, by decide⟩).energy) (xi := (20597507896277 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12870 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12870]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12870])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12870) (a := (3358750542621 / 4000000000000 : ℝ)) (b := (5000668649 / 3125000000000 : ℝ)) (q := (557769232419 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12870])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12870])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12870]

theorem cert12870_4 : CellCertificate 12870 (441000765509867 / 5000000000000000 : ℝ) (20400483179007 / 12500000000000000 : ℝ) (20597507896277 / 625000000000000 : ℝ)
    (cell12870 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · have h := gap_lower (n := 12870) (a := (20983479221989 / 25000000000000 : ℝ)) (b := (5000668649 / 3125000000000 : ℝ)) (q := (2231080950721 / 100000000000000 : ℝ))
      (E := (cell12870 ⟨4, by decide⟩).energy) (xi := (20597507896277 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12870 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12870]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12870])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12870) (a := (20983479221989 / 25000000000000 : ℝ)) (b := (5000668649 / 3125000000000 : ℝ)) (q := (2231080950721 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12870])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12870])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12870]

theorem cert12870_5 : CellCertificate 12870 (441000765509867 / 5000000000000000 : ℝ) (20400483179007 / 12500000000000000 : ℝ) (20597507896277 / 625000000000000 : ℝ)
    (cell12870 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · have h := gap_lower (n := 12870) (a := (20974773740029 / 25000000000000 : ℝ)) (b := (5000668649 / 3125000000000 : ℝ)) (q := (557771229413 / 25000000000000 : ℝ))
      (E := (cell12870 ⟨5, by decide⟩).energy) (xi := (20597507896277 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12870 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12870]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12870])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12870) (a := (20974773740029 / 25000000000000 : ℝ)) (b := (5000668649 / 3125000000000 : ℝ)) (q := (557771229413 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12870])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12870])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12870]

theorem cert12870_6 : CellCertificate 12870 (441000765509867 / 5000000000000000 : ℝ) (20400483179007 / 12500000000000000 : ℝ) (20597507896277 / 625000000000000 : ℝ)
    (cell12870 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · have h := gap_lower (n := 12870) (a := (83864297746241 / 100000000000000 : ℝ)) (b := (5000668649 / 3125000000000 : ℝ)) (q := (1115544477053 / 50000000000000 : ℝ))
      (E := (cell12870 ⟨6, by decide⟩).energy) (xi := (20597507896277 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12870 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12870]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12870])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12870) (a := (83864297746241 / 100000000000000 : ℝ)) (b := (5000668649 / 3125000000000 : ℝ)) (q := (1115544477053 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12870])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12870])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12870]

theorem cert12870_7 : CellCertificate 12870 (441000765509867 / 5000000000000000 : ℝ) (20400483179007 / 12500000000000000 : ℝ) (20597507896277 / 625000000000000 : ℝ)
    (cell12870 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · have h := gap_lower (n := 12870) (a := (20957381302689 / 25000000000000 : ℝ)) (b := (5000668649 / 3125000000000 : ℝ)) (q := (223109295169 / 10000000000000 : ℝ))
      (E := (cell12870 ⟨7, by decide⟩).energy) (xi := (20597507896277 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12870 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12870]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12870])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12870) (a := (20957381302689 / 25000000000000 : ℝ)) (b := (5000668649 / 3125000000000 : ℝ)) (q := (223109295169 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12870])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12870])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12870]

theorem cert12870_8 : CellCertificate 12870 (441000765509867 / 5000000000000000 : ℝ) (20400483179007 / 12500000000000000 : ℝ) (20597507896277 / 625000000000000 : ℝ)
    (cell12870 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · have h := gap_lower (n := 12870) (a := (83794777318269 / 100000000000000 : ℝ)) (b := (5000668649 / 3125000000000 : ℝ)) (q := (2231096917601 / 100000000000000 : ℝ))
      (E := (cell12870 ⟨8, by decide⟩).energy) (xi := (20597507896277 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12870 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12870]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12870])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12870) (a := (83794777318269 / 100000000000000 : ℝ)) (b := (5000668649 / 3125000000000 : ℝ)) (q := (2231096917601 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12870])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12870])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12870]

theorem cert12870_9 : CellCertificate 12870 (441000765509867 / 5000000000000000 : ℝ) (20400483179007 / 12500000000000000 : ℝ) (20597507896277 / 625000000000000 : ℝ)
    (cell12870 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · have h := gap_lower (n := 12870) (a := (10470006754197 / 12500000000000 : ℝ)) (b := (5000668649 / 3125000000000 : ℝ)) (q := (2231100916819 / 100000000000000 : ℝ))
      (E := (cell12870 ⟨9, by decide⟩).energy) (xi := (20597507896277 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12870 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12870]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12870])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12870) (a := (10470006754197 / 12500000000000 : ℝ)) (b := (5000668649 / 3125000000000 : ℝ)) (q := (2231100916819 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12870])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12870])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12870]

theorem cert12870_10 : CellCertificate 12870 (441000765509867 / 5000000000000000 : ℝ) (20400483179007 / 12500000000000000 : ℝ) (20597507896277 / 625000000000000 : ℝ)
    (cell12870 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · have h := gap_lower (n := 12870) (a := (10465669415207 / 12500000000000 : ℝ)) (b := (5000668649 / 3125000000000 : ℝ)) (q := (2231104956107 / 100000000000000 : ℝ))
      (E := (cell12870 ⟨10, by decide⟩).energy) (xi := (20597507896277 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12870 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12870]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12870])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12870) (a := (10465669415207 / 12500000000000 : ℝ)) (b := (5000668649 / 3125000000000 : ℝ)) (q := (2231104956107 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12870])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12870])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12870]

theorem cert12870_11 : CellCertificate 12870 (441000765509867 / 5000000000000000 : ℝ) (20400483179007 / 12500000000000000 : ℝ) (20597507896277 / 625000000000000 : ℝ)
    (cell12870 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · have h := gap_lower (n := 12870) (a := (83690681147669 / 100000000000000 : ℝ)) (b := (5000668649 / 3125000000000 : ℝ)) (q := (1115554462907 / 50000000000000 : ℝ))
      (E := (cell12870 ⟨11, by decide⟩).energy) (xi := (20597507896277 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12870 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12870]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12870])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12870) (a := (83690681147669 / 100000000000000 : ℝ)) (b := (5000668649 / 3125000000000 : ℝ)) (q := (1115554462907 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12870])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12870])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12870]

theorem cert12870_12 : CellCertificate 12870 (441000765509867 / 5000000000000000 : ℝ) (20400483179007 / 12500000000000000 : ℝ) (20597507896277 / 625000000000000 : ℝ)
    (cell12870 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · have h := gap_lower (n := 12870) (a := (83656031476959 / 100000000000000 : ℝ)) (b := (5000668649 / 3125000000000 : ℝ)) (q := (55777823707 / 2500000000000 : ℝ))
      (E := (cell12870 ⟨12, by decide⟩).energy) (xi := (20597507896277 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12870 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12870]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12870])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12870) (a := (83656031476959 / 100000000000000 : ℝ)) (b := (5000668649 / 3125000000000 : ℝ)) (q := (55777823707 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12870])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12870])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12870]

theorem cert12870_13 : CellCertificate 12870 (441000765509867 / 5000000000000000 : ℝ) (20400483179007 / 12500000000000000 : ℝ) (20597507896277 / 625000000000000 : ℝ)
    (cell12870 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · have h := gap_lower (n := 12870) (a := (10452675784381 / 12500000000000 : ℝ)) (b := (5000668649 / 3125000000000 : ℝ)) (q := (17430601339 / 781250000000 : ℝ))
      (E := (cell12870 ⟨13, by decide⟩).energy) (xi := (20597507896277 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12870 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12870]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12870])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12870) (a := (10452675784381 / 12500000000000 : ℝ)) (b := (5000668649 / 3125000000000 : ℝ)) (q := (17430601339 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12870])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12870])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12870]

theorem cert12870_14 : CellCertificate 12870 (441000765509867 / 5000000000000000 : ℝ) (20400483179007 / 12500000000000000 : ℝ) (20597507896277 / 625000000000000 : ℝ)
    (cell12870 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · have h := gap_lower (n := 12870) (a := (41793402753819 / 50000000000000 : ℝ)) (b := (5000668649 / 3125000000000 : ℝ)) (q := (2231120942701 / 100000000000000 : ℝ))
      (E := (cell12870 ⟨14, by decide⟩).energy) (xi := (20597507896277 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12870 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12870]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12870])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12870) (a := (41793402753819 / 50000000000000 : ℝ)) (b := (5000668649 / 3125000000000 : ℝ)) (q := (2231120942701 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12870])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12870])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12870]

theorem cert12870_15 : CellCertificate 12870 (441000765509867 / 5000000000000000 : ℝ) (20400483179007 / 12500000000000000 : ℝ) (20597507896277 / 625000000000000 : ℝ)
    (cell12870 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · have h := gap_lower (n := 12870) (a := (8355222914061 / 10000000000000 : ℝ)) (b := (5000668649 / 3125000000000 : ℝ)) (q := (2231124983949 / 100000000000000 : ℝ))
      (E := (cell12870 ⟨15, by decide⟩).energy) (xi := (20597507896277 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12870 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12870]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12870])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12870) (a := (8355222914061 / 10000000000000 : ℝ)) (b := (5000668649 / 3125000000000 : ℝ)) (q := (2231124983949 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12870])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12870])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12870]

theorem cert12870_16 : CellCertificate 12870 (441000765509867 / 5000000000000000 : ℝ) (20400483179007 / 12500000000000000 : ℝ) (20597507896277 / 625000000000000 : ℝ)
    (cell12870 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · have h := gap_lower (n := 12870) (a := (4175883857001 / 5000000000000 : ℝ)) (b := (5000668649 / 3125000000000 : ℝ)) (q := (111556449201 / 5000000000000 : ℝ))
      (E := (cell12870 ⟨16, by decide⟩).energy) (xi := (20597507896277 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12870 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12870]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12870])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12870) (a := (4175883857001 / 5000000000000 : ℝ)) (b := (5000668649 / 3125000000000 : ℝ)) (q := (111556449201 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12870])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12870])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12870]

theorem cert12870_17 : CellCertificate 12870 (441000765509867 / 5000000000000000 : ℝ) (20400483179007 / 12500000000000000 : ℝ) (20597507896277 / 625000000000000 : ℝ)
    (cell12870 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · have h := gap_lower (n := 12870) (a := (41741574736051 / 50000000000000 : ℝ)) (b := (5000668649 / 3125000000000 : ℝ)) (q := (2231132947813 / 100000000000000 : ℝ))
      (E := (cell12870 ⟨17, by decide⟩).energy) (xi := (20597507896277 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12870 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12870]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12870])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12870) (a := (41741574736051 / 50000000000000 : ℝ)) (b := (5000668649 / 3125000000000 : ℝ)) (q := (2231132947813 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12870])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12870])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12870]

theorem cert12870_18 : CellCertificate 12870 (441000765509867 / 5000000000000000 : ℝ) (20400483179007 / 12500000000000000 : ℝ) (20597507896277 / 625000000000000 : ℝ)
    (cell12870 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · have h := gap_lower (n := 12870) (a := (83448646103261 / 100000000000000 : ℝ)) (b := (5000668649 / 3125000000000 : ℝ)) (q := (1115568498243 / 50000000000000 : ℝ))
      (E := (cell12870 ⟨18, by decide⟩).energy) (xi := (20597507896277 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12870 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12870]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12870])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12870) (a := (83448646103261 / 100000000000000 : ℝ)) (b := (5000668649 / 3125000000000 : ℝ)) (q := (1115568498243 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12870])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12870])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12870]

theorem cert12870_19 : CellCertificate 12870 (441000765509867 / 5000000000000000 : ℝ) (20400483179007 / 12500000000000000 : ℝ) (20597507896277 / 625000000000000 : ℝ)
    (cell12870 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · have h := gap_lower (n := 12870) (a := (41707083500039 / 50000000000000 : ℝ)) (b := (5000668649 / 3125000000000 : ℝ)) (q := (446228191957 / 20000000000000 : ℝ))
      (E := (cell12870 ⟨19, by decide⟩).energy) (xi := (20597507896277 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12870 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12870]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12870])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12870) (a := (41707083500039 / 50000000000000 : ℝ)) (b := (5000668649 / 3125000000000 : ℝ)) (q := (446228191957 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12870])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12870])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12870]

theorem cert12871_0 : CellCertificate 12871 (27561696880543 / 312500000000000 : ℝ) (1631911813505821 / 1000000000000000000 : ℝ) (41191739247269 / 1250000000000000 : ℝ)
    (cell12871 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · have h := gap_lower (n := 12871) (a := (84073437726513 / 100000000000000 : ℝ)) (b := (160008816569 / 100000000000000 : ℝ)) (q := (223094737719 / 10000000000000 : ℝ))
      (E := (cell12871 ⟨0, by decide⟩).energy) (xi := (41191739247269 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12871 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12871]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12871])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12871) (a := (84073437726513 / 100000000000000 : ℝ)) (b := (160008816569 / 100000000000000 : ℝ)) (q := (223094737719 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12871])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12871])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12871]

theorem cert12871_1 : CellCertificate 12871 (27561696880543 / 312500000000000 : ℝ) (1631911813505821 / 1000000000000000000 : ℝ) (41191739247269 / 1250000000000000 : ℝ)
    (cell12871 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · have h := gap_lower (n := 12871) (a := (4201925844841 / 5000000000000 : ℝ)) (b := (160008816569 / 100000000000000 : ℝ)) (q := (2230951411027 / 100000000000000 : ℝ))
      (E := (cell12871 ⟨1, by decide⟩).energy) (xi := (41191739247269 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12871 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12871]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12871])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12871) (a := (4201925844841 / 5000000000000 : ℝ)) (b := (160008816569 / 100000000000000 : ℝ)) (q := (2230951411027 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12871])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12871])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12871]

theorem cert12871_2 : CellCertificate 12871 (27561696880543 / 312500000000000 : ℝ) (1631911813505821 / 1000000000000000000 : ℝ) (41191739247269 / 1250000000000000 : ℝ)
    (cell12871 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · have h := gap_lower (n := 12871) (a := (84003620924841 / 100000000000000 : ℝ)) (b := (160008816569 / 100000000000000 : ℝ)) (q := (2230955424559 / 100000000000000 : ℝ))
      (E := (cell12871 ⟨2, by decide⟩).energy) (xi := (41191739247269 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12871 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12871]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12871])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12871) (a := (84003620924841 / 100000000000000 : ℝ)) (b := (160008816569 / 100000000000000 : ℝ)) (q := (2230955424559 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12871])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12871])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12871]

theorem cert12871_3 : CellCertificate 12871 (27561696880543 / 312500000000000 : ℝ) (1631911813505821 / 1000000000000000000 : ℝ) (41191739247269 / 1250000000000000 : ℝ)
    (cell12871 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · have h := gap_lower (n := 12871) (a := (41984374887123 / 50000000000000 : ℝ)) (b := (160008816569 / 100000000000000 : ℝ)) (q := (89238377053 / 4000000000000 : ℝ))
      (E := (cell12871 ⟨3, by decide⟩).energy) (xi := (41191739247269 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12871 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12871]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12871])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12871) (a := (41984374887123 / 50000000000000 : ℝ)) (b := (160008816569 / 100000000000000 : ℝ)) (q := (89238377053 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12871])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12871])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12871]

theorem cert12871_4 : CellCertificate 12871 (27561696880543 / 312500000000000 : ℝ) (1631911813505821 / 1000000000000000000 : ℝ) (41191739247269 / 1250000000000000 : ℝ)
    (cell12871 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · have h := gap_lower (n := 12871) (a := (83933903408891 / 100000000000000 : ℝ)) (b := (160008816569 / 100000000000000 : ℝ)) (q := (2230963424609 / 100000000000000 : ℝ))
      (E := (cell12871 ⟨4, by decide⟩).energy) (xi := (41191739247269 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12871 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12871]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12871])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12871) (a := (83933903408891 / 100000000000000 : ℝ)) (b := (160008816569 / 100000000000000 : ℝ)) (q := (2230963424609 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12871])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12871])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12871]

theorem cert12871_5 : CellCertificate 12871 (27561696880543 / 312500000000000 : ℝ) (1631911813505821 / 1000000000000000000 : ℝ) (41191739247269 / 1250000000000000 : ℝ)
    (cell12871 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · have h := gap_lower (n := 12871) (a := (41949540896413 / 50000000000000 : ℝ)) (b := (160008816569 / 100000000000000 : ℝ)) (q := (2230967427437 / 100000000000000 : ℝ))
      (E := (cell12871 ⟨5, by decide⟩).energy) (xi := (41191739247269 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12871 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12871]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12871])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12871) (a := (41949540896413 / 50000000000000 : ℝ)) (b := (160008816569 / 100000000000000 : ℝ)) (q := (2230967427437 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12871])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12871])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12871]

theorem cert12871_6 : CellCertificate 12871 (27561696880543 / 312500000000000 : ℝ) (1631911813505821 / 1000000000000000000 : ℝ) (41191739247269 / 1250000000000000 : ℝ)
    (cell12871 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · have h := gap_lower (n := 12871) (a := (83864284890287 / 100000000000000 : ℝ)) (b := (160008816569 / 100000000000000 : ℝ)) (q := (446194276923 / 20000000000000 : ℝ))
      (E := (cell12871 ⟨6, by decide⟩).energy) (xi := (41191739247269 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12871 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12871]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12871])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12871) (a := (83864284890287 / 100000000000000 : ℝ)) (b := (160008816569 / 100000000000000 : ℝ)) (q := (446194276923 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12871])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12871])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12871]

theorem cert12871_7 : CellCertificate 12871 (27561696880543 / 312500000000000 : ℝ) (1631911813505821 / 1000000000000000000 : ℝ) (41191739247269 / 1250000000000000 : ℝ)
    (cell12871 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · have h := gap_lower (n := 12871) (a := (83829512665699 / 100000000000000 : ℝ)) (b := (160008816569 / 100000000000000 : ℝ)) (q := (223097541957 / 10000000000000 : ℝ))
      (E := (cell12871 ⟨7, by decide⟩).energy) (xi := (41191739247269 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12871 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12871]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12871])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12871) (a := (83829512665699 / 100000000000000 : ℝ)) (b := (160008816569 / 100000000000000 : ℝ)) (q := (223097541957 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12871])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12871])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12871]

theorem cert12871_8 : CellCertificate 12871 (27561696880543 / 312500000000000 : ℝ) (1631911813505821 / 1000000000000000000 : ℝ) (41191739247269 / 1250000000000000 : ℝ)
    (cell12871 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · have h := gap_lower (n := 12871) (a := (41897382541837 / 50000000000000 : ℝ)) (b := (160008816569 / 100000000000000 : ℝ)) (q := (2230979423609 / 100000000000000 : ℝ))
      (E := (cell12871 ⟨8, by decide⟩).energy) (xi := (41191739247269 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12871 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12871]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12871])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12871) (a := (41897382541837 / 50000000000000 : ℝ)) (b := (160008816569 / 100000000000000 : ℝ)) (q := (2230979423609 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12871])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12871])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12871]

theorem cert12871_9 : CellCertificate 12871 (27561696880543 / 312500000000000 : ℝ) (1631911813505821 / 1000000000000000000 : ℝ) (41191739247269 / 1250000000000000 : ℝ)
    (cell12871 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · have h := gap_lower (n := 12871) (a := (16752008421801 / 20000000000000 : ℝ)) (b := (160008816569 / 100000000000000 : ℝ)) (q := (1115491701839 / 50000000000000 : ℝ))
      (E := (cell12871 ⟨9, by decide⟩).energy) (xi := (41191739247269 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12871 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12871]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12871])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12871) (a := (16752008421801 / 20000000000000 : ℝ)) (b := (160008816569 / 100000000000000 : ℝ)) (q := (1115491701839 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12871])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12871])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12871]

theorem cert12871_10 : CellCertificate 12871 (27561696880543 / 312500000000000 : ℝ) (1631911813505821 / 1000000000000000000 : ℝ) (41191739247269 / 1250000000000000 : ℝ)
    (cell12871 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · have h := gap_lower (n := 12871) (a := (41862671853337 / 50000000000000 : ℝ)) (b := (160008816569 / 100000000000000 : ℝ)) (q := (2230987424527 / 100000000000000 : ℝ))
      (E := (cell12871 ⟨10, by decide⟩).energy) (xi := (41191739247269 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12871 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12871]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12871])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12871) (a := (41862671853337 / 50000000000000 : ℝ)) (b := (160008816569 / 100000000000000 : ℝ)) (q := (2230987424527 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12871])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12871])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12871]

theorem cert12871_11 : CellCertificate 12871 (27561696880543 / 312500000000000 : ℝ) (1631911813505821 / 1000000000000000000 : ℝ) (41191739247269 / 1250000000000000 : ℝ)
    (cell12871 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · have h := gap_lower (n := 12871) (a := (83690669841843 / 100000000000000 : ℝ)) (b := (160008816569 / 100000000000000 : ℝ)) (q := (2230991434587 / 100000000000000 : ℝ))
      (E := (cell12871 ⟨11, by decide⟩).energy) (xi := (41191739247269 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12871 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12871]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12871])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12871) (a := (83690669841843 / 100000000000000 : ℝ)) (b := (160008816569 / 100000000000000 : ℝ)) (q := (2230991434587 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12871])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12871])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12871]

theorem cert12871_12 : CellCertificate 12871 (27561696880543 / 312500000000000 : ℝ) (1631911813505821 / 1000000000000000000 : ℝ) (41191739247269 / 1250000000000000 : ℝ)
    (cell12871 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · have h := gap_lower (n := 12871) (a := (41828010239927 / 50000000000000 : ℝ)) (b := (160008816569 / 100000000000000 : ℝ)) (q := (1115497720027 / 50000000000000 : ℝ))
      (E := (cell12871 ⟨12, by decide⟩).energy) (xi := (41191739247269 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12871 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12871]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12871])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12871) (a := (41828010239927 / 50000000000000 : ℝ)) (b := (160008816569 / 100000000000000 : ℝ)) (q := (1115497720027 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12871])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12871])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12871]

theorem cert12871_13 : CellCertificate 12871 (27561696880543 / 312500000000000 : ℝ) (1631911813505821 / 1000000000000000000 : ℝ) (41191739247269 / 1250000000000000 : ℝ)
    (cell12871 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · have h := gap_lower (n := 12871) (a := (83621395586233 / 100000000000000 : ℝ)) (b := (160008816569 / 100000000000000 : ℝ)) (q := (713919823 / 32000000000 : ℝ))
      (E := (cell12871 ⟨13, by decide⟩).energy) (xi := (41191739247269 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12871 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12871]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12871])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12871) (a := (83621395586233 / 100000000000000 : ℝ)) (b := (160008816569 / 100000000000000 : ℝ)) (q := (713919823 / 32000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12871])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12871])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12871]

theorem cert12871_14 : CellCertificate 12871 (27561696880543 / 312500000000000 : ℝ) (1631911813505821 / 1000000000000000000 : ℝ) (41191739247269 / 1250000000000000 : ℝ)
    (cell12871 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · have h := gap_lower (n := 12871) (a := (83586795126681 / 100000000000000 : ℝ)) (b := (160008816569 / 100000000000000 : ℝ)) (q := (2231003460753 / 100000000000000 : ℝ))
      (E := (cell12871 ⟨14, by decide⟩).energy) (xi := (41191739247269 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12871 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12871]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12871])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12871) (a := (83586795126681 / 100000000000000 : ℝ)) (b := (160008816569 / 100000000000000 : ℝ)) (q := (2231003460753 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12871])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12871])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12871]

theorem cert12871_15 : CellCertificate 12871 (27561696880543 / 312500000000000 : ℝ) (1631911813505821 / 1000000000000000000 : ℝ) (41191739247269 / 1250000000000000 : ℝ)
    (cell12871 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · have h := gap_lower (n := 12871) (a := (83552219067081 / 100000000000000 : ℝ)) (b := (160008816569 / 100000000000000 : ℝ)) (q := (2231007428967 / 100000000000000 : ℝ))
      (E := (cell12871 ⟨15, by decide⟩).energy) (xi := (41191739247269 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12871 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12871]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12871])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12871) (a := (83552219067081 / 100000000000000 : ℝ)) (b := (160008816569 / 100000000000000 : ℝ)) (q := (2231007428967 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12871])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12871])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12871]

theorem cert12871_16 : CellCertificate 12871 (27561696880543 / 312500000000000 : ℝ) (1631911813505821 / 1000000000000000000 : ℝ) (41191739247269 / 1250000000000000 : ℝ)
    (cell12871 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · have h := gap_lower (n := 12871) (a := (5219854210843 / 6250000000000 : ℝ)) (b := (160008816569 / 100000000000000 : ℝ)) (q := (139438213429 / 6250000000000 : ℝ))
      (E := (cell12871 ⟨16, by decide⟩).energy) (xi := (41191739247269 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12871 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12871]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12871])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12871) (a := (5219854210843 / 6250000000000 : ℝ)) (b := (160008816569 / 100000000000000 : ℝ)) (q := (139438213429 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12871])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12871])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12871]

theorem cert12871_17 : CellCertificate 12871 (27561696880543 / 312500000000000 : ℝ) (1631911813505821 / 1000000000000000000 : ℝ) (41191739247269 / 1250000000000000 : ℝ)
    (cell12871 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · have h := gap_lower (n := 12871) (a := (41741570006069 / 50000000000000 : ℝ)) (b := (160008816569 / 100000000000000 : ℝ)) (q := (557753855853 / 25000000000000 : ℝ))
      (E := (cell12871 ⟨17, by decide⟩).energy) (xi := (41191739247269 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12871 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12871]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12871])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12871) (a := (41741570006069 / 50000000000000 : ℝ)) (b := (160008816569 / 100000000000000 : ℝ)) (q := (557753855853 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12871])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12871])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12871]

theorem cert12871_18 : CellCertificate 12871 (27561696880543 / 312500000000000 : ℝ) (1631911813505821 / 1000000000000000000 : ℝ) (41191739247269 / 1250000000000000 : ℝ)
    (cell12871 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · have h := gap_lower (n := 12871) (a := (41724318474719 / 50000000000000 : ℝ)) (b := (160008816569 / 100000000000000 : ℝ)) (q := (1115509729671 / 50000000000000 : ℝ))
      (E := (cell12871 ⟨18, by decide⟩).energy) (xi := (41191739247269 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12871 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12871]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12871])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12871) (a := (41724318474719 / 50000000000000 : ℝ)) (b := (160008816569 / 100000000000000 : ℝ)) (q := (1115509729671 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12871])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12871])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12871]

theorem cert12871_19 : CellCertificate 12871 (27561696880543 / 312500000000000 : ℝ) (1631911813505821 / 1000000000000000000 : ℝ) (41191739247269 / 1250000000000000 : ℝ)
    (cell12871 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · have h := gap_lower (n := 12871) (a := (83414158151969 / 100000000000000 : ℝ)) (b := (160008816569 / 100000000000000 : ℝ)) (q := (223102346887 / 10000000000000 : ℝ))
      (E := (cell12871 ⟨19, by decide⟩).energy) (xi := (41191739247269 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12871 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12871]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12871])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12871) (a := (83414158151969 / 100000000000000 : ℝ)) (b := (160008816569 / 100000000000000 : ℝ)) (q := (223102346887 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12871])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12871])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12871]

theorem cert12872_0 : CellCertificate 12872 (7055576587137 / 80000000000000 : ℝ) (815892496202747 / 500000000000000000 : ℝ) (32950770582977 / 1000000000000000 : ℝ)
    (cell12872 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · have h := gap_lower (n := 12872) (a := (10509177874779 / 12500000000000 : ℝ)) (b := (159996238359 / 100000000000000 : ℝ)) (q := (2230829884071 / 100000000000000 : ℝ))
      (E := (cell12872 ⟨0, by decide⟩).energy) (xi := (32950770582977 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12872 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12872]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12872])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12872) (a := (10509177874779 / 12500000000000 : ℝ)) (b := (159996238359 / 100000000000000 : ℝ)) (q := (2230829884071 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12872])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12872])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12872]

theorem cert12872_1 : CellCertificate 12872 (7055576587137 / 80000000000000 : ℝ) (815892496202747 / 500000000000000000 : ℝ) (32950770582977 / 1000000000000000 : ℝ)
    (cell12872 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · have h := gap_lower (n := 12872) (a := (84038502482041 / 100000000000000 : ℝ)) (b := (159996238359 / 100000000000000 : ℝ)) (q := (2230833893013 / 100000000000000 : ℝ))
      (E := (cell12872 ⟨1, by decide⟩).energy) (xi := (32950770582977 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12872 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12872]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12872])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12872) (a := (84038502482041 / 100000000000000 : ℝ)) (b := (159996238359 / 100000000000000 : ℝ)) (q := (2230833893013 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12872])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12872])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12872]

theorem cert12872_2 : CellCertificate 12872 (7055576587137 / 80000000000000 : ℝ) (815892496202747 / 500000000000000000 : ℝ) (32950770582977 / 1000000000000000 : ℝ)
    (cell12872 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · have h := gap_lower (n := 12872) (a := (84003606823123 / 100000000000000 : ℝ)) (b := (159996238359 / 100000000000000 : ℝ)) (q := (446167576473 / 20000000000000 : ℝ))
      (E := (cell12872 ⟨2, by decide⟩).energy) (xi := (32950770582977 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12872 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12872]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12872])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12872) (a := (84003606823123 / 100000000000000 : ℝ)) (b := (159996238359 / 100000000000000 : ℝ)) (q := (446167576473 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12872])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12872])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12872]

theorem cert12872_3 : CellCertificate 12872 (7055576587137 / 80000000000000 : ℝ) (815892496202747 / 500000000000000000 : ℝ) (32950770582977 / 1000000000000000 : ℝ)
    (cell12872 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · have h := gap_lower (n := 12872) (a := (16793747197029 / 20000000000000 : ℝ)) (b := (159996238359 / 100000000000000 : ℝ)) (q := (2230841918567 / 100000000000000 : ℝ))
      (E := (cell12872 ⟨3, by decide⟩).energy) (xi := (32950770582977 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12872 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12872]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12872])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12872) (a := (16793747197029 / 20000000000000 : ℝ)) (b := (159996238359 / 100000000000000 : ℝ)) (q := (2230841918567 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12872])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12872])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12872]

theorem cert12872_4 : CellCertificate 12872 (7055576587137 / 80000000000000 : ℝ) (815892496202747 / 500000000000000000 : ℝ) (32950770582977 / 1000000000000000 : ℝ)
    (cell12872 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · have h := gap_lower (n := 12872) (a := (1311467030187 / 1562500000000 : ℝ)) (b := (159996238359 / 100000000000000 : ℝ)) (q := (139427868383 / 6250000000000 : ℝ))
      (E := (cell12872 ⟨4, by decide⟩).energy) (xi := (32950770582977 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12872 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12872]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12872])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12872) (a := (1311467030187 / 1562500000000 : ℝ)) (b := (159996238359 / 100000000000000 : ℝ)) (q := (139427868383 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12872])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12872])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12872]

theorem cert12872_5 : CellCertificate 12872 (7055576587137 / 80000000000000 : ℝ) (815892496202747 / 500000000000000000 : ℝ) (32950770582977 / 1000000000000000 : ℝ)
    (cell12872 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · have h := gap_lower (n := 12872) (a := (2097476715691 / 2500000000000 : ℝ)) (b := (159996238359 / 100000000000000 : ℝ)) (q := (557712483223 / 25000000000000 : ℝ))
      (E := (cell12872 ⟨5, by decide⟩).energy) (xi := (32950770582977 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12872 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12872]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12872])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12872) (a := (2097476715691 / 2500000000000 : ℝ)) (b := (159996238359 / 100000000000000 : ℝ)) (q := (557712483223 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12872])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12872])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12872]

theorem cert12872_6 : CellCertificate 12872 (7055576587137 / 80000000000000 : ℝ) (815892496202747 / 500000000000000000 : ℝ) (32950770582977 / 1000000000000000 : ℝ)
    (cell12872 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · have h := gap_lower (n := 12872) (a := (209660680091 / 250000000000 : ℝ)) (b := (159996238359 / 100000000000000 : ℝ)) (q := (446170785353 / 20000000000000 : ℝ))
      (E := (cell12872 ⟨6, by decide⟩).energy) (xi := (32950770582977 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12872 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12872]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12872])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12872) (a := (209660680091 / 250000000000 : ℝ)) (b := (159996238359 / 100000000000000 : ℝ)) (q := (446170785353 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12872])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12872])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12872]

theorem cert12872_7 : CellCertificate 12872 (7055576587137 / 80000000000000 : ℝ) (815892496202747 / 500000000000000000 : ℝ) (32950770582977 / 1000000000000000 : ℝ)
    (cell12872 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · have h := gap_lower (n := 12872) (a := (5239343757667 / 6250000000000 : ℝ)) (b := (159996238359 / 100000000000000 : ℝ)) (q := (1115428970593 / 50000000000000 : ℝ))
      (E := (cell12872 ⟨7, by decide⟩).energy) (xi := (32950770582977 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12872 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12872]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12872])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12872) (a := (5239343757667 / 6250000000000 : ℝ)) (b := (159996238359 / 100000000000000 : ℝ)) (q := (1115428970593 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12872])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12872])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12872]

theorem cert12872_8 : CellCertificate 12872 (7055576587137 / 80000000000000 : ℝ) (815892496202747 / 500000000000000000 : ℝ) (32950770582977 / 1000000000000000 : ℝ)
    (cell12872 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · have h := gap_lower (n := 12872) (a := (8379475285107 / 10000000000000 : ℝ)) (b := (159996238359 / 100000000000000 : ℝ)) (q := (2230861925403 / 100000000000000 : ℝ))
      (E := (cell12872 ⟨8, by decide⟩).energy) (xi := (32950770582977 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12872 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12872]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12872])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12872) (a := (8379475285107 / 10000000000000 : ℝ)) (b := (159996238359 / 100000000000000 : ℝ)) (q := (2230861925403 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12872])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12872])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12872]

theorem cert12872_9 : CellCertificate 12872 (7055576587137 / 80000000000000 : ℝ) (815892496202747 / 500000000000000000 : ℝ) (32950770582977 / 1000000000000000 : ℝ)
    (cell12872 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · have h := gap_lower (n := 12872) (a := (8376003018639 / 10000000000000 : ℝ)) (b := (159996238359 / 100000000000000 : ℝ)) (q := (446173188879 / 20000000000000 : ℝ))
      (E := (cell12872 ⟨9, by decide⟩).energy) (xi := (32950770582977 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12872 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12872]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12872])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12872) (a := (8376003018639 / 10000000000000 : ℝ)) (b := (159996238359 / 100000000000000 : ℝ)) (q := (446173188879 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12872])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12872])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12872]

theorem cert12872_10 : CellCertificate 12872 (7055576587137 / 80000000000000 : ℝ) (815892496202747 / 500000000000000000 : ℝ) (32950770582977 / 1000000000000000 : ℝ)
    (cell12872 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · have h := gap_lower (n := 12872) (a := (83725332093611 / 100000000000000 : ℝ)) (b := (159996238359 / 100000000000000 : ℝ)) (q := (2230869946867 / 100000000000000 : ℝ))
      (E := (cell12872 ⟨10, by decide⟩).energy) (xi := (32950770582977 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12872 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12872]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12872])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12872) (a := (83725332093611 / 100000000000000 : ℝ)) (b := (159996238359 / 100000000000000 : ℝ)) (q := (2230869946867 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12872])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12872])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12872]

theorem cert12872_11 : CellCertificate 12872 (7055576587137 / 80000000000000 : ℝ) (815892496202747 / 500000000000000000 : ℝ) (32950770582977 / 1000000000000000 : ℝ)
    (cell12872 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · have h := gap_lower (n := 12872) (a := (41845329268949 / 50000000000000 : ℝ)) (b := (159996238359 / 100000000000000 : ℝ)) (q := (2230873939257 / 100000000000000 : ℝ))
      (E := (cell12872 ⟨11, by decide⟩).energy) (xi := (32950770582977 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12872 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12872]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12872])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12872) (a := (41845329268949 / 50000000000000 : ℝ)) (b := (159996238359 / 100000000000000 : ℝ)) (q := (2230873939257 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12872])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12872])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12872]

theorem cert12872_12 : CellCertificate 12872 (7055576587137 / 80000000000000 : ℝ) (815892496202747 / 500000000000000000 : ℝ) (32950770582977 / 1000000000000000 : ℝ)
    (cell12872 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · have h := gap_lower (n := 12872) (a := (41828004742297 / 50000000000000 : ℝ)) (b := (159996238359 / 100000000000000 : ℝ)) (q := (2230877927763 / 100000000000000 : ℝ))
      (E := (cell12872 ⟨12, by decide⟩).energy) (xi := (32950770582977 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12872 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12872]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12872])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12872) (a := (41828004742297 / 50000000000000 : ℝ)) (b := (159996238359 / 100000000000000 : ℝ)) (q := (2230877927763 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12872])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12872])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12872]

theorem cert12872_13 : CellCertificate 12872 (7055576587137 / 80000000000000 : ℝ) (815892496202747 / 500000000000000000 : ℝ) (32950770582977 / 1000000000000000 : ℝ)
    (cell12872 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · have h := gap_lower (n := 12872) (a := (3344855395969 / 4000000000000 : ℝ)) (b := (159996238359 / 100000000000000 : ℝ)) (q := (2230881918331 / 100000000000000 : ℝ))
      (E := (cell12872 ⟨13, by decide⟩).energy) (xi := (32950770582977 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12872 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12872]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12872])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12872) (a := (3344855395969 / 4000000000000 : ℝ)) (b := (159996238359 / 100000000000000 : ℝ)) (q := (2230881918331 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12872])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12872])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12872]

theorem cert12872_14 : CellCertificate 12872 (7055576587137 / 80000000000000 : ℝ) (815892496202747 / 500000000000000000 : ℝ) (32950770582977 / 1000000000000000 : ℝ)
    (cell12872 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · have h := gap_lower (n := 12872) (a := (41793392373747 / 50000000000000 : ℝ)) (b := (159996238359 / 100000000000000 : ℝ)) (q := (2230885916663 / 100000000000000 : ℝ))
      (E := (cell12872 ⟨14, by decide⟩).energy) (xi := (32950770582977 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12872 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12872]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12872])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12872) (a := (41793392373747 / 50000000000000 : ℝ)) (b := (159996238359 / 100000000000000 : ℝ)) (q := (2230885916663 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12872])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12872])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12872]

theorem cert12872_15 : CellCertificate 12872 (7055576587137 / 80000000000000 : ℝ) (815892496202747 / 500000000000000000 : ℝ) (32950770582977 / 1000000000000000 : ℝ)
    (cell12872 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · have h := gap_lower (n := 12872) (a := (20888052248821 / 25000000000000 : ℝ)) (b := (159996238359 / 100000000000000 : ℝ)) (q := (2230889928213 / 100000000000000 : ℝ))
      (E := (cell12872 ⟨15, by decide⟩).energy) (xi := (32950770582977 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12872 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12872]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12872])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12872) (a := (20888052248821 / 25000000000000 : ℝ)) (b := (159996238359 / 100000000000000 : ℝ)) (q := (2230889928213 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12872])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12872])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12872]

theorem cert12872_16 : CellCertificate 12872 (7055576587137 / 80000000000000 : ℝ) (815892496202747 / 500000000000000000 : ℝ) (32950770582977 / 1000000000000000 : ℝ)
    (cell12872 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · have h := gap_lower (n := 12872) (a := (20879414402163 / 25000000000000 : ℝ)) (b := (159996238359 / 100000000000000 : ℝ)) (q := (1115446979099 / 50000000000000 : ℝ))
      (E := (cell12872 ⟨16, by decide⟩).energy) (xi := (32950770582977 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12872 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12872]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12872])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12872) (a := (20879414402163 / 25000000000000 : ℝ)) (b := (159996238359 / 100000000000000 : ℝ)) (q := (1115446979099 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12872])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12872])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12872]

theorem cert12872_17 : CellCertificate 12872 (7055576587137 / 80000000000000 : ℝ) (815892496202747 / 500000000000000000 : ℝ) (32950770582977 / 1000000000000000 : ℝ)
    (cell12872 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · have h := gap_lower (n := 12872) (a := (41741565276917 / 50000000000000 : ℝ)) (b := (159996238359 / 100000000000000 : ℝ)) (q := (27886224417 / 1250000000000 : ℝ))
      (E := (cell12872 ⟨17, by decide⟩).energy) (xi := (32950770582977 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12872 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12872]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12872])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12872) (a := (41741565276917 / 50000000000000 : ℝ)) (b := (159996238359 / 100000000000000 : ℝ)) (q := (27886224417 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12872])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12872])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12872]

theorem cert12872_18 : CellCertificate 12872 (7055576587137 / 80000000000000 : ℝ) (815892496202747 / 500000000000000000 : ℝ) (32950770582977 / 1000000000000000 : ℝ)
    (cell12872 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · have h := gap_lower (n := 12872) (a := (41724313898619 / 50000000000000 : ℝ)) (b := (159996238359 / 100000000000000 : ℝ)) (q := (2230901976607 / 100000000000000 : ℝ))
      (E := (cell12872 ⟨18, by decide⟩).energy) (xi := (32950770582977 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12872 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12872]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12872])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12872) (a := (41724313898619 / 50000000000000 : ℝ)) (b := (159996238359 / 100000000000000 : ℝ)) (q := (2230901976607 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12872])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12872])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12872]

theorem cert12872_19 : CellCertificate 12872 (7055576587137 / 80000000000000 : ℝ) (815892496202747 / 500000000000000000 : ℝ) (32950770582977 / 1000000000000000 : ℝ)
    (cell12872 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · have h := gap_lower (n := 12872) (a := (41707074652723 / 50000000000000 : ℝ)) (b := (159996238359 / 100000000000000 : ℝ)) (q := (557726493539 / 25000000000000 : ℝ))
      (E := (cell12872 ⟨19, by decide⟩).energy) (xi := (32950770582977 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12872 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12872]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12872])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12872) (a := (41707074652723 / 50000000000000 : ℝ)) (b := (159996238359 / 100000000000000 : ℝ)) (q := (557726493539 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12872])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12872])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12872]

theorem cert12873_0 : CellCertificate 12873 (88191985066303 / 1000000000000000 : ℝ) (1631658191014981 / 1000000000000000000 : ℝ) (329481501894197 / 10000000000000000 : ℝ)
    (cell12873 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · have h := gap_lower (n := 12873) (a := (84073408272241 / 100000000000000 : ℝ)) (b := (159983662137 / 100000000000000 : ℝ)) (q := (2230712444259 / 100000000000000 : ℝ))
      (E := (cell12873 ⟨0, by decide⟩).energy) (xi := (329481501894197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12873 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12873]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12873])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12873) (a := (84073408272241 / 100000000000000 : ℝ)) (b := (159983662137 / 100000000000000 : ℝ)) (q := (2230712444259 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12873])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12873])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12873]

theorem cert12873_1 : CellCertificate 12873 (88191985066303 / 1000000000000000 : ℝ) (1631658191014981 / 1000000000000000000 : ℝ) (329481501894197 / 10000000000000000 : ℝ)
    (cell12873 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · have h := gap_lower (n := 12873) (a := (21009622017379 / 25000000000000 : ℝ)) (b := (159983662137 / 100000000000000 : ℝ)) (q := (1115358214183 / 50000000000000 : ℝ))
      (E := (cell12873 ⟨1, by decide⟩).energy) (xi := (329481501894197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12873 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12873]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12873])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12873) (a := (21009622017379 / 25000000000000 : ℝ)) (b := (159983662137 / 100000000000000 : ℝ)) (q := (1115358214183 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12873])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12873])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12873]

theorem cert12873_2 : CellCertificate 12873 (88191985066303 / 1000000000000000 : ℝ) (1631658191014981 / 1000000000000000000 : ℝ) (329481501894197 / 10000000000000000 : ℝ)
    (cell12873 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · have h := gap_lower (n := 12873) (a := (4200179636181 / 5000000000000 : ℝ)) (b := (159983662137 / 100000000000000 : ℝ)) (q := (557680112869 / 25000000000000 : ℝ))
      (E := (cell12873 ⟨2, by decide⟩).energy) (xi := (329481501894197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12873 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12873]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12873])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12873) (a := (4200179636181 / 5000000000000 : ℝ)) (b := (159983662137 / 100000000000000 : ℝ)) (q := (557680112869 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12873])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12873])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12873]

theorem cert12873_3 : CellCertificate 12873 (88191985066303 / 1000000000000000 : ℝ) (1631658191014981 / 1000000000000000000 : ℝ) (329481501894197 / 10000000000000000 : ℝ)
    (cell12873 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · have h := gap_lower (n := 12873) (a := (83968722198223 / 100000000000000 : ℝ)) (b := (159983662137 / 100000000000000 : ℝ)) (q := (2230724464301 / 100000000000000 : ℝ))
      (E := (cell12873 ⟨3, by decide⟩).energy) (xi := (329481501894197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12873 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12873]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12873])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12873) (a := (83968722198223 / 100000000000000 : ℝ)) (b := (159983662137 / 100000000000000 : ℝ)) (q := (2230724464301 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12873])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12873])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12873]

theorem cert12873_4 : CellCertificate 12873 (88191985066303 / 1000000000000000 : ℝ) (1631658191014981 / 1000000000000000000 : ℝ) (329481501894197 / 10000000000000000 : ℝ)
    (cell12873 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · have h := gap_lower (n := 12873) (a := (16786775291437 / 20000000000000 : ℝ)) (b := (159983662137 / 100000000000000 : ℝ)) (q := (2230728417201 / 100000000000000 : ℝ))
      (E := (cell12873 ⟨4, by decide⟩).energy) (xi := (329481501894197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12873 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12873]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12873])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12873) (a := (16786775291437 / 20000000000000 : ℝ)) (b := (159983662137 / 100000000000000 : ℝ)) (q := (2230728417201 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12873])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12873])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12873]

theorem cert12873_5 : CellCertificate 12873 (88191985066303 / 1000000000000000 : ℝ) (1631658191014981 / 1000000000000000000 : ℝ) (329481501894197 / 10000000000000000 : ℝ)
    (cell12873 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · have h := gap_lower (n := 12873) (a := (83899055464557 / 100000000000000 : ℝ)) (b := (159983662137 / 100000000000000 : ℝ)) (q := (1115366217009 / 50000000000000 : ℝ))
      (E := (cell12873 ⟨5, by decide⟩).energy) (xi := (329481501894197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12873 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12873]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12873])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12873) (a := (83899055464557 / 100000000000000 : ℝ)) (b := (159983662137 / 100000000000000 : ℝ)) (q := (1115366217009 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12873])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12873])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12873]

theorem cert12873_6 : CellCertificate 12873 (88191985066303 / 1000000000000000 : ℝ) (1631658191014981 / 1000000000000000000 : ℝ) (329481501894197 / 10000000000000000 : ℝ)
    (cell12873 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · have h := gap_lower (n := 12873) (a := (41932129592289 / 50000000000000 : ℝ)) (b := (159983662137 / 100000000000000 : ℝ)) (q := (1115368232313 / 50000000000000 : ℝ))
      (E := (cell12873 ⟨6, by decide⟩).energy) (xi := (329481501894197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12873 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12873]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12873])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12873) (a := (41932129592289 / 50000000000000 : ℝ)) (b := (159983662137 / 100000000000000 : ℝ)) (q := (1115368232313 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12873])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12873])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12873]

theorem cert12873_7 : CellCertificate 12873 (88191985066303 / 1000000000000000 : ℝ) (1631658191014981 / 1000000000000000000 : ℝ) (329481501894197 / 10000000000000000 : ℝ)
    (cell12873 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · have h := gap_lower (n := 12873) (a := (3353179503267 / 4000000000000 : ℝ)) (b := (159983662137 / 100000000000000 : ℝ)) (q := (2230740458549 / 100000000000000 : ℝ))
      (E := (cell12873 ⟨7, by decide⟩).energy) (xi := (329481501894197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12873 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12873]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12873])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12873) (a := (3353179503267 / 4000000000000 : ℝ)) (b := (159983662137 / 100000000000000 : ℝ)) (q := (2230740458549 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12873])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12873])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12873]

theorem cert12873_8 : CellCertificate 12873 (88191985066303 / 1000000000000000 : ℝ) (1631658191014981 / 1000000000000000000 : ℝ) (329481501894197 / 10000000000000000 : ℝ)
    (cell12873 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · have h := gap_lower (n := 12873) (a := (83794740620459 / 100000000000000 : ℝ)) (b := (159983662137 / 100000000000000 : ℝ)) (q := (446148896199 / 20000000000000 : ℝ))
      (E := (cell12873 ⟨8, by decide⟩).energy) (xi := (329481501894197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12873 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12873]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12873])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12873) (a := (83794740620459 / 100000000000000 : ℝ)) (b := (159983662137 / 100000000000000 : ℝ)) (q := (446148896199 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12873])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12873])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12873]

theorem cert12873_9 : CellCertificate 12873 (88191985066303 / 1000000000000000 : ℝ) (1631658191014981 / 1000000000000000000 : ℝ) (329481501894197 / 10000000000000000 : ℝ)
    (cell12873 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · have h := gap_lower (n := 12873) (a := (654375142701 / 781250000000 : ℝ)) (b := (159983662137 / 100000000000000 : ℝ)) (q := (1115374240469 / 50000000000000 : ℝ))
      (E := (cell12873 ⟨9, by decide⟩).energy) (xi := (329481501894197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12873 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12873]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12873])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12873) (a := (654375142701 / 781250000000 : ℝ)) (b := (159983662137 / 100000000000000 : ℝ)) (q := (1115374240469 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12873])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12873])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12873]

theorem cert12873_10 : CellCertificate 12873 (88191985066303 / 1000000000000000 : ℝ) (1631658191014981 / 1000000000000000000 : ℝ) (329481501894197 / 10000000000000000 : ℝ)
    (cell12873 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · have h := gap_lower (n := 12873) (a := (16745064096493 / 20000000000000 : ℝ)) (b := (159983662137 / 100000000000000 : ℝ)) (q := (557688116267 / 25000000000000 : ℝ))
      (E := (cell12873 ⟨10, by decide⟩).energy) (xi := (329481501894197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12873 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12873]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12873])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12873) (a := (16745064096493 / 20000000000000 : ℝ)) (b := (159983662137 / 100000000000000 : ℝ)) (q := (557688116267 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12873])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12873])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12873]

theorem cert12873_11 : CellCertificate 12873 (88191985066303 / 1000000000000000 : ℝ) (1631658191014981 / 1000000000000000000 : ℝ) (329481501894197 / 10000000000000000 : ℝ)
    (cell12873 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · have h := gap_lower (n := 12873) (a := (83690647235833 / 100000000000000 : ℝ)) (b := (159983662137 / 100000000000000 : ℝ)) (q := (2230756439827 / 100000000000000 : ℝ))
      (E := (cell12873 ⟨11, by decide⟩).energy) (xi := (329481501894197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12873 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12873]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12873])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12873) (a := (83690647235833 / 100000000000000 : ℝ)) (b := (159983662137 / 100000000000000 : ℝ)) (q := (2230756439827 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12873])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12873])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12873]

theorem cert12873_12 : CellCertificate 12873 (88191985066303 / 1000000000000000 : ℝ) (1631658191014981 / 1000000000000000000 : ℝ) (329481501894197 / 10000000000000000 : ℝ)
    (cell12873 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · have h := gap_lower (n := 12873) (a := (83655998491177 / 100000000000000 : ℝ)) (b := (159983662137 / 100000000000000 : ℝ)) (q := (1115380234759 / 50000000000000 : ℝ))
      (E := (cell12873 ⟨12, by decide⟩).energy) (xi := (329481501894197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12873 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12873]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12873])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12873) (a := (83655998491177 / 100000000000000 : ℝ)) (b := (159983662137 / 100000000000000 : ℝ)) (q := (1115380234759 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12873])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12873])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12873]

theorem cert12873_13 : CellCertificate 12873 (88191985066303 / 1000000000000000 : ℝ) (1631658191014981 / 1000000000000000000 : ℝ) (329481501894197 / 10000000000000000 : ℝ)
    (cell12873 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · have h := gap_lower (n := 12873) (a := (10452671776753 / 12500000000000 : ℝ)) (b := (159983662137 / 100000000000000 : ℝ)) (q := (2230764443893 / 100000000000000 : ℝ))
      (E := (cell12873 ⟨13, by decide⟩).energy) (xi := (329481501894197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12873 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12873]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12873])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12873) (a := (10452671776753 / 12500000000000 : ℝ)) (b := (159983662137 / 100000000000000 : ℝ)) (q := (2230764443893 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12873])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12873])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12873]

theorem cert12873_14 : CellCertificate 12873 (88191985066303 / 1000000000000000 : ℝ) (1631658191014981 / 1000000000000000000 : ℝ) (329481501894197 / 10000000000000000 : ℝ)
    (cell12873 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · have h := gap_lower (n := 12873) (a := (83586774370077 / 100000000000000 : ℝ)) (b := (159983662137 / 100000000000000 : ℝ)) (q := (2230768484893 / 100000000000000 : ℝ))
      (E := (cell12873 ⟨14, by decide⟩).energy) (xi := (329481501894197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12873 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12873]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12873])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12873) (a := (83586774370077 / 100000000000000 : ℝ)) (b := (159983662137 / 100000000000000 : ℝ)) (q := (2230768484893 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12873])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12873])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12873]

theorem cert12873_15 : CellCertificate 12873 (88191985066303 / 1000000000000000 : ℝ) (1631658191014981 / 1000000000000000000 : ℝ) (329481501894197 / 10000000000000000 : ℝ)
    (cell12873 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · have h := gap_lower (n := 12873) (a := (4177609946261 / 5000000000000 : ℝ)) (b := (159983662137 / 100000000000000 : ℝ)) (q := (278846560211 / 12500000000000 : ℝ))
      (E := (cell12873 ⟨15, by decide⟩).energy) (xi := (329481501894197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12873 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12873]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12873])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12873) (a := (4177609946261 / 5000000000000 : ℝ)) (b := (159983662137 / 100000000000000 : ℝ)) (q := (278846560211 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12873])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12873])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12873]

theorem cert12873_16 : CellCertificate 12873 (88191985066303 / 1000000000000000 : ℝ) (1631658191014981 / 1000000000000000000 : ℝ) (329481501894197 / 10000000000000000 : ℝ)
    (cell12873 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · have h := gap_lower (n := 12873) (a := (83517647845513 / 100000000000000 : ℝ)) (b := (159983662137 / 100000000000000 : ℝ)) (q := (111538824881 / 5000000000000 : ℝ))
      (E := (cell12873 ⟨16, by decide⟩).energy) (xi := (329481501894197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12873 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12873]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12873])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12873) (a := (83517647845513 / 100000000000000 : ℝ)) (b := (159983662137 / 100000000000000 : ℝ)) (q := (111538824881 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12873])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12873])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12873]

theorem cert12873_17 : CellCertificate 12873 (88191985066303 / 1000000000000000 : ℝ) (1631658191014981 / 1000000000000000000 : ℝ) (329481501894197 / 10000000000000000 : ℝ)
    (cell12873 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · have h := gap_lower (n := 12873) (a := (83483121097189 / 100000000000000 : ℝ)) (b := (159983662137 / 100000000000000 : ℝ)) (q := (446156095887 / 20000000000000 : ℝ))
      (E := (cell12873 ⟨17, by decide⟩).energy) (xi := (329481501894197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12873 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12873]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12873])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12873) (a := (83483121097189 / 100000000000000 : ℝ)) (b := (159983662137 / 100000000000000 : ℝ)) (q := (446156095887 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12873])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12873])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12873]

theorem cert12873_18 : CellCertificate 12873 (88191985066303 / 1000000000000000 : ℝ) (1631658191014981 / 1000000000000000000 : ℝ) (329481501894197 / 10000000000000000 : ℝ)
    (cell12873 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · have h := gap_lower (n := 12873) (a := (4172430932333 / 5000000000000 : ℝ)) (b := (159983662137 / 100000000000000 : ℝ)) (q := (2230784490037 / 100000000000000 : ℝ))
      (E := (cell12873 ⟨18, by decide⟩).energy) (xi := (329481501894197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12873 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12873]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12873])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12873) (a := (4172430932333 / 5000000000000 : ℝ)) (b := (159983662137 / 100000000000000 : ℝ)) (q := (2230784490037 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12873])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12873])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12873]

theorem cert12873_19 : CellCertificate 12873 (88191985066303 / 1000000000000000 : ℝ) (1631658191014981 / 1000000000000000000 : ℝ) (329481501894197 / 10000000000000000 : ℝ)
    (cell12873 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · have h := gap_lower (n := 12873) (a := (83414140460509 / 100000000000000 : ℝ)) (b := (159983662137 / 100000000000000 : ℝ)) (q := (1115394237821 / 50000000000000 : ℝ))
      (E := (cell12873 ⟨19, by decide⟩).energy) (xi := (329481501894197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12873 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12873]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12873])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12873) (a := (83414140460509 / 100000000000000 : ℝ)) (b := (159983662137 / 100000000000000 : ℝ)) (q := (1115394237821 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12873])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12873])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12873]

theorem cert12874_0 : CellCertificate 12874 (881892631989141 / 10000000000000000 : ℝ) (163153140932969 / 100000000000000000 : ℝ) (41181912771293 / 1250000000000000 : ℝ)
    (cell12874 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · have h := gap_lower (n := 12874) (a := (42036696774271 / 50000000000000 : ℝ)) (b := (159971087903 / 100000000000000 : ℝ)) (q := (1115297499963 / 50000000000000 : ℝ))
      (E := (cell12874 ⟨0, by decide⟩).energy) (xi := (41181912771293 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12874 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12874]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12874])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12874) (a := (42036696774271 / 50000000000000 : ℝ)) (b := (159971087903 / 100000000000000 : ℝ)) (q := (1115297499963 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12874])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12874])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12874]

theorem cert12874_1 : CellCertificate 12874 (881892631989141 / 10000000000000000 : ℝ) (163153140932969 / 100000000000000000 : ℝ) (41181912771293 / 1250000000000000 : ℝ)
    (cell12874 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · have h := gap_lower (n := 12874) (a := (21009618414811 / 25000000000000 : ℝ)) (b := (159971087903 / 100000000000000 : ℝ)) (q := (2230599017087 / 100000000000000 : ℝ))
      (E := (cell12874 ⟨1, by decide⟩).energy) (xi := (41181912771293 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12874 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12874]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12874])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12874) (a := (21009618414811 / 25000000000000 : ℝ)) (b := (159971087903 / 100000000000000 : ℝ)) (q := (2230599017087 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12874])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12874])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12874]

theorem cert12874_2 : CellCertificate 12874 (881892631989141 / 10000000000000000 : ℝ) (163153140932969 / 100000000000000000 : ℝ) (41181912771293 / 1250000000000000 : ℝ)
    (cell12874 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · have h := gap_lower (n := 12874) (a := (21000894656583 / 25000000000000 : ℝ)) (b := (159971087903 / 100000000000000 : ℝ)) (q := (2230603016143 / 100000000000000 : ℝ))
      (E := (cell12874 ⟨2, by decide⟩).energy) (xi := (41181912771293 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12874 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12874]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12874])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12874) (a := (21000894656583 / 25000000000000 : ℝ)) (b := (159971087903 / 100000000000000 : ℝ)) (q := (2230603016143 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12874])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12874])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12874]

theorem cert12874_3 : CellCertificate 12874 (881892631989141 / 10000000000000000 : ℝ) (163153140932969 / 100000000000000000 : ℝ) (41181912771293 / 1250000000000000 : ℝ)
    (cell12874 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · have h := gap_lower (n := 12874) (a := (83968708413479 / 100000000000000 : ℝ)) (b := (159971087903 / 100000000000000 : ℝ)) (q := (557651751407 / 25000000000000 : ℝ))
      (E := (cell12874 ⟨3, by decide⟩).energy) (xi := (41181912771293 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12874 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12874]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12874])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12874) (a := (83968708413479 / 100000000000000 : ℝ)) (b := (159971087903 / 100000000000000 : ℝ)) (q := (557651751407 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12874])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12874])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12874]

theorem cert12874_4 : CellCertificate 12874 (881892631989141 / 10000000000000000 : ℝ) (163153140932969 / 100000000000000000 : ℝ) (41181912771293 / 1250000000000000 : ℝ)
    (cell12874 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · have h := gap_lower (n := 12874) (a := (83933862984543 / 100000000000000 : ℝ)) (b := (159971087903 / 100000000000000 : ℝ)) (q := (2230610993827 / 100000000000000 : ℝ))
      (E := (cell12874 ⟨4, by decide⟩).energy) (xi := (41181912771293 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12874 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12874]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12874])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12874) (a := (83933862984543 / 100000000000000 : ℝ)) (b := (159971087903 / 100000000000000 : ℝ)) (q := (2230610993827 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12874])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12874])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12874]

theorem cert12874_5 : CellCertificate 12874 (881892631989141 / 10000000000000000 : ℝ) (163153140932969 / 100000000000000000 : ℝ) (41181912771293 / 1250000000000000 : ℝ)
    (cell12874 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · have h := gap_lower (n := 12874) (a := (41949521151789 / 50000000000000 : ℝ)) (b := (159971087903 / 100000000000000 : ℝ)) (q := (2230614988759 / 100000000000000 : ℝ))
      (E := (cell12874 ⟨5, by decide⟩).energy) (xi := (41181912771293 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12874 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12874]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12874])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12874) (a := (41949521151789 / 50000000000000 : ℝ)) (b := (159971087903 / 100000000000000 : ℝ)) (q := (2230614988759 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12874])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12874])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12874]

theorem cert12874_6 : CellCertificate 12874 (881892631989141 / 10000000000000000 : ℝ) (163153140932969 / 100000000000000000 : ℝ) (41181912771293 / 1250000000000000 : ℝ)
    (cell12874 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · have h := gap_lower (n := 12874) (a := (83864246334823 / 100000000000000 : ℝ)) (b := (159971087903 / 100000000000000 : ℝ)) (q := (446123799639 / 20000000000000 : ℝ))
      (E := (cell12874 ⟨6, by decide⟩).energy) (xi := (41181912771293 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12874 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12874]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12874])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12874) (a := (83864246334823 / 100000000000000 : ℝ)) (b := (159971087903 / 100000000000000 : ℝ)) (q := (446123799639 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12874])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12874])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12874]

theorem cert12874_7 : CellCertificate 12874 (881892631989141 / 10000000000000000 : ℝ) (163153140932969 / 100000000000000000 : ℝ) (41181912771293 / 1250000000000000 : ℝ)
    (cell12874 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · have h := gap_lower (n := 12874) (a := (16765895008541 / 20000000000000 : ℝ)) (b := (159971087903 / 100000000000000 : ℝ)) (q := (2230623029651 / 100000000000000 : ℝ))
      (E := (cell12874 ⟨7, by decide⟩).energy) (xi := (41181912771293 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12874 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12874]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12874])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12874) (a := (16765895008541 / 20000000000000 : ℝ)) (b := (159971087903 / 100000000000000 : ℝ)) (q := (2230623029651 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12874])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12874])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12874]

theorem cert12874_8 : CellCertificate 12874 (881892631989141 / 10000000000000000 : ℝ) (163153140932969 / 100000000000000000 : ℝ) (41181912771293 / 1250000000000000 : ℝ)
    (cell12874 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · have h := gap_lower (n := 12874) (a := (83794728391839 / 100000000000000 : ℝ)) (b := (159971087903 / 100000000000000 : ℝ)) (q := (2230627032373 / 100000000000000 : ℝ))
      (E := (cell12874 ⟨8, by decide⟩).energy) (xi := (41181912771293 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12874 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12874]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12874])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12874) (a := (83794728391839 / 100000000000000 : ℝ)) (b := (159971087903 / 100000000000000 : ℝ)) (q := (2230627032373 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12874])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12874])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12874]

theorem cert12874_9 : CellCertificate 12874 (881892631989141 / 10000000000000000 : ℝ) (163153140932969 / 100000000000000000 : ℝ) (41181912771293 / 1250000000000000 : ℝ)
    (cell12874 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · have h := gap_lower (n := 12874) (a := (83760006347021 / 100000000000000 : ℝ)) (b := (159971087903 / 100000000000000 : ℝ)) (q := (278828876663 / 12500000000000 : ℝ))
      (E := (cell12874 ⟨9, by decide⟩).energy) (xi := (41181912771293 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12874 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12874]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12874])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12874) (a := (83760006347021 / 100000000000000 : ℝ)) (b := (159971087903 / 100000000000000 : ℝ)) (q := (278828876663 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12874])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12874])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12874]

theorem cert12874_10 : CellCertificate 12874 (881892631989141 / 10000000000000000 : ℝ) (163153140932969 / 100000000000000000 : ℝ) (41181912771293 / 1250000000000000 : ℝ)
    (cell12874 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · have h := gap_lower (n := 12874) (a := (20931327218309 / 25000000000000 : ℝ)) (b := (159971087903 / 100000000000000 : ℝ)) (q := (2230635037193 / 100000000000000 : ℝ))
      (E := (cell12874 ⟨10, by decide⟩).energy) (xi := (41181912771293 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12874 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12874]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12874])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12874) (a := (20931327218309 / 25000000000000 : ℝ)) (b := (159971087903 / 100000000000000 : ℝ)) (q := (2230635037193 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12874])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12874])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12874]

theorem cert12874_11 : CellCertificate 12874 (881892631989141 / 10000000000000000 : ℝ) (163153140932969 / 100000000000000000 : ℝ) (41181912771293 / 1250000000000000 : ℝ)
    (cell12874 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · have h := gap_lower (n := 12874) (a := (2615332372989 / 3125000000000 : ℝ)) (b := (159971087903 / 100000000000000 : ℝ)) (q := (2230639052467 / 100000000000000 : ℝ))
      (E := (cell12874 ⟨11, by decide⟩).energy) (xi := (41181912771293 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12874 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12874]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12874])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12874) (a := (2615332372989 / 3125000000000 : ℝ)) (b := (159971087903 / 100000000000000 : ℝ)) (q := (2230639052467 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12874])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12874])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12874]

theorem cert12874_12 : CellCertificate 12874 (881892631989141 / 10000000000000000 : ℝ) (163153140932969 / 100000000000000000 : ℝ) (41181912771293 / 1250000000000000 : ℝ)
    (cell12874 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · have h := gap_lower (n := 12874) (a := (83655987499603 / 100000000000000 : ℝ)) (b := (159971087903 / 100000000000000 : ℝ)) (q := (2230643007211 / 100000000000000 : ℝ))
      (E := (cell12874 ⟨12, by decide⟩).energy) (xi := (41181912771293 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12874 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12874]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12874])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12874) (a := (83655987499603 / 100000000000000 : ℝ)) (b := (159971087903 / 100000000000000 : ℝ)) (q := (2230643007211 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12874])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12874])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12874]

theorem cert12874_13 : CellCertificate 12874 (881892631989141 / 10000000000000000 : ℝ) (163153140932969 / 100000000000000000 : ℝ) (41181912771293 / 1250000000000000 : ℝ)
    (cell12874 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · have h := gap_lower (n := 12874) (a := (20905340882657 / 25000000000000 : ℝ)) (b := (159971087903 / 100000000000000 : ℝ)) (q := (2230647023563 / 100000000000000 : ℝ))
      (E := (cell12874 ⟨13, by decide⟩).energy) (xi := (41181912771293 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12874 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12874]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12874])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12874) (a := (20905340882657 / 25000000000000 : ℝ)) (b := (159971087903 / 100000000000000 : ℝ)) (q := (2230647023563 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12874])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12874])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12874]

theorem cert12874_14 : CellCertificate 12874 (881892631989141 / 10000000000000000 : ℝ) (163153140932969 / 100000000000000000 : ℝ) (41181912771293 / 1250000000000000 : ℝ)
    (cell12874 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · have h := gap_lower (n := 12874) (a := (83586763994429 / 100000000000000 : ℝ)) (b := (159971087903 / 100000000000000 : ℝ)) (q := (1115325524569 / 50000000000000 : ℝ))
      (E := (cell12874 ⟨14, by decide⟩).energy) (xi := (41181912771293 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12874 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12874]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12874])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12874) (a := (83586763994429 / 100000000000000 : ℝ)) (b := (159971087903 / 100000000000000 : ℝ)) (q := (1115325524569 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12874])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12874])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12874]

theorem cert12874_15 : CellCertificate 12874 (881892631989141 / 10000000000000000 : ℝ) (163153140932969 / 100000000000000000 : ℝ) (41181912771293 / 1250000000000000 : ℝ)
    (cell12874 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · have h := gap_lower (n := 12874) (a := (83552188856889 / 100000000000000 : ℝ)) (b := (159971087903 / 100000000000000 : ℝ)) (q := (2230655031213 / 100000000000000 : ℝ))
      (E := (cell12874 ⟨15, by decide⟩).energy) (xi := (41181912771293 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12874 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12874]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12874])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12874) (a := (83552188856889 / 100000000000000 : ℝ)) (b := (159971087903 / 100000000000000 : ℝ)) (q := (2230655031213 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12874])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12874])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12874]

theorem cert12874_16 : CellCertificate 12874 (881892631989141 / 10000000000000000 : ℝ) (163153140932969 / 100000000000000000 : ℝ) (41181912771293 / 1250000000000000 : ℝ)
    (cell12874 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · have h := gap_lower (n := 12874) (a := (20879409521017 / 25000000000000 : ℝ)) (b := (159971087903 / 100000000000000 : ℝ)) (q := (557664758283 / 25000000000000 : ℝ))
      (E := (cell12874 ⟨16, by decide⟩).energy) (xi := (41181912771293 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12874 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12874]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12874])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12874) (a := (20879409521017 / 25000000000000 : ℝ)) (b := (159971087903 / 100000000000000 : ℝ)) (q := (557664758283 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12874])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12874])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12874]

theorem cert12874_17 : CellCertificate 12874 (881892631989141 / 10000000000000000 : ℝ) (163153140932969 / 100000000000000000 : ℝ) (41181912771293 / 1250000000000000 : ℝ)
    (cell12874 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · have h := gap_lower (n := 12874) (a := (83483111642203 / 100000000000000 : ℝ)) (b := (159971087903 / 100000000000000 : ℝ)) (q := (2230663059861 / 100000000000000 : ℝ))
      (E := (cell12874 ⟨17, by decide⟩).energy) (xi := (41181912771293 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12874 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12874]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12874])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12874) (a := (83483111642203 / 100000000000000 : ℝ)) (b := (159971087903 / 100000000000000 : ℝ)) (q := (2230663059861 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12874])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12874])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12874]

theorem cert12874_18 : CellCertificate 12874 (881892631989141 / 10000000000000000 : ℝ) (163153140932969 / 100000000000000000 : ℝ) (41181912771293 / 1250000000000000 : ℝ)
    (cell12874 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · have h := gap_lower (n := 12874) (a := (16689721899541 / 20000000000000 : ℝ)) (b := (159971087903 / 100000000000000 : ℝ)) (q := (2230667057879 / 100000000000000 : ℝ))
      (E := (cell12874 ⟨18, by decide⟩).energy) (xi := (41181912771293 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12874 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12874]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12874])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12874) (a := (16689721899541 / 20000000000000 : ℝ)) (b := (159971087903 / 100000000000000 : ℝ)) (q := (2230667057879 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12874])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12874])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12874]

theorem cert12874_19 : CellCertificate 12874 (881892631989141 / 10000000000000000 : ℝ) (163153140932969 / 100000000000000000 : ℝ) (41181912771293 / 1250000000000000 : ℝ)
    (cell12874 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · have h := gap_lower (n := 12874) (a := (83414131617157 / 100000000000000 : ℝ)) (b := (159971087903 / 100000000000000 : ℝ)) (q := (2230671031603 / 100000000000000 : ℝ))
      (E := (cell12874 ⟨19, by decide⟩).energy) (xi := (41181912771293 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12874 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12874]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12874])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12874) (a := (83414131617157 / 100000000000000 : ℝ)) (b := (159971087903 / 100000000000000 : ℝ)) (q := (2230671031603 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12874])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12874])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12874]

end BstLean.Part268
