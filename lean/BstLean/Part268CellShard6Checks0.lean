import BstLean.Part268CellShard6Data

/-! Twenty scalar cells per dimension in a 25-dimension shard. -/
namespace BstLean.Part268
open Real BstLean.Part263

theorem cert12500_0 : CellCertificate 12500 (2788636686689 / 31250000000000 : ℝ) (1680363136043441 / 1000000000000000000 : ℝ) (339557587310217 / 10000000000000000 : ℝ)
    (cell12500 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · have h := gap_lower (n := 12500) (a := (84079064747421 / 100000000000000 : ℝ)) (b := (164816889259 / 100000000000000 : ℝ)) (q := (2276787547047 / 100000000000000 : ℝ))
      (E := (cell12500 ⟨0, by decide⟩).energy) (xi := (339557587310217 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12500 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12500]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12500])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12500) (a := (84079064747421 / 100000000000000 : ℝ)) (b := (164816889259 / 100000000000000 : ℝ)) (q := (2276787547047 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12500])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12500])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12500]

theorem cert12500_1 : CellCertificate 12500 (2788636686689 / 31250000000000 : ℝ) (1680363136043441 / 1000000000000000000 : ℝ) (339557587310217 / 10000000000000000 : ℝ)
    (cell12500 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · have h := gap_lower (n := 12500) (a := (42022012472923 / 50000000000000 : ℝ)) (b := (164816889259 / 100000000000000 : ℝ)) (q := (2276791572993 / 100000000000000 : ℝ))
      (E := (cell12500 ⟨1, by decide⟩).energy) (xi := (339557587310217 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12500 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12500]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12500])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12500) (a := (42022012472923 / 50000000000000 : ℝ)) (b := (164816889259 / 100000000000000 : ℝ)) (q := (2276791572993 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12500])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12500])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12500]

theorem cert12500_2 : CellCertificate 12500 (2788636686689 / 31250000000000 : ℝ) (1680363136043441 / 1000000000000000000 : ℝ) (339557587310217 / 10000000000000000 : ℝ)
    (cell12500 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · have h := gap_lower (n := 12500) (a := (16801802034057 / 20000000000000 : ℝ)) (b := (164816889259 / 100000000000000 : ℝ)) (q := (2276795529307 / 100000000000000 : ℝ))
      (E := (cell12500 ⟨2, by decide⟩).energy) (xi := (339557587310217 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12500 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12500]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12500])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12500) (a := (16801802034057 / 20000000000000 : ℝ)) (b := (164816889259 / 100000000000000 : ℝ)) (q := (2276795529307 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12500])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12500])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12500]

theorem cert12500_3 : CellCertificate 12500 (2788636686689 / 31250000000000 : ℝ) (1680363136043441 / 1000000000000000000 : ℝ) (339557587310217 / 10000000000000000 : ℝ)
    (cell12500 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · have h := gap_lower (n := 12500) (a := (83974020384033 / 100000000000000 : ℝ)) (b := (164816889259 / 100000000000000 : ℝ)) (q := (1138399770443 / 50000000000000 : ℝ))
      (E := (cell12500 ⟨3, by decide⟩).energy) (xi := (339557587310217 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12500 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12500]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12500])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12500) (a := (83974020384033 / 100000000000000 : ℝ)) (b := (164816889259 / 100000000000000 : ℝ)) (q := (1138399770443 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12500])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12500])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12500]

theorem cert12500_4 : CellCertificate 12500 (2788636686689 / 31250000000000 : ℝ) (1680363136043441 / 1000000000000000000 : ℝ) (339557587310217 / 10000000000000000 : ℝ)
    (cell12500 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · have h := gap_lower (n := 12500) (a := (83939055550579 / 100000000000000 : ℝ)) (b := (164816889259 / 100000000000000 : ℝ)) (q := (1138401779453 / 50000000000000 : ℝ))
      (E := (cell12500 ⟨4, by decide⟩).energy) (xi := (339557587310217 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12500 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12500]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12500])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12500) (a := (83939055550579 / 100000000000000 : ℝ)) (b := (164816889259 / 100000000000000 : ℝ)) (q := (1138401779453 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12500])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12500])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12500]

theorem cert12500_5 : CellCertificate 12500 (2788636686689 / 31250000000000 : ℝ) (1680363136043441 / 1000000000000000000 : ℝ) (339557587310217 / 10000000000000000 : ℝ)
    (cell12500 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · have h := gap_lower (n := 12500) (a := (16780823126721 / 20000000000000 : ℝ)) (b := (164816889259 / 100000000000000 : ℝ)) (q := (569201883547 / 25000000000000 : ℝ))
      (E := (cell12500 ⟨5, by decide⟩).energy) (xi := (339557587310217 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12500 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12500]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12500])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12500) (a := (16780823126721 / 20000000000000 : ℝ)) (b := (164816889259 / 100000000000000 : ℝ)) (q := (569201883547 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12500])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12500])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12500]

theorem cert12500_6 : CellCertificate 12500 (2788636686689 / 31250000000000 : ℝ) (1680363136043441 / 1000000000000000000 : ℝ) (339557587310217 / 10000000000000000 : ℝ)
    (cell12500 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · have h := gap_lower (n := 12500) (a := (83869200596983 / 100000000000000 : ℝ)) (b := (164816889259 / 100000000000000 : ℝ)) (q := (284601441633 / 12500000000000 : ℝ))
      (E := (cell12500 ⟨6, by decide⟩).energy) (xi := (339557587310217 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12500 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12500]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12500])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12500) (a := (83869200596983 / 100000000000000 : ℝ)) (b := (164816889259 / 100000000000000 : ℝ)) (q := (284601441633 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12500])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12500])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12500]

theorem cert12500_7 : CellCertificate 12500 (2788636686689 / 31250000000000 : ℝ) (1680363136043441 / 1000000000000000000 : ℝ) (339557587310217 / 10000000000000000 : ℝ)
    (cell12500 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · have h := gap_lower (n := 12500) (a := (41917155202389 / 50000000000000 : ℝ)) (b := (164816889259 / 100000000000000 : ℝ)) (q := (455363101159 / 20000000000000 : ℝ))
      (E := (cell12500 ⟨7, by decide⟩).energy) (xi := (339557587310217 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12500 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12500]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12500])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12500) (a := (41917155202389 / 50000000000000 : ℝ)) (b := (164816889259 / 100000000000000 : ℝ)) (q := (455363101159 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12500])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12500])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12500]

theorem cert12500_8 : CellCertificate 12500 (2788636686689 / 31250000000000 : ℝ) (1680363136043441 / 1000000000000000000 : ℝ) (339557587310217 / 10000000000000000 : ℝ)
    (cell12500 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · have h := gap_lower (n := 12500) (a := (83799445021239 / 100000000000000 : ℝ)) (b := (164816889259 / 100000000000000 : ℝ)) (q := (9107278073 / 400000000000 : ℝ))
      (E := (cell12500 ⟨8, by decide⟩).energy) (xi := (339557587310217 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12500 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12500]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12500])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12500) (a := (83799445021239 / 100000000000000 : ℝ)) (b := (164816889259 / 100000000000000 : ℝ)) (q := (9107278073 / 400000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12500])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12500])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12500]

theorem cert12500_9 : CellCertificate 12500 (2788636686689 / 31250000000000 : ℝ) (1680363136043441 / 1000000000000000000 : ℝ) (339557587310217 / 10000000000000000 : ℝ)
    (cell12500 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · have h := gap_lower (n := 12500) (a := (83764604410807 / 100000000000000 : ℝ)) (b := (164816889259 / 100000000000000 : ℝ)) (q := (569205880033 / 25000000000000 : ℝ))
      (E := (cell12500 ⟨9, by decide⟩).energy) (xi := (339557587310217 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12500 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12500]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12500])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12500) (a := (83764604410807 / 100000000000000 : ℝ)) (b := (164816889259 / 100000000000000 : ℝ)) (q := (569205880033 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12500])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12500])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12500]

theorem cert12500_10 : CellCertificate 12500 (2788636686689 / 31250000000000 : ℝ) (1680363136043441 / 1000000000000000000 : ℝ) (339557587310217 / 10000000000000000 : ℝ)
    (cell12500 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · have h := gap_lower (n := 12500) (a := (83729788538107 / 100000000000000 : ℝ)) (b := (164816889259 / 100000000000000 : ℝ)) (q := (91073100753 / 4000000000000 : ℝ))
      (E := (cell12500 ⟨10, by decide⟩).energy) (xi := (339557587310217 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12500 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12500]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12500])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12500) (a := (83729788538107 / 100000000000000 : ℝ)) (b := (164816889259 / 100000000000000 : ℝ)) (q := (91073100753 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12500])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12500])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12500]

theorem cert12500_11 : CellCertificate 12500 (2788636686689 / 31250000000000 : ℝ) (1680363136043441 / 1000000000000000000 : ℝ) (339557587310217 / 10000000000000000 : ℝ)
    (cell12500 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · have h := gap_lower (n := 12500) (a := (20923749341987 / 25000000000000 : ℝ)) (b := (164816889259 / 100000000000000 : ℝ)) (q := (1138415760731 / 50000000000000 : ℝ))
      (E := (cell12500 ⟨11, by decide⟩).energy) (xi := (339557587310217 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12500 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12500]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12500])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12500) (a := (20923749341987 / 25000000000000 : ℝ)) (b := (164816889259 / 100000000000000 : ℝ)) (q := (1138415760731 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12500])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12500])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12500]

theorem cert12500_12 : CellCertificate 12500 (2788636686689 / 31250000000000 : ℝ) (1680363136043441 / 1000000000000000000 : ℝ) (339557587310217 / 10000000000000000 : ℝ)
    (cell12500 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · have h := gap_lower (n := 12500) (a := (83660230865327 / 100000000000000 : ℝ)) (b := (164816889259 / 100000000000000 : ℝ)) (q := (2276835534921 / 100000000000000 : ℝ))
      (E := (cell12500 ⟨12, by decide⟩).energy) (xi := (339557587310217 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12500 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12500]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12500])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12500) (a := (83660230865327 / 100000000000000 : ℝ)) (b := (164816889259 / 100000000000000 : ℝ)) (q := (2276835534921 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12500])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12500])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12500]

theorem cert12500_13 : CellCertificate 12500 (2788636686689 / 31250000000000 : ℝ) (1680363136043441 / 1000000000000000000 : ℝ) (339557587310217 / 10000000000000000 : ℝ)
    (cell12500 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · have h := gap_lower (n := 12500) (a := (41812744497709 / 50000000000000 : ℝ)) (b := (164816889259 / 100000000000000 : ℝ)) (q := (2276839507743 / 100000000000000 : ℝ))
      (E := (cell12500 ⟨13, by decide⟩).energy) (xi := (339557587310217 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12500 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12500]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12500])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12500) (a := (41812744497709 / 50000000000000 : ℝ)) (b := (164816889259 / 100000000000000 : ℝ)) (q := (2276839507743 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12500])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12500])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12500]

theorem cert12500_14 : CellCertificate 12500 (2788636686689 / 31250000000000 : ℝ) (1680363136043441 / 1000000000000000000 : ℝ) (339557587310217 / 10000000000000000 : ℝ)
    (cell12500 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · have h := gap_lower (n := 12500) (a := (41795385861791 / 50000000000000 : ℝ)) (b := (164816889259 / 100000000000000 : ℝ)) (q := (455368700871 / 20000000000000 : ℝ))
      (E := (cell12500 ⟨14, by decide⟩).energy) (xi := (339557587310217 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12500 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12500]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12500])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12500) (a := (41795385861791 / 50000000000000 : ℝ)) (b := (164816889259 / 100000000000000 : ℝ)) (q := (455368700871 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12500])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12500])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12500]

theorem cert12500_15 : CellCertificate 12500 (2788636686689 / 31250000000000 : ℝ) (1680363136043441 / 1000000000000000000 : ℝ) (339557587310217 / 10000000000000000 : ℝ)
    (cell12500 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · have h := gap_lower (n := 12500) (a := (83556079015357 / 100000000000000 : ℝ)) (b := (164816889259 / 100000000000000 : ℝ)) (q := (455369506179 / 20000000000000 : ℝ))
      (E := (cell12500 ⟨15, by decide⟩).energy) (xi := (339557587310217 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12500 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12500]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12500])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12500) (a := (83556079015357 / 100000000000000 : ℝ)) (b := (164816889259 / 100000000000000 : ℝ)) (q := (455369506179 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12500])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12500])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12500]

theorem cert12500_16 : CellCertificate 12500 (2788636686689 / 31250000000000 : ℝ) (1680363136043441 / 1000000000000000000 : ℝ) (339557587310217 / 10000000000000000 : ℝ)
    (cell12500 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · have h := gap_lower (n := 12500) (a := (4176070541823 / 5000000000000 : ℝ)) (b := (164816889259 / 100000000000000 : ℝ)) (q := (2276851535089 / 100000000000000 : ℝ))
      (E := (cell12500 ⟨16, by decide⟩).energy) (xi := (339557587310217 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12500 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12500]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12500])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12500) (a := (4176070541823 / 5000000000000 : ℝ)) (b := (164816889259 / 100000000000000 : ℝ)) (q := (2276851535089 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12500])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12500])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12500]

theorem cert12500_17 : CellCertificate 12500 (2788636686689 / 31250000000000 : ℝ) (1680363136043441 / 1000000000000000000 : ℝ) (339557587310217 / 10000000000000000 : ℝ)
    (cell12500 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · have h := gap_lower (n := 12500) (a := (83486767152789 / 100000000000000 : ℝ)) (b := (164816889259 / 100000000000000 : ℝ)) (q := (227685552251 / 10000000000000 : ℝ))
      (E := (cell12500 ⟨17, by decide⟩).energy) (xi := (339557587310217 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12500 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12500]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12500])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12500) (a := (83486767152789 / 100000000000000 : ℝ)) (b := (164816889259 / 100000000000000 : ℝ)) (q := (227685552251 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12500])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12500])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12500]

theorem cert12500_18 : CellCertificate 12500 (2788636686689 / 31250000000000 : ℝ) (1680363136043441 / 1000000000000000000 : ℝ) (339557587310217 / 10000000000000000 : ℝ)
    (cell12500 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · have h := gap_lower (n := 12500) (a := (16690429586083 / 20000000000000 : ℝ)) (b := (164816889259 / 100000000000000 : ℝ)) (q := (569214874623 / 25000000000000 : ℝ))
      (E := (cell12500 ⟨18, by decide⟩).energy) (xi := (339557587310217 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12500 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12500]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12500])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12500) (a := (16690429586083 / 20000000000000 : ℝ)) (b := (164816889259 / 100000000000000 : ℝ)) (q := (569214874623 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12500])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12500])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12500]

theorem cert12500_19 : CellCertificate 12500 (2788636686689 / 31250000000000 : ℝ) (1680363136043441 / 1000000000000000000 : ℝ) (339557587310217 / 10000000000000000 : ℝ)
    (cell12500 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · have h := gap_lower (n := 12500) (a := (20854388283897 / 25000000000000 : ℝ)) (b := (164816889259 / 100000000000000 : ℝ)) (q := (455372705271 / 20000000000000 : ℝ))
      (E := (cell12500 ⟨19, by decide⟩).energy) (xi := (339557587310217 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12500 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12500]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12500])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12500) (a := (20854388283897 / 25000000000000 : ℝ)) (b := (164816889259 / 100000000000000 : ℝ)) (q := (455372705271 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12500])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12500])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12500]

theorem cert12501_0 : CellCertificate 12501 (446167469926593 / 5000000000000000 : ℝ) (840114336423563 / 500000000000000000 : ℝ) (42441217093877 / 1250000000000000 : ℝ)
    (cell12501 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · have h := gap_lower (n := 12501) (a := (42039524565373 / 50000000000000 : ℝ)) (b := (164803537959 / 100000000000000 : ℝ)) (q := (569164167169 / 25000000000000 : ℝ))
      (E := (cell12501 ⟨0, by decide⟩).energy) (xi := (42441217093877 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12501 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12501]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12501])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12501) (a := (42039524565373 / 50000000000000 : ℝ)) (b := (164803537959 / 100000000000000 : ℝ)) (q := (569164167169 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12501])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12501])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12501]

theorem cert12501_1 : CellCertificate 12501 (446167469926593 / 5000000000000000 : ℝ) (840114336423563 / 500000000000000000 : ℝ) (42441217093877 / 1250000000000000 : ℝ)
    (cell12501 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · have h := gap_lower (n := 12501) (a := (5252750603573 / 6250000000000 : ℝ)) (b := (164803537959 / 100000000000000 : ℝ)) (q := (1821328519 / 80000000000 : ℝ))
      (E := (cell12501 ⟨1, by decide⟩).energy) (xi := (42441217093877 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12501 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12501]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12501])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12501) (a := (5252750603573 / 6250000000000 : ℝ)) (b := (164803537959 / 100000000000000 : ℝ)) (q := (1821328519 / 80000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12501])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12501])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12501]

theorem cert12501_2 : CellCertificate 12501 (446167469926593 / 5000000000000000 : ℝ) (840114336423563 / 500000000000000000 : ℝ) (42441217093877 / 1250000000000000 : ℝ)
    (cell12501 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · have h := gap_lower (n := 12501) (a := (84008995209139 / 100000000000000 : ℝ)) (b := (164803537959 / 100000000000000 : ℝ)) (q := (2276664617767 / 100000000000000 : ℝ))
      (E := (cell12501 ⟨2, by decide⟩).energy) (xi := (42441217093877 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12501 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12501]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12501])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12501) (a := (84008995209139 / 100000000000000 : ℝ)) (b := (164803537959 / 100000000000000 : ℝ)) (q := (2276664617767 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12501])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12501])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12501]

theorem cert12501_3 : CellCertificate 12501 (446167469926593 / 5000000000000000 : ℝ) (840114336423563 / 500000000000000000 : ℝ) (42441217093877 / 1250000000000000 : ℝ)
    (cell12501 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · have h := gap_lower (n := 12501) (a := (20993501437489 / 25000000000000 : ℝ)) (b := (164803537959 / 100000000000000 : ℝ)) (q := (455333728567 / 20000000000000 : ℝ))
      (E := (cell12501 ⟨3, by decide⟩).energy) (xi := (42441217093877 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12501 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12501]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12501])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12501) (a := (20993501437489 / 25000000000000 : ℝ)) (b := (164803537959 / 100000000000000 : ℝ)) (q := (455333728567 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12501])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12501])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12501]

theorem cert12501_4 : CellCertificate 12501 (446167469926593 / 5000000000000000 : ℝ) (840114336423563 / 500000000000000000 : ℝ) (42441217093877 / 1250000000000000 : ℝ)
    (cell12501 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · have h := gap_lower (n := 12501) (a := (20984760310777 / 25000000000000 : ℝ)) (b := (164803537959 / 100000000000000 : ℝ)) (q := (569168154311 / 25000000000000 : ℝ))
      (E := (cell12501 ⟨4, by decide⟩).energy) (xi := (42441217093877 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12501 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12501]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12501])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12501) (a := (20984760310777 / 25000000000000 : ℝ)) (b := (164803537959 / 100000000000000 : ℝ)) (q := (569168154311 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12501])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12501])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12501]

theorem cert12501_5 : CellCertificate 12501 (446167469926593 / 5000000000000000 : ℝ) (840114336423563 / 500000000000000000 : ℝ) (42441217093877 / 1250000000000000 : ℝ)
    (cell12501 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · have h := gap_lower (n := 12501) (a := (41952050826139 / 50000000000000 : ℝ)) (b := (164803537959 / 100000000000000 : ℝ)) (q := (2276676607559 / 100000000000000 : ℝ))
      (E := (cell12501 ⟨5, by decide⟩).energy) (xi := (42441217093877 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12501 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12501]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12501])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12501) (a := (41952050826139 / 50000000000000 : ℝ)) (b := (164803537959 / 100000000000000 : ℝ)) (q := (2276676607559 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12501])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12501])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12501]

theorem cert12501_6 : CellCertificate 12501 (446167469926593 / 5000000000000000 : ℝ) (840114336423563 / 500000000000000000 : ℝ) (42441217093877 / 1250000000000000 : ℝ)
    (cell12501 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · have h := gap_lower (n := 12501) (a := (83869186941341 / 100000000000000 : ℝ)) (b := (164803537959 / 100000000000000 : ℝ)) (q := (9106722489 / 400000000000 : ℝ))
      (E := (cell12501 ⟨6, by decide⟩).energy) (xi := (42441217093877 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12501 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12501]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12501])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12501) (a := (83869186941341 / 100000000000000 : ℝ)) (b := (164803537959 / 100000000000000 : ℝ)) (q := (9106722489 / 400000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12501])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12501])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12501]

theorem cert12501_7 : CellCertificate 12501 (446167469926593 / 5000000000000000 : ℝ) (840114336423563 / 500000000000000000 : ℝ) (42441217093877 / 1250000000000000 : ℝ)
    (cell12501 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · have h := gap_lower (n := 12501) (a := (83834297074359 / 100000000000000 : ℝ)) (b := (164803537959 / 100000000000000 : ℝ)) (q := (1138342305789 / 50000000000000 : ℝ))
      (E := (cell12501 ⟨7, by decide⟩).energy) (xi := (42441217093877 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12501 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12501]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12501])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12501) (a := (83834297074359 / 100000000000000 : ℝ)) (b := (164803537959 / 100000000000000 : ℝ)) (q := (1138342305789 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12501])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12501])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12501]

theorem cert12501_8 : CellCertificate 12501 (446167469926593 / 5000000000000000 : ℝ) (840114336423563 / 500000000000000000 : ℝ) (42441217093877 / 1250000000000000 : ℝ)
    (cell12501 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · have h := gap_lower (n := 12501) (a := (41899716007793 / 50000000000000 : ℝ)) (b := (164803537959 / 100000000000000 : ℝ)) (q := (227668864141 / 10000000000000 : ℝ))
      (E := (cell12501 ⟨8, by decide⟩).energy) (xi := (42441217093877 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12501 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12501]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12501])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12501) (a := (41899716007793 / 50000000000000 : ℝ)) (b := (164803537959 / 100000000000000 : ℝ)) (q := (227668864141 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12501])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12501])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12501]

theorem cert12501_9 : CellCertificate 12501 (446167469926593 / 5000000000000000 : ℝ) (840114336423563 / 500000000000000000 : ℝ) (42441217093877 / 1250000000000000 : ℝ)
    (cell12501 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · have h := gap_lower (n := 12501) (a := (83764591729461 / 100000000000000 : ℝ)) (b := (164803537959 / 100000000000000 : ℝ)) (q := (2276692603449 / 100000000000000 : ℝ))
      (E := (cell12501 ⟨9, by decide⟩).energy) (xi := (42441217093877 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12501 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12501]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12501])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12501) (a := (83764591729461 / 100000000000000 : ℝ)) (b := (164803537959 / 100000000000000 : ℝ)) (q := (2276692603449 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12501])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12501])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12501]

theorem cert12501_10 : CellCertificate 12501 (446167469926593 / 5000000000000000 : ℝ) (840114336423563 / 500000000000000000 : ℝ) (42441217093877 / 1250000000000000 : ℝ)
    (cell12501 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · have h := gap_lower (n := 12501) (a := (20932444045153 / 25000000000000 : ℝ)) (b := (164803537959 / 100000000000000 : ℝ)) (q := (2276696621053 / 100000000000000 : ℝ))
      (E := (cell12501 ⟨10, by decide⟩).energy) (xi := (42441217093877 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12501 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12501]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12501])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12501) (a := (20932444045153 / 25000000000000 : ℝ)) (b := (164803537959 / 100000000000000 : ℝ)) (q := (2276696621053 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12501])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12501])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12501]

theorem cert12501_11 : CellCertificate 12501 (446167469926593 / 5000000000000000 : ℝ) (840114336423563 / 500000000000000000 : ℝ) (42441217093877 / 1250000000000000 : ℝ)
    (cell12501 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · have h := gap_lower (n := 12501) (a := (83694985333849 / 100000000000000 : ℝ)) (b := (164803537959 / 100000000000000 : ℝ)) (q := (569175146333 / 25000000000000 : ℝ))
      (E := (cell12501 ⟨11, by decide⟩).energy) (xi := (42441217093877 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12501 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12501]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12501])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12501) (a := (83694985333849 / 100000000000000 : ℝ)) (b := (164803537959 / 100000000000000 : ℝ)) (q := (569175146333 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12501])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12501])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12501]

theorem cert12501_12 : CellCertificate 12501 (446167469926593 / 5000000000000000 : ℝ) (840114336423563 / 500000000000000000 : ℝ) (42441217093877 / 1250000000000000 : ℝ)
    (cell12501 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · have h := gap_lower (n := 12501) (a := (10457527394271 / 12500000000000 : ℝ)) (b := (164803537959 / 100000000000000 : ℝ)) (q := (1138352309617 / 50000000000000 : ℝ))
      (E := (cell12501 ⟨12, by decide⟩).energy) (xi := (42441217093877 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12501 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12501]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12501])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12501) (a := (10457527394271 / 12500000000000 : ℝ)) (b := (164803537959 / 100000000000000 : ℝ)) (q := (1138352309617 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12501])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12501])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12501]

theorem cert12501_13 : CellCertificate 12501 (446167469926593 / 5000000000000000 : ℝ) (840114336423563 / 500000000000000000 : ℝ) (42441217093877 / 1250000000000000 : ℝ)
    (cell12501 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · have h := gap_lower (n := 12501) (a := (41812738803373 / 50000000000000 : ℝ)) (b := (164803537959 / 100000000000000 : ℝ)) (q := (2276708613273 / 100000000000000 : ℝ))
      (E := (cell12501 ⟨13, by decide⟩).energy) (xi := (42441217093877 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12501 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12501]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12501])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12501) (a := (41812738803373 / 50000000000000 : ℝ)) (b := (164803537959 / 100000000000000 : ℝ)) (q := (2276708613273 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12501])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12501])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12501]

theorem cert12501_14 : CellCertificate 12501 (446167469926593 / 5000000000000000 : ℝ) (840114336423563 / 500000000000000000 : ℝ) (42441217093877 / 1250000000000000 : ℝ)
    (cell12501 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · have h := gap_lower (n := 12501) (a := (5224422541059 / 6250000000000 : ℝ)) (b := (164803537959 / 100000000000000 : ℝ)) (q := (7114726793 / 312500000000 : ℝ))
      (E := (cell12501 ⟨14, by decide⟩).energy) (xi := (42441217093877 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12501 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12501]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12501])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12501) (a := (5224422541059 / 6250000000000 : ℝ)) (b := (164803537959 / 100000000000000 : ℝ)) (q := (7114726793 / 312500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12501])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12501])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12501]

theorem cert12501_15 : CellCertificate 12501 (446167469926593 / 5000000000000000 : ℝ) (840114336423563 / 500000000000000000 : ℝ) (42441217093877 / 1250000000000000 : ℝ)
    (cell12501 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · have h := gap_lower (n := 12501) (a := (835560682703 / 1000000000000 : ℝ)) (b := (164803537959 / 100000000000000 : ℝ)) (q := (455343324609 / 20000000000000 : ℝ))
      (E := (cell12501 ⟨15, by decide⟩).energy) (xi := (42441217093877 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12501 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12501]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12501])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12501) (a := (835560682703 / 1000000000000 : ℝ)) (b := (164803537959 / 100000000000000 : ℝ)) (q := (455343324609 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12501])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12501])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12501]

theorem cert12501_16 : CellCertificate 12501 (446167469926593 / 5000000000000000 : ℝ) (840114336423563 / 500000000000000000 : ℝ) (42441217093877 / 1250000000000000 : ℝ)
    (cell12501 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · have h := gap_lower (n := 12501) (a := (16704280082507 / 20000000000000 : ℝ)) (b := (164803537959 / 100000000000000 : ℝ)) (q := (227672059259 / 10000000000000 : ℝ))
      (E := (cell12501 ⟨16, by decide⟩).energy) (xi := (42441217093877 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12501 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12501]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12501])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12501) (a := (16704280082507 / 20000000000000 : ℝ)) (b := (164803537959 / 100000000000000 : ℝ)) (q := (227672059259 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12501])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12501])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12501]

theorem cert12501_17 : CellCertificate 12501 (446167469926593 / 5000000000000000 : ℝ) (840114336423563 / 500000000000000000 : ℝ) (42441217093877 / 1250000000000000 : ℝ)
    (cell12501 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · have h := gap_lower (n := 12501) (a := (10435844631193 / 12500000000000 : ℝ)) (b := (164803537959 / 100000000000000 : ℝ)) (q := (2276724604277 / 100000000000000 : ℝ))
      (E := (cell12501 ⟨17, by decide⟩).energy) (xi := (42441217093877 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12501 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12501]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12501])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12501) (a := (10435844631193 / 12500000000000 : ℝ)) (b := (164803537959 / 100000000000000 : ℝ)) (q := (2276724604277 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12501])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12501])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12501]

theorem cert12501_18 : CellCertificate 12501 (446167469926593 / 5000000000000000 : ℝ) (840114336423563 / 500000000000000000 : ℝ) (42441217093877 / 1250000000000000 : ℝ)
    (cell12501 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · have h := gap_lower (n := 12501) (a := (41726069073701 / 50000000000000 : ℝ)) (b := (164803537959 / 100000000000000 : ℝ)) (q := (455345721059 / 20000000000000 : ℝ))
      (E := (cell12501 ⟨18, by decide⟩).energy) (xi := (42441217093877 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12501 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12501]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12501])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12501) (a := (41726069073701 / 50000000000000 : ℝ)) (b := (164803537959 / 100000000000000 : ℝ)) (q := (455345721059 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12501])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12501])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12501]

theorem cert12501_19 : CellCertificate 12501 (446167469926593 / 5000000000000000 : ℝ) (840114336423563 / 500000000000000000 : ℝ) (42441217093877 / 1250000000000000 : ℝ)
    (cell12501 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · have h := gap_lower (n := 12501) (a := (83417543672359 / 100000000000000 : ℝ)) (b := (164803537959 / 100000000000000 : ℝ)) (q := (227673260073 / 10000000000000 : ℝ))
      (E := (cell12501 ⟨19, by decide⟩).energy) (xi := (42441217093877 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12501 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12501]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12501])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12501) (a := (83417543672359 / 100000000000000 : ℝ)) (b := (164803537959 / 100000000000000 : ℝ)) (q := (227673260073 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12501])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12501])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12501]

theorem cert12502_0 : CellCertificate 12502 (178461228879307 / 2000000000000000 : ℝ) (1680094231168663 / 1000000000000000000 : ℝ) (339501890844129 / 10000000000000000 : ℝ)
    (cell12502 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · have h := gap_lower (n := 12502) (a := (84079033516573 / 100000000000000 : ℝ)) (b := (82395094421 / 50000000000000 : ℝ)) (q := (1138262892663 / 50000000000000 : ℝ))
      (E := (cell12502 ⟨0, by decide⟩).energy) (xi := (339501890844129 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12502 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12502]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12502])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12502) (a := (84079033516573 / 100000000000000 : ℝ)) (b := (82395094421 / 50000000000000 : ℝ)) (q := (1138262892663 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12502])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12502])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12502]

theorem cert12502_1 : CellCertificate 12502 (178461228879307 / 2000000000000000 : ℝ) (1680094231168663 / 1000000000000000000 : ℝ) (339501890844129 / 10000000000000000 : ℝ)
    (cell12502 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · have h := gap_lower (n := 12502) (a := (84043994370951 / 100000000000000 : ℝ)) (b := (82395094421 / 50000000000000 : ℝ)) (q := (1138264888691 / 50000000000000 : ℝ))
      (E := (cell12502 ⟨1, by decide⟩).energy) (xi := (339501890844129 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12502 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12502]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12502])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12502) (a := (84043994370951 / 100000000000000 : ℝ)) (b := (82395094421 / 50000000000000 : ℝ)) (q := (1138264888691 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12502])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12502])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12502]

theorem cert12502_2 : CellCertificate 12502 (178461228879307 / 2000000000000000 : ℝ) (1680094231168663 / 1000000000000000000 : ℝ) (339501890844129 / 10000000000000000 : ℝ)
    (cell12502 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · have h := gap_lower (n := 12502) (a := (42004490125207 / 50000000000000 : ℝ)) (b := (82395094421 / 50000000000000 : ℝ)) (q := (2276533759167 / 100000000000000 : ℝ))
      (E := (cell12502 ⟨2, by decide⟩).energy) (xi := (339501890844129 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12502 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12502]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12502])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12502) (a := (42004490125207 / 50000000000000 : ℝ)) (b := (82395094421 / 50000000000000 : ℝ)) (q := (2276533759167 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12502])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12502])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12502]

theorem cert12502_3 : CellCertificate 12502 (178461228879307 / 2000000000000000 : ℝ) (1680094231168663 / 1000000000000000000 : ℝ) (339501890844129 / 10000000000000000 : ℝ)
    (cell12502 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · have h := gap_lower (n := 12502) (a := (83973991118259 / 100000000000000 : ℝ)) (b := (82395094421 / 50000000000000 : ℝ)) (q := (2276537797789 / 100000000000000 : ℝ))
      (E := (cell12502 ⟨3, by decide⟩).energy) (xi := (339501890844129 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12502 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12502]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12502])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12502) (a := (83973991118259 / 100000000000000 : ℝ)) (b := (82395094421 / 50000000000000 : ℝ)) (q := (2276537797789 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12502])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12502])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12502]

theorem cert12502_4 : CellCertificate 12502 (178461228879307 / 2000000000000000 : ℝ) (1680094231168663 / 1000000000000000000 : ℝ) (339501890844129 / 10000000000000000 : ℝ)
    (cell12502 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · have h := gap_lower (n := 12502) (a := (83939026937977 / 100000000000000 : ℝ)) (b := (82395094421 / 50000000000000 : ℝ)) (q := (455308357307 / 20000000000000 : ℝ))
      (E := (cell12502 ⟨4, by decide⟩).energy) (xi := (339501890844129 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12502 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12502]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12502])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12502) (a := (83939026937977 / 100000000000000 : ℝ)) (b := (82395094421 / 50000000000000 : ℝ)) (q := (455308357307 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12502])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12502])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12502]

theorem cert12502_5 : CellCertificate 12502 (178461228879307 / 2000000000000000 : ℝ) (1680094231168663 / 1000000000000000000 : ℝ) (339501890844129 / 10000000000000000 : ℝ)
    (cell12502 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · have h := gap_lower (n := 12502) (a := (83904087673251 / 100000000000000 : ℝ)) (b := (82395094421 / 50000000000000 : ℝ)) (q := (569136447993 / 25000000000000 : ℝ))
      (E := (cell12502 ⟨5, by decide⟩).energy) (xi := (339501890844129 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12502 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12502]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12502])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12502) (a := (83904087673251 / 100000000000000 : ℝ)) (b := (82395094421 / 50000000000000 : ℝ)) (q := (569136447993 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12502])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12502])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12502]

theorem cert12502_6 : CellCertificate 12502 (178461228879307 / 2000000000000000 : ℝ) (1680094231168663 / 1000000000000000000 : ℝ) (339501890844129 / 10000000000000000 : ℝ)
    (cell12502 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · have h := gap_lower (n := 12502) (a := (83869173287957 / 100000000000000 : ℝ)) (b := (82395094421 / 50000000000000 : ℝ)) (q := (569137441159 / 25000000000000 : ℝ))
      (E := (cell12502 ⟨6, by decide⟩).energy) (xi := (339501890844129 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12502 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12502]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12502])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12502) (a := (83869173287957 / 100000000000000 : ℝ)) (b := (82395094421 / 50000000000000 : ℝ)) (q := (569137441159 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12502])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12502])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12502]

theorem cert12502_7 : CellCertificate 12502 (178461228879307 / 2000000000000000 : ℝ) (1680094231168663 / 1000000000000000000 : ℝ) (339501890844129 / 10000000000000000 : ℝ)
    (cell12502 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · have h := gap_lower (n := 12502) (a := (83834283746159 / 100000000000000 : ℝ)) (b := (82395094421 / 50000000000000 : ℝ)) (q := (1138276885313 / 50000000000000 : ℝ))
      (E := (cell12502 ⟨7, by decide⟩).energy) (xi := (339501890844129 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12502 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12502]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12502])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12502) (a := (83834283746159 / 100000000000000 : ℝ)) (b := (82395094421 / 50000000000000 : ℝ)) (q := (1138276885313 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12502])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12502])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12502]

theorem cert12502_8 : CellCertificate 12502 (178461228879307 / 2000000000000000 : ℝ) (1680094231168663 / 1000000000000000000 : ℝ) (339501890844129 / 10000000000000000 : ℝ)
    (cell12502 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · have h := gap_lower (n := 12502) (a := (83799419012111 / 100000000000000 : ℝ)) (b := (82395094421 / 50000000000000 : ℝ)) (q := (1138278879961 / 50000000000000 : ℝ))
      (E := (cell12502 ⟨8, by decide⟩).energy) (xi := (339501890844129 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12502 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12502]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12502])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12502) (a := (83799419012111 / 100000000000000 : ℝ)) (b := (82395094421 / 50000000000000 : ℝ)) (q := (1138278879961 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12502])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12502])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12502]

theorem cert12502_9 : CellCertificate 12502 (178461228879307 / 2000000000000000 : ℝ) (1680094231168663 / 1000000000000000000 : ℝ) (339501890844129 / 10000000000000000 : ℝ)
    (cell12502 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · have h := gap_lower (n := 12502) (a := (41882289525127 / 50000000000000 : ℝ)) (b := (82395094421 / 50000000000000 : ℝ)) (q := (1138280870079 / 50000000000000 : ℝ))
      (E := (cell12502 ⟨9, by decide⟩).energy) (xi := (339501890844129 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12502 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12502]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12502])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12502) (a := (41882289525127 / 50000000000000 : ℝ)) (b := (82395094421 / 50000000000000 : ℝ)) (q := (1138280870079 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12502])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12502])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12502]

theorem cert12502_10 : CellCertificate 12502 (178461228879307 / 2000000000000000 : ℝ) (1680094231168663 / 1000000000000000000 : ℝ) (339501890844129 / 10000000000000000 : ℝ)
    (cell12502 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · have h := gap_lower (n := 12502) (a := (1308277559769 / 1562500000000 : ℝ)) (b := (82395094421 / 50000000000000 : ℝ)) (q := (2276565776739 / 100000000000000 : ℝ))
      (E := (cell12502 ⟨10, by decide⟩).energy) (xi := (339501890844129 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12502 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12502]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12502])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12502) (a := (1308277559769 / 1562500000000 : ℝ)) (b := (82395094421 / 50000000000000 : ℝ)) (q := (2276565776739 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12502])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12502])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12502]

theorem cert12502_11 : CellCertificate 12502 (178461228879307 / 2000000000000000 : ℝ) (1680094231168663 / 1000000000000000000 : ℝ) (339501890844129 / 10000000000000000 : ℝ)
    (cell12502 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · have h := gap_lower (n := 12502) (a := (5230935831363 / 6250000000000 : ℝ)) (b := (82395094421 / 50000000000000 : ℝ)) (q := (2276569760771 / 100000000000000 : ℝ))
      (E := (cell12502 ⟨11, by decide⟩).energy) (xi := (339501890844129 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12502 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12502]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12502])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12502) (a := (5230935831363 / 6250000000000 : ℝ)) (b := (82395094421 / 50000000000000 : ℝ)) (q := (2276569760771 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12502])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12502])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12502]

theorem cert12502_12 : CellCertificate 12502 (178461228879307 / 2000000000000000 : ℝ) (1680094231168663 / 1000000000000000000 : ℝ) (339501890844129 / 10000000000000000 : ℝ)
    (cell12502 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · have h := gap_lower (n := 12502) (a := (83660207445027 / 100000000000000 : ℝ)) (b := (82395094421 / 50000000000000 : ℝ)) (q := (1138286878567 / 50000000000000 : ℝ))
      (E := (cell12502 ⟨12, by decide⟩).energy) (xi := (339501890844129 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12502 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12502]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12502])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12502) (a := (83660207445027 / 100000000000000 : ℝ)) (b := (82395094421 / 50000000000000 : ℝ)) (q := (1138286878567 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12502])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12502])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12502]

theorem cert12502_13 : CellCertificate 12502 (178461228879307 / 2000000000000000 : ℝ) (1680094231168663 / 1000000000000000000 : ℝ) (339501890844129 / 10000000000000000 : ℝ)
    (cell12502 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · have h := gap_lower (n := 12502) (a := (83625466220053 / 100000000000000 : ℝ)) (b := (82395094421 / 50000000000000 : ℝ)) (q := (56914442859 / 2500000000000 : ℝ))
      (E := (cell12502 ⟨13, by decide⟩).energy) (xi := (339501890844129 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12502 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12502]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12502])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12502) (a := (83625466220053 / 100000000000000 : ℝ)) (b := (82395094421 / 50000000000000 : ℝ)) (q := (56914442859 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12502])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12502])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12502]

theorem cert12502_14 : CellCertificate 12502 (178461228879307 / 2000000000000000 : ℝ) (1680094231168663 / 1000000000000000000 : ℝ) (339501890844129 / 10000000000000000 : ℝ)
    (cell12502 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · have h := gap_lower (n := 12502) (a := (20897687398061 / 25000000000000 : ℝ)) (b := (82395094421 / 50000000000000 : ℝ)) (q := (455316351 / 20000000000 : ℝ))
      (E := (cell12502 ⟨14, by decide⟩).energy) (xi := (339501890844129 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12502 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12502]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12502])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12502) (a := (20897687398061 / 25000000000000 : ℝ)) (b := (82395094421 / 50000000000000 : ℝ)) (q := (455316351 / 20000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12502])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12502])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12502]

theorem cert12502_15 : CellCertificate 12502 (178461228879307 / 2000000000000000 : ℝ) (1680094231168663 / 1000000000000000000 : ℝ) (339501890844129 / 10000000000000000 : ℝ)
    (cell12502 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · have h := gap_lower (n := 12502) (a := (83556057527143 / 100000000000000 : ℝ)) (b := (82395094421 / 50000000000000 : ℝ)) (q := (2276585710833 / 100000000000000 : ℝ))
      (E := (cell12502 ⟨15, by decide⟩).energy) (xi := (339501890844129 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12502 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12502]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12502])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12502) (a := (83556057527143 / 100000000000000 : ℝ)) (b := (82395094421 / 50000000000000 : ℝ)) (q := (2276585710833 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12502])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12502])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12502]

theorem cert12502_16 : CellCertificate 12502 (178461228879307 / 2000000000000000 : ℝ) (1680094231168663 / 1000000000000000000 : ℝ) (339501890844129 / 10000000000000000 : ℝ)
    (cell12502 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · have h := gap_lower (n := 12502) (a := (83521389990469 / 100000000000000 : ℝ)) (b := (82395094421 / 50000000000000 : ℝ)) (q := (455317940787 / 20000000000000 : ℝ))
      (E := (cell12502 ⟨16, by decide⟩).energy) (xi := (339501890844129 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12502 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12502]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12502])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12502) (a := (83521389990469 / 100000000000000 : ℝ)) (b := (82395094421 / 50000000000000 : ℝ)) (q := (455317940787 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12502])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12502])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12502]

theorem cert12502_17 : CellCertificate 12502 (178461228879307 / 2000000000000000 : ℝ) (1680094231168663 / 1000000000000000000 : ℝ) (339501890844129 / 10000000000000000 : ℝ)
    (cell12502 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · have h := gap_lower (n := 12502) (a := (2087168673703 / 2500000000000 : ℝ)) (b := (82395094421 / 50000000000000 : ℝ)) (q := (2276593739951 / 100000000000000 : ℝ))
      (E := (cell12502 ⟨17, by decide⟩).energy) (xi := (339501890844129 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12502 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12502]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12502])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12502) (a := (2087168673703 / 2500000000000 : ℝ)) (b := (82395094421 / 50000000000000 : ℝ)) (q := (2276593739951 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12502])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12502])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12502]

theorem cert12502_18 : CellCertificate 12502 (178461228879307 / 2000000000000000 : ℝ) (1680094231168663 / 1000000000000000000 : ℝ) (339501890844129 / 10000000000000000 : ℝ)
    (cell12502 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · have h := gap_lower (n := 12502) (a := (8345212836617 / 10000000000000 : ℝ)) (b := (82395094421 / 50000000000000 : ℝ)) (q := (1138298853929 / 50000000000000 : ℝ))
      (E := (cell12502 ⟨18, by decide⟩).energy) (xi := (339501890844129 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12502 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12502]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12502])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12502) (a := (8345212836617 / 10000000000000 : ℝ)) (b := (82395094421 / 50000000000000 : ℝ)) (q := (1138298853929 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12502])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12502])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12502]

theorem cert12502_19 : CellCertificate 12502 (178461228879307 / 2000000000000000 : ℝ) (1680094231168663 / 1000000000000000000 : ℝ) (339501890844129 / 10000000000000000 : ℝ)
    (cell12502 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · have h := gap_lower (n := 12502) (a := (83417534210871 / 100000000000000 : ℝ)) (b := (82395094421 / 50000000000000 : ℝ)) (q := (113830086457 / 5000000000000 : ℝ))
      (E := (cell12502 ⟨19, by decide⟩).energy) (xi := (339501890844129 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12502 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12502]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12502])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12502) (a := (83417534210871 / 100000000000000 : ℝ)) (b := (82395094421 / 50000000000000 : ℝ)) (q := (113830086457 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12502])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12502])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12502]

theorem cert12503_0 : CellCertificate 12503 (892277353369453 / 10000000000000000 : ℝ) (1679959811002887 / 1000000000000000000 : ℝ) (42434256198533 / 1250000000000000 : ℝ)
    (cell12503 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · have h := gap_lower (n := 12503) (a := (840790179049 / 1000000000000 : ℝ)) (b := (164776841909 / 100000000000000 : ℝ)) (q := (1138197477393 / 50000000000000 : ℝ))
      (E := (cell12503 ⟨0, by decide⟩).energy) (xi := (42434256198533 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12503 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12503]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12503])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12503) (a := (840790179049 / 1000000000000 : ℝ)) (b := (164776841909 / 100000000000000 : ℝ)) (q := (1138197477393 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12503])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12503])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12503]

theorem cert12503_1 : CellCertificate 12503 (892277353369453 / 10000000000000000 : ℝ) (1679959811002887 / 1000000000000000000 : ℝ) (42434256198533 / 1250000000000000 : ℝ)
    (cell12503 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · have h := gap_lower (n := 12503) (a := (16808795817439 / 20000000000000 : ℝ)) (b := (164776841909 / 100000000000000 : ℝ)) (q := (284549869861 / 12500000000000 : ℝ))
      (E := (cell12503 ⟨1, by decide⟩).energy) (xi := (42434256198533 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12503 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12503]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12503])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12503) (a := (16808795817439 / 20000000000000 : ℝ)) (b := (164776841909 / 100000000000000 : ℝ)) (q := (284549869861 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12503])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12503])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12503]

theorem cert12503_2 : CellCertificate 12503 (892277353369453 / 10000000000000000 : ℝ) (1679959811002887 / 1000000000000000000 : ℝ) (42434256198533 / 1250000000000000 : ℝ)
    (cell12503 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · have h := gap_lower (n := 12503) (a := (84008965294109 / 100000000000000 : ℝ)) (b := (164776841909 / 100000000000000 : ℝ)) (q := (2276402953507 / 100000000000000 : ℝ))
      (E := (cell12503 ⟨2, by decide⟩).energy) (xi := (42434256198533 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12503 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12503]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12503])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12503) (a := (84008965294109 / 100000000000000 : ℝ)) (b := (164776841909 / 100000000000000 : ℝ)) (q := (2276402953507 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12503])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12503])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12503]

theorem cert12503_3 : CellCertificate 12503 (892277353369453 / 10000000000000000 : ℝ) (1679959811002887 / 1000000000000000000 : ℝ) (42434256198533 / 1250000000000000 : ℝ)
    (cell12503 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · have h := gap_lower (n := 12503) (a := (41986988244471 / 50000000000000 : ℝ)) (b := (164776841909 / 100000000000000 : ℝ)) (q := (2276406947887 / 100000000000000 : ℝ))
      (E := (cell12503 ⟨3, by decide⟩).energy) (xi := (42434256198533 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12503 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12503]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12503])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12503) (a := (41986988244471 / 50000000000000 : ℝ)) (b := (164776841909 / 100000000000000 : ℝ)) (q := (2276406947887 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12503])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12503])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12503]

theorem cert12503_4 : CellCertificate 12503 (892277353369453 / 10000000000000000 : ℝ) (1679959811002887 / 1000000000000000000 : ℝ) (42434256198533 / 1250000000000000 : ℝ)
    (cell12503 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · have h := gap_lower (n := 12503) (a := (16787802527037 / 20000000000000 : ℝ)) (b := (164776841909 / 100000000000000 : ℝ)) (q := (2276410951013 / 100000000000000 : ℝ))
      (E := (cell12503 ⟨4, by decide⟩).energy) (xi := (42434256198533 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12503 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12503]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12503])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12503) (a := (16787802527037 / 20000000000000 : ℝ)) (b := (164776841909 / 100000000000000 : ℝ)) (q := (2276410951013 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12503])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12503])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12503]

theorem cert12503_5 : CellCertificate 12503 (892277353369453 / 10000000000000000 : ℝ) (1679959811002887 / 1000000000000000000 : ℝ) (42434256198533 / 1250000000000000 : ℝ)
    (cell12503 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · have h := gap_lower (n := 12503) (a := (83904073696523 / 100000000000000 : ℝ)) (b := (164776841909 / 100000000000000 : ℝ)) (q := (569103742903 / 25000000000000 : ℝ))
      (E := (cell12503 ⟨5, by decide⟩).energy) (xi := (42434256198533 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12503 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12503]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12503])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12503) (a := (83904073696523 / 100000000000000 : ℝ)) (b := (164776841909 / 100000000000000 : ℝ)) (q := (569103742903 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12503])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12503])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12503]

theorem cert12503_6 : CellCertificate 12503 (892277353369453 / 10000000000000000 : ℝ) (1679959811002887 / 1000000000000000000 : ℝ) (42434256198533 / 1250000000000000 : ℝ)
    (cell12503 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · have h := gap_lower (n := 12503) (a := (2620911238651 / 3125000000000 : ℝ)) (b := (164776841909 / 100000000000000 : ℝ)) (q := (2276418960221 / 100000000000000 : ℝ))
      (E := (cell12503 ⟨6, by decide⟩).energy) (xi := (42434256198533 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12503 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12503]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12503])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12503) (a := (2620911238651 / 3125000000000 : ℝ)) (b := (164776841909 / 100000000000000 : ℝ)) (q := (2276418960221 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12503])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12503])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12503]

theorem cert12503_7 : CellCertificate 12503 (892277353369453 / 10000000000000000 : ℝ) (1679959811002887 / 1000000000000000000 : ℝ) (42434256198533 / 1250000000000000 : ℝ)
    (cell12503 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · have h := gap_lower (n := 12503) (a := (41917135210089 / 50000000000000 : ℝ)) (b := (164776841909 / 100000000000000 : ℝ)) (q := (1138211462491 / 50000000000000 : ℝ))
      (E := (cell12503 ⟨7, by decide⟩).energy) (xi := (42434256198533 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12503 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12503]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12503])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12503) (a := (41917135210089 / 50000000000000 : ℝ)) (b := (164776841909 / 100000000000000 : ℝ)) (q := (1138211462491 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12503])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12503])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12503]

theorem cert12503_8 : CellCertificate 12503 (892277353369453 / 10000000000000000 : ℝ) (1679959811002887 / 1000000000000000000 : ℝ) (42434256198533 / 1250000000000000 : ℝ)
    (cell12503 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · have h := gap_lower (n := 12503) (a := (16759881202163 / 20000000000000 : ℝ)) (b := (164776841909 / 100000000000000 : ℝ)) (q := (1138213465881 / 50000000000000 : ℝ))
      (E := (cell12503 ⟨8, by decide⟩).energy) (xi := (42434256198533 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12503 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12503]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12503])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12503) (a := (16759881202163 / 20000000000000 : ℝ)) (b := (164776841909 / 100000000000000 : ℝ)) (q := (1138213465881 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12503])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12503])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12503]

theorem cert12503_9 : CellCertificate 12503 (892277353369453 / 10000000000000000 : ℝ) (1679959811002887 / 1000000000000000000 : ℝ) (42434256198533 / 1250000000000000 : ℝ)
    (cell12503 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · have h := gap_lower (n := 12503) (a := (16752913274637 / 20000000000000 : ℝ)) (b := (164776841909 / 100000000000000 : ℝ)) (q := (2276430930261 / 100000000000000 : ℝ))
      (E := (cell12503 ⟨9, by decide⟩).energy) (xi := (42434256198533 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12503 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12503]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12503])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12503) (a := (16752913274637 / 20000000000000 : ℝ)) (b := (164776841909 / 100000000000000 : ℝ)) (q := (2276430930261 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12503])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12503])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12503]

theorem cert12503_10 : CellCertificate 12503 (892277353369453 / 10000000000000000 : ℝ) (1679959811002887 / 1000000000000000000 : ℝ) (42434256198533 / 1250000000000000 : ℝ)
    (cell12503 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · have h := gap_lower (n := 12503) (a := (41864875735959 / 50000000000000 : ℝ)) (b := (164776841909 / 100000000000000 : ℝ)) (q := (2276434927859 / 100000000000000 : ℝ))
      (E := (cell12503 ⟨10, by decide⟩).energy) (xi := (42434256198533 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12503 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12503]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12503])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12503) (a := (41864875735959 / 50000000000000 : ℝ)) (b := (164776841909 / 100000000000000 : ℝ)) (q := (2276434927859 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12503])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12503])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12503]

theorem cert12503_11 : CellCertificate 12503 (892277353369453 / 10000000000000000 : ℝ) (1679959811002887 / 1000000000000000000 : ℝ) (42434256198533 / 1250000000000000 : ℝ)
    (cell12503 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · have h := gap_lower (n := 12503) (a := (41847480635913 / 50000000000000 : ℝ)) (b := (164776841909 / 100000000000000 : ℝ)) (q := (455287786337 / 20000000000000 : ℝ))
      (E := (cell12503 ⟨11, by decide⟩).energy) (xi := (42434256198533 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12503 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12503]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12503])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12503) (a := (41847480635913 / 50000000000000 : ℝ)) (b := (164776841909 / 100000000000000 : ℝ)) (q := (455287786337 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12503])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12503])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12503]

theorem cert12503_12 : CellCertificate 12503 (892277353369453 / 10000000000000000 : ℝ) (1679959811002887 / 1000000000000000000 : ℝ) (42434256198533 / 1250000000000000 : ℝ)
    (cell12503 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · have h := gap_lower (n := 12503) (a := (41830097868953 / 50000000000000 : ℝ)) (b := (164776841909 / 100000000000000 : ℝ)) (q := (1138221474309 / 50000000000000 : ℝ))
      (E := (cell12503 ⟨12, by decide⟩).energy) (xi := (42434256198533 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12503 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12503]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12503])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12503) (a := (41830097868953 / 50000000000000 : ℝ)) (b := (164776841909 / 100000000000000 : ℝ)) (q := (1138221474309 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12503])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12503])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12503]

theorem cert12503_13 : CellCertificate 12503 (892277353369453 / 10000000000000000 : ℝ) (1679959811002887 / 1000000000000000000 : ℝ) (42434256198533 / 1250000000000000 : ℝ)
    (cell12503 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · have h := gap_lower (n := 12503) (a := (41812727417669 / 50000000000000 : ℝ)) (b := (164776841909 / 100000000000000 : ℝ)) (q := (2276446927193 / 100000000000000 : ℝ))
      (E := (cell12503 ⟨13, by decide⟩).energy) (xi := (42434256198533 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12503 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12503]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12503])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12503) (a := (41812727417669 / 50000000000000 : ℝ)) (b := (164776841909 / 100000000000000 : ℝ)) (q := (2276446927193 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12503])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12503])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12503]

theorem cert12503_14 : CellCertificate 12503 (892277353369453 / 10000000000000000 : ℝ) (1679959811002887 / 1000000000000000000 : ℝ) (42434256198533 / 1250000000000000 : ℝ)
    (cell12503 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · have h := gap_lower (n := 12503) (a := (20897684632371 / 25000000000000 : ℝ)) (b := (164776841909 / 100000000000000 : ℝ)) (q := (569112732959 / 25000000000000 : ℝ))
      (E := (cell12503 ⟨14, by decide⟩).energy) (xi := (42434256198533 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12503 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12503]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12503])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12503) (a := (20897684632371 / 25000000000000 : ℝ)) (b := (164776841909 / 100000000000000 : ℝ)) (q := (569112732959 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12503])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12503])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12503]

theorem cert12503_15 : CellCertificate 12503 (892277353369453 / 10000000000000000 : ℝ) (1679959811002887 / 1000000000000000000 : ℝ) (42434256198533 / 1250000000000000 : ℝ)
    (cell12503 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · have h := gap_lower (n := 12503) (a := (16711209357177 / 20000000000000 : ℝ)) (b := (164776841909 / 100000000000000 : ℝ)) (q := (2276454910541 / 100000000000000 : ℝ))
      (E := (cell12503 ⟨15, by decide⟩).energy) (xi := (42434256198533 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12503 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12503]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12503])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12503) (a := (16711209357177 / 20000000000000 : ℝ)) (b := (164776841909 / 100000000000000 : ℝ)) (q := (2276454910541 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12503])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12503])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12503]

theorem cert12503_16 : CellCertificate 12503 (892277353369453 / 10000000000000000 : ℝ) (1679959811002887 / 1000000000000000000 : ℝ) (42434256198533 / 1250000000000000 : ℝ)
    (cell12503 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · have h := gap_lower (n := 12503) (a := (83521379570263 / 100000000000000 : ℝ)) (b := (164776841909 / 100000000000000 : ℝ)) (q := (284557365911 / 12500000000000 : ℝ))
      (E := (cell12503 ⟨16, by decide⟩).energy) (xi := (42434256198533 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12503 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12503]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12503])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12503) (a := (83521379570263 / 100000000000000 : ℝ)) (b := (164776841909 / 100000000000000 : ℝ)) (q := (284557365911 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12503])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12503])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12503]

theorem cert12503_17 : CellCertificate 12503 (892277353369453 / 10000000000000000 : ℝ) (1679959811002887 / 1000000000000000000 : ℝ) (42434256198533 / 1250000000000000 : ℝ)
    (cell12503 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · have h := gap_lower (n := 12503) (a := (16697347369703 / 20000000000000 : ℝ)) (b := (164776841909 / 100000000000000 : ℝ)) (q := (2276462929533 / 100000000000000 : ℝ))
      (E := (cell12503 ⟨17, by decide⟩).energy) (xi := (42434256198533 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12503 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12503]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12503])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12503) (a := (16697347369703 / 20000000000000 : ℝ)) (b := (164776841909 / 100000000000000 : ℝ)) (q := (2276462929533 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12503])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12503])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12503]

theorem cert12503_18 : CellCertificate 12503 (892277353369453 / 10000000000000000 : ℝ) (1679959811002887 / 1000000000000000000 : ℝ) (42434256198533 / 1250000000000000 : ℝ)
    (cell12503 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · have h := gap_lower (n := 12503) (a := (83452118586719 / 100000000000000 : ℝ)) (b := (164776841909 / 100000000000000 : ℝ)) (q := (2276466922603 / 100000000000000 : ℝ))
      (E := (cell12503 ⟨18, by decide⟩).energy) (xi := (42434256198533 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12503 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12503]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12503])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12503) (a := (83452118586719 / 100000000000000 : ℝ)) (b := (164776841909 / 100000000000000 : ℝ)) (q := (2276466922603 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12503])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12503])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12503]

theorem cert12503_19 : CellCertificate 12503 (892277353369453 / 10000000000000000 : ℝ) (1679959811002887 / 1000000000000000000 : ℝ) (42434256198533 / 1250000000000000 : ℝ)
    (cell12503 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · have h := gap_lower (n := 12503) (a := (20854381187781 / 25000000000000 : ℝ)) (b := (164776841909 / 100000000000000 : ℝ)) (q := (1138235455793 / 50000000000000 : ℝ))
      (E := (cell12503 ⟨19, by decide⟩).energy) (xi := (42434256198533 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12503 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12503]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12503])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12503) (a := (20854381187781 / 25000000000000 : ℝ)) (b := (164776841909 / 100000000000000 : ℝ)) (q := (1138235455793 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12503])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12503])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12503]

theorem cert12504_0 : CellCertificate 12504 (892248566770871 / 10000000000000000 : ℝ) (419956353086159 / 250000000000000000 : ℝ) (67889242596427 / 2000000000000000 : ℝ)
    (cell12504 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · have h := gap_lower (n := 12504) (a := (5254937643483 / 6250000000000 : ℝ)) (b := (164763497157 / 100000000000000 : ℝ)) (q := (1138132088529 / 50000000000000 : ℝ))
      (E := (cell12504 ⟨0, by decide⟩).energy) (xi := (67889242596427 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12504 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12504]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12504])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12504) (a := (5254937643483 / 6250000000000 : ℝ)) (b := (164763497157 / 100000000000000 : ℝ)) (q := (1138132088529 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12504])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12504])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12504]

theorem cert12504_1 : CellCertificate 12504 (892248566770871 / 10000000000000000 : ℝ) (419956353086159 / 250000000000000000 : ℝ) (67889242596427 / 2000000000000000 : ℝ)
    (cell12504 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · have h := gap_lower (n := 12504) (a := (42021981902949 / 50000000000000 : ℝ)) (b := (164763497157 / 100000000000000 : ℝ)) (q := (2276268193273 / 100000000000000 : ℝ))
      (E := (cell12504 ⟨1, by decide⟩).energy) (xi := (67889242596427 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12504 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12504]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12504])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12504) (a := (42021981902949 / 50000000000000 : ℝ)) (b := (164763497157 / 100000000000000 : ℝ)) (q := (2276268193273 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12504])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12504])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12504]

theorem cert12504_2 : CellCertificate 12504 (892248566770871 / 10000000000000000 : ℝ) (419956353086159 / 250000000000000000 : ℝ) (67889242596427 / 2000000000000000 : ℝ)
    (cell12504 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · have h := gap_lower (n := 12504) (a := (84008950340223 / 100000000000000 : ℝ)) (b := (164763497157 / 100000000000000 : ℝ)) (q := (2276272200791 / 100000000000000 : ℝ))
      (E := (cell12504 ⟨2, by decide⟩).energy) (xi := (67889242596427 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12504 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12504]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12504])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12504) (a := (84008950340223 / 100000000000000 : ℝ)) (b := (164763497157 / 100000000000000 : ℝ)) (q := (2276272200791 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12504])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12504])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12504]

theorem cert12504_3 : CellCertificate 12504 (892248566770871 / 10000000000000000 : ℝ) (419956353086159 / 250000000000000000 : ℝ) (67889242596427 / 2000000000000000 : ℝ)
    (cell12504 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · have h := gap_lower (n := 12504) (a := (83973961862003 / 100000000000000 : ℝ)) (b := (164763497157 / 100000000000000 : ℝ)) (q := (1138138104427 / 50000000000000 : ℝ))
      (E := (cell12504 ⟨3, by decide⟩).energy) (xi := (67889242596427 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12504 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12504]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12504])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12504) (a := (83973961862003 / 100000000000000 : ℝ)) (b := (164763497157 / 100000000000000 : ℝ)) (q := (1138138104427 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12504])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12504])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12504]

theorem cert12504_4 : CellCertificate 12504 (892248566770871 / 10000000000000000 : ℝ) (419956353086159 / 250000000000000000 : ℝ) (67889242596427 / 2000000000000000 : ℝ)
    (cell12504 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · have h := gap_lower (n := 12504) (a := (83938998334731 / 100000000000000 : ℝ)) (b := (164763497157 / 100000000000000 : ℝ)) (q := (569070042141 / 25000000000000 : ℝ))
      (E := (cell12504 ⟨4, by decide⟩).energy) (xi := (67889242596427 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12504 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12504]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12504])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12504) (a := (83938998334731 / 100000000000000 : ℝ)) (b := (164763497157 / 100000000000000 : ℝ)) (q := (569070042141 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12504])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12504])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12504]

theorem cert12504_5 : CellCertificate 12504 (892248566770871 / 10000000000000000 : ℝ) (419956353086159 / 250000000000000000 : ℝ) (67889242596427 / 2000000000000000 : ℝ)
    (cell12504 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · have h := gap_lower (n := 12504) (a := (83904059722093 / 100000000000000 : ℝ)) (b := (164763497157 / 100000000000000 : ℝ)) (q := (227628420439 / 10000000000000 : ℝ))
      (E := (cell12504 ⟨5, by decide⟩).energy) (xi := (67889242596427 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12504 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12504]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12504])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12504) (a := (83904059722093 / 100000000000000 : ℝ)) (b := (164763497157 / 100000000000000 : ℝ)) (q := (227628420439 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12504])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12504])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12504]

theorem cert12504_6 : CellCertificate 12504 (892248566770871 / 10000000000000000 : ℝ) (419956353086159 / 250000000000000000 : ℝ) (67889242596427 / 2000000000000000 : ℝ)
    (cell12504 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · have h := gap_lower (n := 12504) (a := (16773829197593 / 20000000000000 : ℝ)) (b := (164763497157 / 100000000000000 : ℝ)) (q := (1138144075539 / 50000000000000 : ℝ))
      (E := (cell12504 ⟨6, by decide⟩).energy) (xi := (67889242596427 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12504 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12504]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12504])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12504) (a := (16773829197593 / 20000000000000 : ℝ)) (b := (164763497157 / 100000000000000 : ℝ)) (q := (1138144075539 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12504])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12504])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12504]

theorem cert12504_7 : CellCertificate 12504 (892248566770871 / 10000000000000000 : ℝ) (419956353086159 / 250000000000000000 : ℝ) (67889242596427 / 2000000000000000 : ℝ)
    (cell12504 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · have h := gap_lower (n := 12504) (a := (41917128548207 / 50000000000000 : ℝ)) (b := (164763497157 / 100000000000000 : ℝ)) (q := (1138146095281 / 50000000000000 : ℝ))
      (E := (cell12504 ⟨7, by decide⟩).energy) (xi := (67889242596427 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12504 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12504]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12504])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12504) (a := (41917128548207 / 50000000000000 : ℝ)) (b := (164763497157 / 100000000000000 : ℝ)) (q := (1138146095281 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12504])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12504])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12504]

theorem cert12504_8 : CellCertificate 12504 (892248566770871 / 10000000000000000 : ℝ) (419956353086159 / 250000000000000000 : ℝ) (67889242596427 / 2000000000000000 : ℝ)
    (cell12504 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · have h := gap_lower (n := 12504) (a := (5237462063231 / 6250000000000 : ℝ)) (b := (164763497157 / 100000000000000 : ℝ)) (q := (1138148078467 / 50000000000000 : ℝ))
      (E := (cell12504 ⟨8, by decide⟩).energy) (xi := (67889242596427 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12504 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12504]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12504])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12504) (a := (5237462063231 / 6250000000000 : ℝ)) (b := (164763497157 / 100000000000000 : ℝ)) (q := (1138148078467 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12504])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12504])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12504]

theorem cert12504_9 : CellCertificate 12504 (892248566770871 / 10000000000000000 : ℝ) (419956353086159 / 250000000000000000 : ℝ) (67889242596427 / 2000000000000000 : ℝ)
    (cell12504 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · have h := gap_lower (n := 12504) (a := (41882276849127 / 50000000000000 : ℝ)) (b := (164763497157 / 100000000000000 : ℝ)) (q := (7113438043 / 312500000000 : ℝ))
      (E := (cell12504 ⟨9, by decide⟩).energy) (xi := (67889242596427 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12504 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12504]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12504])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12504) (a := (41882276849127 / 50000000000000 : ℝ)) (b := (164763497157 / 100000000000000 : ℝ)) (q := (7113438043 / 312500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12504])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12504])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12504]

theorem cert12504_10 : CellCertificate 12504 (892248566770871 / 10000000000000000 : ℝ) (419956353086159 / 250000000000000000 : ℝ) (67889242596427 / 2000000000000000 : ℝ)
    (cell12504 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · have h := gap_lower (n := 12504) (a := (41864869560359 / 50000000000000 : ℝ)) (b := (164763497157 / 100000000000000 : ℝ)) (q := (2276304190463 / 100000000000000 : ℝ))
      (E := (cell12504 ⟨10, by decide⟩).energy) (xi := (67889242596427 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12504 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12504]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12504])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12504) (a := (41864869560359 / 50000000000000 : ℝ)) (b := (164763497157 / 100000000000000 : ℝ)) (q := (2276304190463 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12504])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12504])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12504]

theorem cert12504_11 : CellCertificate 12504 (892248566770871 / 10000000000000000 : ℝ) (419956353086159 / 250000000000000000 : ℝ) (67889242596427 / 2000000000000000 : ℝ)
    (cell12504 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · have h := gap_lower (n := 12504) (a := (83694949243901 / 100000000000000 : ℝ)) (b := (164763497157 / 100000000000000 : ℝ)) (q := (18210465249 / 800000000000 : ℝ))
      (E := (cell12504 ⟨11, by decide⟩).energy) (xi := (67889242596427 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12504 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12504]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12504])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12504) (a := (83694949243901 / 100000000000000 : ℝ)) (b := (164763497157 / 100000000000000 : ℝ)) (q := (18210465249 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12504])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12504])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12504]

theorem cert12504_12 : CellCertificate 12504 (892248566770871 / 10000000000000000 : ℝ) (419956353086159 / 250000000000000000 : ℝ) (67889242596427 / 2000000000000000 : ℝ)
    (cell12504 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · have h := gap_lower (n := 12504) (a := (41830092016401 / 50000000000000 : ℝ)) (b := (164763497157 / 100000000000000 : ℝ)) (q := (2276312135623 / 100000000000000 : ℝ))
      (E := (cell12504 ⟨12, by decide⟩).energy) (xi := (67889242596427 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12504 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12504]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12504])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12504) (a := (41830092016401 / 50000000000000 : ℝ)) (b := (164763497157 / 100000000000000 : ℝ)) (q := (2276312135623 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12504])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12504])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12504]

theorem cert12504_13 : CellCertificate 12504 (892248566770871 / 10000000000000000 : ℝ) (419956353086159 / 250000000000000000 : ℝ) (67889242596427 / 2000000000000000 : ℝ)
    (cell12504 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · have h := gap_lower (n := 12504) (a := (83625443452601 / 100000000000000 : ℝ)) (b := (164763497157 / 100000000000000 : ℝ)) (q := (455263227117 / 20000000000000 : ℝ))
      (E := (cell12504 ⟨13, by decide⟩).energy) (xi := (67889242596427 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12504 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12504]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12504])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12504) (a := (83625443452601 / 100000000000000 : ℝ)) (b := (164763497157 / 100000000000000 : ℝ)) (q := (455263227117 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12504])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12504])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12504]

theorem cert12504_14 : CellCertificate 12504 (892248566770871 / 10000000000000000 : ℝ) (419956353086159 / 250000000000000000 : ℝ) (67889242596427 / 2000000000000000 : ℝ)
    (cell12504 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · have h := gap_lower (n := 12504) (a := (41795363734331 / 50000000000000 : ℝ)) (b := (164763497157 / 100000000000000 : ℝ)) (q := (2276320162391 / 100000000000000 : ℝ))
      (E := (cell12504 ⟨14, by decide⟩).energy) (xi := (67889242596427 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12504 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12504]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12504])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12504) (a := (41795363734331 / 50000000000000 : ℝ)) (b := (164763497157 / 100000000000000 : ℝ)) (q := (2276320162391 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12504])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12504])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12504]

theorem cert12504_15 : CellCertificate 12504 (892248566770871 / 10000000000000000 : ℝ) (419956353086159 / 250000000000000000 : ℝ) (67889242596427 / 2000000000000000 : ℝ)
    (cell12504 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · have h := gap_lower (n := 12504) (a := (41778018023263 / 50000000000000 : ℝ)) (b := (164763497157 / 100000000000000 : ℝ)) (q := (2276324164031 / 100000000000000 : ℝ))
      (E := (cell12504 ⟨15, by decide⟩).energy) (xi := (67889242596427 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12504 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12504]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12504])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12504) (a := (41778018023263 / 50000000000000 : ℝ)) (b := (164763497157 / 100000000000000 : ℝ)) (q := (2276324164031 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12504])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12504])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12504]

theorem cert12504_16 : CellCertificate 12504 (892248566770871 / 10000000000000000 : ℝ) (419956353086159 / 250000000000000000 : ℝ) (67889242596427 / 2000000000000000 : ℝ)
    (cell12504 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · have h := gap_lower (n := 12504) (a := (20880342287979 / 25000000000000 : ℝ)) (b := (164763497157 / 100000000000000 : ℝ)) (q := (2276328146323 / 100000000000000 : ℝ))
      (E := (cell12504 ⟨16, by decide⟩).energy) (xi := (67889242596427 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12504 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12504]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12504])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12504) (a := (20880342287979 / 25000000000000 : ℝ)) (b := (164763497157 / 100000000000000 : ℝ)) (q := (2276328146323 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12504])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12504])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12504]

theorem cert12504_17 : CellCertificate 12504 (892248566770871 / 10000000000000000 : ℝ) (419956353086159 / 250000000000000000 : ℝ) (67889242596427 / 2000000000000000 : ℝ)
    (cell12504 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · have h := gap_lower (n := 12504) (a := (8348672675073 / 10000000000000 : ℝ)) (b := (164763497157 / 100000000000000 : ℝ)) (q := (1138166086513 / 50000000000000 : ℝ))
      (E := (cell12504 ⟨17, by decide⟩).energy) (xi := (67889242596427 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12504 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12504]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12504])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12504) (a := (8348672675073 / 10000000000000 : ℝ)) (b := (164763497157 / 100000000000000 : ℝ)) (q := (1138166086513 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12504])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12504])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12504]

theorem cert12504_18 : CellCertificate 12504 (892248566770871 / 10000000000000000 : ℝ) (419956353086159 / 250000000000000000 : ℝ) (67889242596427 / 2000000000000000 : ℝ)
    (cell12504 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · have h := gap_lower (n := 12504) (a := (83452108809047 / 100000000000000 : ℝ)) (b := (164763497157 / 100000000000000 : ℝ)) (q := (2276336133113 / 100000000000000 : ℝ))
      (E := (cell12504 ⟨18, by decide⟩).energy) (xi := (67889242596427 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12504 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12504]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12504])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12504) (a := (83452108809047 / 100000000000000 : ℝ)) (b := (164763497157 / 100000000000000 : ℝ)) (q := (2276336133113 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12504])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12504])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12504]

theorem cert12504_19 : CellCertificate 12504 (892248566770871 / 10000000000000000 : ℝ) (419956353086159 / 250000000000000000 : ℝ) (67889242596427 / 2000000000000000 : ℝ)
    (cell12504 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · have h := gap_lower (n := 12504) (a := (41708757646559 / 50000000000000 : ℝ)) (b := (164763497157 / 100000000000000 : ℝ)) (q := (227634014807 / 10000000000000 : ℝ))
      (E := (cell12504 ⟨19, by decide⟩).energy) (xi := (67889242596427 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12504 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12504]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12504])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12504) (a := (41708757646559 / 50000000000000 : ℝ)) (b := (164763497157 / 100000000000000 : ℝ)) (q := (227634014807 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12504])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12504])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12504]

theorem cert12505_0 : CellCertificate 12505 (446109892299859 / 5000000000000000 : ℝ) (1679691035188747 / 1000000000000000000 : ℝ) (84854595256113 / 2500000000000000 : ℝ)
    (cell12505 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · have h := gap_lower (n := 12505) (a := (2627468334033 / 3125000000000 : ℝ)) (b := (41187538647 / 25000000000000 : ℝ)) (q := (1138066754967 / 50000000000000 : ℝ))
      (E := (cell12505 ⟨0, by decide⟩).energy) (xi := (84854595256113 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12505 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12505]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12505])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12505) (a := (2627468334033 / 3125000000000 : ℝ)) (b := (41187538647 / 25000000000000 : ℝ)) (q := (1138066754967 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12505])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12505])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12505]

theorem cert12505_1 : CellCertificate 12505 (446109892299859 / 5000000000000000 : ℝ) (1679691035188747 / 1000000000000000000 : ℝ) (84854595256113 / 2500000000000000 : ℝ)
    (cell12505 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · have h := gap_lower (n := 12505) (a := (4202197426353 / 5000000000000 : ℝ)) (b := (41187538647 / 25000000000000 : ℝ)) (q := (2276137480537 / 100000000000000 : ℝ))
      (E := (cell12505 ⟨1, by decide⟩).energy) (xi := (84854595256113 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12505 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12505]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12505])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12505) (a := (4202197426353 / 5000000000000 : ℝ)) (b := (41187538647 / 25000000000000 : ℝ)) (q := (2276137480537 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12505])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12505])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12505]

theorem cert12505_2 : CellCertificate 12505 (446109892299859 / 5000000000000000 : ℝ) (1679691035188747 / 1000000000000000000 : ℝ) (84854595256113 / 2500000000000000 : ℝ)
    (cell12505 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · have h := gap_lower (n := 12505) (a := (21002233847189 / 25000000000000 : ℝ)) (b := (41187538647 / 25000000000000 : ℝ)) (q := (2276141501017 / 100000000000000 : ℝ))
      (E := (cell12505 ⟨2, by decide⟩).energy) (xi := (84854595256113 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12505 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12505]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12505])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12505) (a := (21002233847189 / 25000000000000 : ℝ)) (b := (41187538647 / 25000000000000 : ℝ)) (q := (2276141501017 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12505])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12505])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12505]

theorem cert12505_3 : CellCertificate 12505 (446109892299859 / 5000000000000000 : ℝ) (1679691035188747 / 1000000000000000000 : ℝ) (84854595256113 / 2500000000000000 : ℝ)
    (cell12505 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · have h := gap_lower (n := 12505) (a := (83973947237443 / 100000000000000 : ℝ)) (b := (41187538647 / 25000000000000 : ℝ)) (q := (284518183121 / 12500000000000 : ℝ))
      (E := (cell12505 ⟨3, by decide⟩).energy) (xi := (84854595256113 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12505 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12505]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12505])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12505) (a := (83973947237443 / 100000000000000 : ℝ)) (b := (41187538647 / 25000000000000 : ℝ)) (q := (284518183121 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12505])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12505])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12505]

theorem cert12505_4 : CellCertificate 12505 (446109892299859 / 5000000000000000 : ℝ) (1679691035188747 / 1000000000000000000 : ℝ) (84854595256113 / 2500000000000000 : ℝ)
    (cell12505 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · have h := gap_lower (n := 12505) (a := (10492373004577 / 12500000000000 : ℝ)) (b := (41187538647 / 25000000000000 : ℝ)) (q := (2276149497071 / 100000000000000 : ℝ))
      (E := (cell12505 ⟨4, by decide⟩).energy) (xi := (84854595256113 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12505 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12505]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12505])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12505) (a := (10492373004577 / 12500000000000 : ℝ)) (b := (41187538647 / 25000000000000 : ℝ)) (q := (2276149497071 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12505])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12505])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12505]

theorem cert12505_5 : CellCertificate 12505 (446109892299859 / 5000000000000000 : ℝ) (1679691035188747 / 1000000000000000000 : ℝ) (84854595256113 / 2500000000000000 : ℝ)
    (cell12505 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · have h := gap_lower (n := 12505) (a := (2097601143749 / 2500000000000 : ℝ)) (b := (41187538647 / 25000000000000 : ℝ)) (q := (1138076745153 / 50000000000000 : ℝ))
      (E := (cell12505 ⟨5, by decide⟩).energy) (xi := (84854595256113 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12505 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12505]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12505])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12505) (a := (2097601143749 / 2500000000000 : ℝ)) (b := (41187538647 / 25000000000000 : ℝ)) (q := (1138076745153 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12505])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12505])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12505]

theorem cert12505_6 : CellCertificate 12505 (446109892299859 / 5000000000000000 : ℝ) (1679691035188747 / 1000000000000000000 : ℝ) (84854595256113 / 2500000000000000 : ℝ)
    (cell12505 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · have h := gap_lower (n := 12505) (a := (16773826468271 / 20000000000000 : ℝ)) (b := (41187538647 / 25000000000000 : ℝ)) (q := (569039363267 / 25000000000000 : ℝ))
      (E := (cell12505 ⟨6, by decide⟩).energy) (xi := (84854595256113 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12505 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12505]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12505])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12505) (a := (16773826468271 / 20000000000000 : ℝ)) (b := (41187538647 / 25000000000000 : ℝ)) (q := (569039363267 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12505])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12505])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12505]

theorem cert12505_7 : CellCertificate 12505 (446109892299859 / 5000000000000000 : ℝ) (1679691035188747 / 1000000000000000000 : ℝ) (84854595256113 / 2500000000000000 : ℝ)
    (cell12505 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · have h := gap_lower (n := 12505) (a := (20958560943717 / 25000000000000 : ℝ)) (b := (41187538647 / 25000000000000 : ℝ)) (q := (2276161451453 / 100000000000000 : ℝ))
      (E := (cell12505 ⟨7, by decide⟩).energy) (xi := (84854595256113 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12505 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12505]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12505])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12505) (a := (20958560943717 / 25000000000000 : ℝ)) (b := (41187538647 / 25000000000000 : ℝ)) (q := (2276161451453 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12505])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12505])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12505]

theorem cert12505_8 : CellCertificate 12505 (446109892299859 / 5000000000000000 : ℝ) (1679691035188747 / 1000000000000000000 : ℝ) (84854595256113 / 2500000000000000 : ℝ)
    (cell12505 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · have h := gap_lower (n := 12505) (a := (16759876002951 / 20000000000000 : ℝ)) (b := (41187538647 / 25000000000000 : ℝ)) (q := (2276165435437 / 100000000000000 : ℝ))
      (E := (cell12505 ⟨8, by decide⟩).energy) (xi := (84854595256113 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12505 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12505]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12505])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12505) (a := (16759876002951 / 20000000000000 : ℝ)) (b := (41187538647 / 25000000000000 : ℝ)) (q := (2276165435437 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12505])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12505])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12505]

theorem cert12505_9 : CellCertificate 12505 (446109892299859 / 5000000000000000 : ℝ) (1679691035188747 / 1000000000000000000 : ℝ) (84854595256113 / 2500000000000000 : ℝ)
    (cell12505 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · have h := gap_lower (n := 12505) (a := (4188227051273 / 5000000000000 : ℝ)) (b := (41187538647 / 25000000000000 : ℝ)) (q := (455233894131 / 20000000000000 : ℝ))
      (E := (cell12505 ⟨9, by decide⟩).energy) (xi := (84854595256113 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12505 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12505]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12505])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12505) (a := (4188227051273 / 5000000000000 : ℝ)) (b := (41187538647 / 25000000000000 : ℝ)) (q := (455233894131 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12505])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12505])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12505]

theorem cert12505_10 : CellCertificate 12505 (446109892299859 / 5000000000000000 : ℝ) (1679691035188747 / 1000000000000000000 : ℝ) (84854595256113 / 2500000000000000 : ℝ)
    (cell12505 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · have h := gap_lower (n := 12505) (a := (16745945354323 / 20000000000000 : ℝ)) (b := (41187538647 / 25000000000000 : ℝ)) (q := (284521681063 / 12500000000000 : ℝ))
      (E := (cell12505 ⟨10, by decide⟩).energy) (xi := (84854595256113 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12505 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12505]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12505])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12505) (a := (16745945354323 / 20000000000000 : ℝ)) (b := (41187538647 / 25000000000000 : ℝ)) (q := (284521681063 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12505])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12505])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12505]

theorem cert12505_11 : CellCertificate 12505 (446109892299859 / 5000000000000000 : ℝ) (1679691035188747 / 1000000000000000000 : ℝ) (84854595256113 / 2500000000000000 : ℝ)
    (cell12505 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · have h := gap_lower (n := 12505) (a := (83694937218033 / 100000000000000 : ℝ)) (b := (41187538647 / 25000000000000 : ℝ)) (q := (227617743409 / 10000000000000 : ℝ))
      (E := (cell12505 ⟨11, by decide⟩).energy) (xi := (84854595256113 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12505 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12505]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12505])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12505) (a := (83694937218033 / 100000000000000 : ℝ)) (b := (41187538647 / 25000000000000 : ℝ)) (q := (227617743409 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12505])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12505])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12505]

theorem cert12505_12 : CellCertificate 12505 (446109892299859 / 5000000000000000 : ℝ) (1679691035188747 / 1000000000000000000 : ℝ) (84854595256113 / 2500000000000000 : ℝ)
    (cell12505 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · have h := gap_lower (n := 12505) (a := (16732034465943 / 20000000000000 : ℝ)) (b := (41187538647 / 25000000000000 : ℝ)) (q := (2276181434287 / 100000000000000 : ℝ))
      (E := (cell12505 ⟨12, by decide⟩).energy) (xi := (84854595256113 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12505 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12505]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12505])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12505) (a := (16732034465943 / 20000000000000 : ℝ)) (b := (41187538647 / 25000000000000 : ℝ)) (q := (2276181434287 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12505])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12505])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12505]

theorem cert12505_13 : CellCertificate 12505 (446109892299859 / 5000000000000000 : ℝ) (1679691035188747 / 1000000000000000000 : ℝ) (84854595256113 / 2500000000000000 : ℝ)
    (cell12505 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · have h := gap_lower (n := 12505) (a := (41812716035921 / 50000000000000 : ℝ)) (b := (41187538647 / 25000000000000 : ℝ)) (q := (91047418229 / 4000000000000 : ℝ))
      (E := (cell12505 ⟨13, by decide⟩).energy) (xi := (84854595256113 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12505 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12505]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12505])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12505) (a := (41812716035921 / 50000000000000 : ℝ)) (b := (41187538647 / 25000000000000 : ℝ)) (q := (91047418229 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12505])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12505])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12505]

theorem cert12505_14 : CellCertificate 12505 (446109892299859 / 5000000000000000 : ℝ) (1679691035188747 / 1000000000000000000 : ℝ) (84854595256113 / 2500000000000000 : ℝ)
    (cell12505 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · have h := gap_lower (n := 12505) (a := (41795358204889 / 50000000000000 : ℝ)) (b := (41187538647 / 25000000000000 : ℝ)) (q := (1138094723331 / 50000000000000 : ℝ))
      (E := (cell12505 ⟨14, by decide⟩).energy) (xi := (84854595256113 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12505 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12505]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12505])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12505) (a := (41795358204889 / 50000000000000 : ℝ)) (b := (41187538647 / 25000000000000 : ℝ)) (q := (1138094723331 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12505])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12505])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12505]

theorem cert12505_15 : CellCertificate 12505 (446109892299859 / 5000000000000000 : ℝ) (1679691035188747 / 1000000000000000000 : ℝ) (84854595256113 / 2500000000000000 : ℝ)
    (cell12505 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · have h := gap_lower (n := 12505) (a := (16711205061813 / 20000000000000 : ℝ)) (b := (41187538647 / 25000000000000 : ℝ)) (q := (1138096706581 / 50000000000000 : ℝ))
      (E := (cell12505 ⟨15, by decide⟩).energy) (xi := (84854595256113 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12505 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12505]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12505])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12505) (a := (16711205061813 / 20000000000000 : ℝ)) (b := (41187538647 / 25000000000000 : ℝ)) (q := (1138096706581 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12505])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12505])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12505]

theorem cert12505_16 : CellCertificate 12505 (446109892299859 / 5000000000000000 : ℝ) (1679691035188747 / 1000000000000000000 : ℝ) (84854595256113 / 2500000000000000 : ℝ)
    (cell12505 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · have h := gap_lower (n := 12505) (a := (83521358735427 / 100000000000000 : ℝ)) (b := (41187538647 / 25000000000000 : ℝ)) (q := (569049354801 / 25000000000000 : ℝ))
      (E := (cell12505 ⟨16, by decide⟩).energy) (xi := (84854595256113 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12505 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12505]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12505])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12505) (a := (83521358735427 / 100000000000000 : ℝ)) (b := (41187538647 / 25000000000000 : ℝ)) (q := (569049354801 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12505])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12505])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12505]

theorem cert12505_17 : CellCertificate 12505 (446109892299859 / 5000000000000000 : ℝ) (1679691035188747 / 1000000000000000000 : ℝ) (84854595256113 / 2500000000000000 : ℝ)
    (cell12505 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · have h := gap_lower (n := 12505) (a := (16697343330953 / 20000000000000 : ℝ)) (b := (41187538647 / 25000000000000 : ℝ)) (q := (2276201412239 / 100000000000000 : ℝ))
      (E := (cell12505 ⟨17, by decide⟩).energy) (xi := (84854595256113 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12505 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12505]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12505])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12505) (a := (16697343330953 / 20000000000000 : ℝ)) (b := (41187538647 / 25000000000000 : ℝ)) (q := (2276201412239 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12505])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12505])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12505]

theorem cert12505_18 : CellCertificate 12505 (446109892299859 / 5000000000000000 : ℝ) (1679691035188747 / 1000000000000000000 : ℝ) (84854595256113 / 2500000000000000 : ℝ)
    (cell12505 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · have h := gap_lower (n := 12505) (a := (16690419806631 / 20000000000000 : ℝ)) (b := (41187538647 / 25000000000000 : ℝ)) (q := (2276205455807 / 100000000000000 : ℝ))
      (E := (cell12505 ⟨18, by decide⟩).energy) (xi := (84854595256113 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12505 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12505]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12505])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12505) (a := (16690419806631 / 20000000000000 : ℝ)) (b := (41187538647 / 25000000000000 : ℝ)) (q := (2276205455807 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12505])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12505])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12505]

theorem cert12505_19 : CellCertificate 12505 (446109892299859 / 5000000000000000 : ℝ) (1679691035188747 / 1000000000000000000 : ℝ) (84854595256113 / 2500000000000000 : ℝ)
    (cell12505 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · have h := gap_lower (n := 12505) (a := (20854376459213 / 25000000000000 : ℝ)) (b := (41187538647 / 25000000000000 : ℝ)) (q := (2276209438591 / 100000000000000 : ℝ))
      (E := (cell12505 ⟨19, by decide⟩).energy) (xi := (84854595256113 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12505 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12505]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12505])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12505) (a := (20854376459213 / 25000000000000 : ℝ)) (b := (41187538647 / 25000000000000 : ℝ)) (q := (2276209438591 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12505])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12505])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12505]

theorem cert12506_0 : CellCertificate 12506 (892191006854923 / 10000000000000000 : ℝ) (839778339765031 / 500000000000000000 : ℝ) (339390553713929 / 10000000000000000 : ℝ)
    (cell12506 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · have h := gap_lower (n := 12506) (a := (42039485542441 / 50000000000000 : ℝ)) (b := (823684071 / 500000000000 : ℝ)) (q := (569000709459 / 25000000000000 : ℝ))
      (E := (cell12506 ⟨0, by decide⟩).energy) (xi := (339390553713929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12506 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12506]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12506])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12506) (a := (42039485542441 / 50000000000000 : ℝ)) (b := (823684071 / 500000000000 : ℝ)) (q := (569000709459 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12506])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12506])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12506]

theorem cert12506_1 : CellCertificate 12506 (892191006854923 / 10000000000000000 : ℝ) (839778339765031 / 500000000000000000 : ℝ) (339390553713929 / 10000000000000000 : ℝ)
    (cell12506 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · have h := gap_lower (n := 12506) (a := (42021966625341 / 50000000000000 : ℝ)) (b := (823684071 / 500000000000 : ℝ)) (q := (2276006820679 / 100000000000000 : ℝ))
      (E := (cell12506 ⟨1, by decide⟩).energy) (xi := (339390553713929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12506 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12506]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12506])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12506) (a := (42021966625341 / 50000000000000 : ℝ)) (b := (823684071 / 500000000000 : ℝ)) (q := (2276006820679 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12506])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12506])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12506]

theorem cert12506_2 : CellCertificate 12506 (892191006854923 / 10000000000000000 : ℝ) (839778339765031 / 500000000000000000 : ℝ) (339390553713929 / 10000000000000000 : ℝ)
    (cell12506 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · have h := gap_lower (n := 12506) (a := (84008920439707 / 100000000000000 : ℝ)) (b := (823684071 / 500000000000 : ℝ)) (q := (35562668693 / 1562500000000 : ℝ))
      (E := (cell12506 ⟨2, by decide⟩).energy) (xi := (339390553713929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12506 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12506]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12506])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12506) (a := (84008920439707 / 100000000000000 : ℝ)) (b := (823684071 / 500000000000 : ℝ)) (q := (35562668693 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12506])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12506])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12506]

theorem cert12506_3 : CellCertificate 12506 (892191006854923 / 10000000000000000 : ℝ) (839778339765031 / 500000000000000000 : ℝ) (339390553713929 / 10000000000000000 : ℝ)
    (cell12506 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · have h := gap_lower (n := 12506) (a := (83973932615261 / 100000000000000 : ℝ)) (b := (823684071 / 500000000000 : ℝ)) (q := (2276014831953 / 100000000000000 : ℝ))
      (E := (cell12506 ⟨3, by decide⟩).energy) (xi := (339390553713929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12506 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12506]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12506])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12506) (a := (83973932615261 / 100000000000000 : ℝ)) (b := (823684071 / 500000000000 : ℝ)) (q := (2276014831953 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12506])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12506])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12506]

theorem cert12506_4 : CellCertificate 12506 (892191006854923 / 10000000000000000 : ℝ) (839778339765031 / 500000000000000000 : ℝ) (339390553713929 / 10000000000000000 : ℝ)
    (cell12506 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · have h := gap_lower (n := 12506) (a := (41969484870419 / 50000000000000 : ℝ)) (b := (823684071 / 500000000000 : ℝ)) (q := (2276018820769 / 100000000000000 : ℝ))
      (E := (cell12506 ⟨4, by decide⟩).energy) (xi := (339390553713929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12506 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12506]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12506])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12506) (a := (41969484870419 / 50000000000000 : ℝ)) (b := (823684071 / 500000000000 : ℝ)) (q := (2276018820769 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12506])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12506])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12506]

theorem cert12506_5 : CellCertificate 12506 (892191006854923 / 10000000000000000 : ℝ) (839778339765031 / 500000000000000000 : ℝ) (339390553713929 / 10000000000000000 : ℝ)
    (cell12506 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · have h := gap_lower (n := 12506) (a := (671232254241 / 800000000000 : ℝ)) (b := (823684071 / 500000000000 : ℝ)) (q := (1138011385727 / 50000000000000 : ℝ))
      (E := (cell12506 ⟨5, by decide⟩).energy) (xi := (339390553713929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12506 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12506]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12506])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12506) (a := (671232254241 / 800000000000 : ℝ)) (b := (823684071 / 500000000000 : ℝ)) (q := (1138011385727 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12506])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12506])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12506]

theorem cert12506_6 : CellCertificate 12506 (892191006854923 / 10000000000000000 : ℝ) (839778339765031 / 500000000000000000 : ℝ) (339390553713929 / 10000000000000000 : ℝ)
    (cell12506 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · have h := gap_lower (n := 12506) (a := (41934559348501 / 50000000000000 : ℝ)) (b := (823684071 / 500000000000 : ℝ)) (q := (2276026808263 / 100000000000000 : ℝ))
      (E := (cell12506 ⟨6, by decide⟩).energy) (xi := (339390553713929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12506 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12506]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12506])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12506) (a := (41934559348501 / 50000000000000 : ℝ)) (b := (823684071 / 500000000000 : ℝ)) (q := (2276026808263 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12506])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12506])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12506]

theorem cert12506_7 : CellCertificate 12506 (892191006854923 / 10000000000000000 : ℝ) (839778339765031 / 500000000000000000 : ℝ) (339390553713929 / 10000000000000000 : ℝ)
    (cell12506 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · have h := gap_lower (n := 12506) (a := (41917115227769 / 50000000000000 : ℝ)) (b := (823684071 / 500000000000 : ℝ)) (q := (1138015382807 / 50000000000000 : ℝ))
      (E := (cell12506 ⟨7, by decide⟩).energy) (xi := (339390553713929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12506 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12506]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12506])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12506) (a := (41917115227769 / 50000000000000 : ℝ)) (b := (823684071 / 500000000000 : ℝ)) (q := (1138015382807 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12506])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12506])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12506]

theorem cert12506_8 : CellCertificate 12506 (892191006854923 / 10000000000000000 : ℝ) (839778339765031 / 500000000000000000 : ℝ) (339390553713929 / 10000000000000000 : ℝ)
    (cell12506 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · have h := gap_lower (n := 12506) (a := (8379936701999 / 10000000000000 : ℝ)) (b := (823684071 / 500000000000 : ℝ)) (q := (91041390691 / 4000000000000 : ℝ))
      (E := (cell12506 ⟨8, by decide⟩).energy) (xi := (339390553713929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12506 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12506]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12506])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12506) (a := (8379936701999 / 10000000000000 : ℝ)) (b := (823684071 / 500000000000 : ℝ)) (q := (91041390691 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12506])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12506])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12506]

theorem cert12506_9 : CellCertificate 12506 (892191006854923 / 10000000000000000 : ℝ) (839778339765031 / 500000000000000000 : ℝ) (339390553713929 / 10000000000000000 : ℝ)
    (cell12506 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · have h := gap_lower (n := 12506) (a := (83764528354803 / 100000000000000 : ℝ)) (b := (823684071 / 500000000000 : ℝ)) (q := (2276038762947 / 100000000000000 : ℝ))
      (E := (cell12506 ⟨9, by decide⟩).energy) (xi := (339390553713929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12506 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12506]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12506])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12506) (a := (83764528354803 / 100000000000000 : ℝ)) (b := (823684071 / 500000000000 : ℝ)) (q := (2276038762947 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12506])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12506])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12506]

theorem cert12506_10 : CellCertificate 12506 (892191006854923 / 10000000000000000 : ℝ) (839778339765031 / 500000000000000000 : ℝ) (339390553713929 / 10000000000000000 : ℝ)
    (cell12506 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · have h := gap_lower (n := 12506) (a := (83729714424609 / 100000000000000 : ℝ)) (b := (823684071 / 500000000000 : ℝ)) (q := (2276042760007 / 100000000000000 : ℝ))
      (E := (cell12506 ⟨10, by decide⟩).energy) (xi := (339390553713929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12506 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12506]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12506])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12506) (a := (83729714424609 / 100000000000000 : ℝ)) (b := (823684071 / 500000000000 : ℝ)) (q := (2276042760007 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12506])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12506])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12506]

theorem cert12506_11 : CellCertificate 12506 (892191006854923 / 10000000000000000 : ℝ) (839778339765031 / 500000000000000000 : ℝ) (339390553713929 / 10000000000000000 : ℝ)
    (cell12506 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · have h := gap_lower (n := 12506) (a := (83694925194223 / 100000000000000 : ℝ)) (b := (823684071 / 500000000000 : ℝ)) (q := (113802338279 / 5000000000000 : ℝ))
      (E := (cell12506 ⟨11, by decide⟩).energy) (xi := (339390553713929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12506 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12506]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12506])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12506) (a := (83694925194223 / 100000000000000 : ℝ)) (b := (823684071 / 500000000000 : ℝ)) (q := (113802338279 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12506])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12506])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12506]

theorem cert12506_12 : CellCertificate 12506 (892191006854923 / 10000000000000000 : ℝ) (839778339765031 / 500000000000000000 : ℝ) (339390553713929 / 10000000000000000 : ℝ)
    (cell12506 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · have h := gap_lower (n := 12506) (a := (41830080314323 / 50000000000000 : ℝ)) (b := (823684071 / 500000000000 : ℝ)) (q := (2276050786543 / 100000000000000 : ℝ))
      (E := (cell12506 ⟨12, by decide⟩).energy) (xi := (339390553713929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12506 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12506]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12506])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12506) (a := (41830080314323 / 50000000000000 : ℝ)) (b := (823684071 / 500000000000 : ℝ)) (q := (2276050786543 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12506])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12506])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12506]

theorem cert12506_13 : CellCertificate 12506 (892191006854923 / 10000000000000000 : ℝ) (839778339765031 / 500000000000000000 : ℝ) (339390553713929 / 10000000000000000 : ℝ)
    (cell12506 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · have h := gap_lower (n := 12506) (a := (83625420693061 / 100000000000000 : ℝ)) (b := (823684071 / 500000000000 : ℝ)) (q := (91042190857 / 4000000000000 : ℝ))
      (E := (cell12506 ⟨13, by decide⟩).energy) (xi := (339390553713929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12506 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12506]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12506])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12506) (a := (83625420693061 / 100000000000000 : ℝ)) (b := (823684071 / 500000000000 : ℝ)) (q := (91042190857 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12506])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12506])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12506]

theorem cert12506_14 : CellCertificate 12506 (892191006854923 / 10000000000000000 : ℝ) (839778339765031 / 500000000000000000 : ℝ) (339390553713929 / 10000000000000000 : ℝ)
    (cell12506 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · have h := gap_lower (n := 12506) (a := (83590705352831 / 100000000000000 : ℝ)) (b := (823684071 / 500000000000 : ℝ)) (q := (455211756931 / 20000000000000 : ℝ))
      (E := (cell12506 ⟨14, by decide⟩).energy) (xi := (339390553713929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12506 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12506]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12506])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12506) (a := (83590705352831 / 100000000000000 : ℝ)) (b := (823684071 / 500000000000 : ℝ)) (q := (455211756931 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12506])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12506])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12506]

theorem cert12506_15 : CellCertificate 12506 (892191006854923 / 10000000000000000 : ℝ) (839778339765031 / 500000000000000000 : ℝ) (339390553713929 / 10000000000000000 : ℝ)
    (cell12506 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · have h := gap_lower (n := 12506) (a := (41778007286751 / 50000000000000 : ℝ)) (b := (823684071 / 500000000000 : ℝ)) (q := (2276062774219 / 100000000000000 : ℝ))
      (E := (cell12506 ⟨15, by decide⟩).energy) (xi := (339390553713929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12506 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12506]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12506])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12506) (a := (41778007286751 / 50000000000000 : ℝ)) (b := (823684071 / 500000000000 : ℝ)) (q := (2276062774219 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12506])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12506])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12506]

theorem cert12506_16 : CellCertificate 12506 (892191006854923 / 10000000000000000 : ℝ) (839778339765031 / 500000000000000000 : ℝ) (339390553713929 / 10000000000000000 : ℝ)
    (cell12506 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · have h := gap_lower (n := 12506) (a := (83521348320797 / 100000000000000 : ℝ)) (b := (823684071 / 500000000000 : ℝ)) (q := (569016686483 / 25000000000000 : ℝ))
      (E := (cell12506 ⟨16, by decide⟩).energy) (xi := (339390553713929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12506 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12506]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12506])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12506) (a := (83521348320797 / 100000000000000 : ℝ)) (b := (823684071 / 500000000000 : ℝ)) (q := (569016686483 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12506])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12506])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12506]

theorem cert12506_17 : CellCertificate 12506 (892191006854923 / 10000000000000000 : ℝ) (839778339765031 / 500000000000000000 : ℝ) (339390553713929 / 10000000000000000 : ℝ)
    (cell12506 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · have h := gap_lower (n := 12506) (a := (83486706560617 / 100000000000000 : ℝ)) (b := (823684071 / 500000000000 : ℝ)) (q := (1138035381777 / 50000000000000 : ℝ))
      (E := (cell12506 ⟨17, by decide⟩).energy) (xi := (339390553713929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12506 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12506]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12506])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12506) (a := (83486706560617 / 100000000000000 : ℝ)) (b := (823684071 / 500000000000 : ℝ)) (q := (1138035381777 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12506])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12506])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12506]

theorem cert12506_18 : CellCertificate 12506 (892191006854923 / 10000000000000000 : ℝ) (839778339765031 / 500000000000000000 : ℝ) (339390553713929 / 10000000000000000 : ℝ)
    (cell12506 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · have h := gap_lower (n := 12506) (a := (41726044629521 / 50000000000000 : ℝ)) (b := (823684071 / 500000000000 : ℝ)) (q := (1138037387133 / 50000000000000 : ℝ))
      (E := (cell12506 ⟨18, by decide⟩).energy) (xi := (339390553713929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12506 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12506]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12506])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12506) (a := (41726044629521 / 50000000000000 : ℝ)) (b := (823684071 / 500000000000 : ℝ)) (q := (1138037387133 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12506])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12506])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12506]

theorem cert12506_19 : CellCertificate 12506 (892191006854923 / 10000000000000000 : ℝ) (839778339765031 / 500000000000000000 : ℝ) (339390553713929 / 10000000000000000 : ℝ)
    (cell12506 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · have h := gap_lower (n := 12506) (a := (3336699855293 / 4000000000000 : ℝ)) (b := (823684071 / 500000000000 : ℝ)) (q := (1138039391577 / 50000000000000 : ℝ))
      (E := (cell12506 ⟨19, by decide⟩).energy) (xi := (339390553713929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12506 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12506]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12506])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12506) (a := (3336699855293 / 4000000000000 : ℝ)) (b := (823684071 / 500000000000 : ℝ)) (q := (1138039391577 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12506])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12506])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12506]

theorem cert12507_0 : CellCertificate 12507 (446081116767709 / 5000000000000000 : ℝ) (1679422345363421 / 1000000000000000000 : ℝ) (339362731049279 / 10000000000000000 : ℝ)
    (cell12507 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · have h := gap_lower (n := 12507) (a := (84078955483207 / 100000000000000 : ℝ)) (b := (20590434499 / 12500000000000 : ℝ)) (q := (455174443711 / 20000000000000 : ℝ))
      (E := (cell12507 ⟨0, by decide⟩).energy) (xi := (339362731049279 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12507 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12507]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12507])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12507) (a := (84078955483207 / 100000000000000 : ℝ)) (b := (20590434499 / 12500000000000 : ℝ)) (q := (455174443711 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12507])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12507])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12507]

theorem cert12507_1 : CellCertificate 12507 (446081116767709 / 5000000000000000 : ℝ) (1679422345363421 / 1000000000000000000 : ℝ) (339362731049279 / 10000000000000000 : ℝ)
    (cell12507 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · have h := gap_lower (n := 12507) (a := (84043917976761 / 100000000000000 : ℝ)) (b := (20590434499 / 12500000000000 : ℝ)) (q := (455175242741 / 20000000000000 : ℝ))
      (E := (cell12507 ⟨1, by decide⟩).energy) (xi := (339362731049279 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12507 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12507]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12507])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12507) (a := (84043917976761 / 100000000000000 : ℝ)) (b := (20590434499 / 12500000000000 : ℝ)) (q := (455175242741 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12507])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12507])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12507]

theorem cert12507_2 : CellCertificate 12507 (446081116767709 / 5000000000000000 : ℝ) (1679422345363421 / 1000000000000000000 : ℝ) (339362731049279 / 10000000000000000 : ℝ)
    (cell12507 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · have h := gap_lower (n := 12507) (a := (21002226373269 / 25000000000000 : ℝ)) (b := (20590434499 / 12500000000000 : ℝ)) (q := (227588020247 / 10000000000000 : ℝ))
      (E := (cell12507 ⟨2, by decide⟩).energy) (xi := (339362731049279 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12507 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12507]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12507])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12507) (a := (21002226373269 / 25000000000000 : ℝ)) (b := (20590434499 / 12500000000000 : ℝ)) (q := (227588020247 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12507])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12507])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12507]

theorem cert12507_3 : CellCertificate 12507 (446081116767709 / 5000000000000000 : ℝ) (1679422345363421 / 1000000000000000000 : ℝ) (339362731049279 / 10000000000000000 : ℝ)
    (cell12507 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · have h := gap_lower (n := 12507) (a := (1312092468679 / 1562500000000 : ℝ)) (b := (20590434499 / 12500000000000 : ℝ)) (q := (227588419409 / 10000000000000 : ℝ))
      (E := (cell12507 ⟨3, by decide⟩).energy) (xi := (339362731049279 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12507 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12507]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12507])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12507) (a := (1312092468679 / 1562500000000 : ℝ)) (b := (20590434499 / 12500000000000 : ℝ)) (q := (227588419409 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12507])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12507])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12507]

theorem cert12507_4 : CellCertificate 12507 (446081116767709 / 5000000000000000 : ℝ) (1679422345363421 / 1000000000000000000 : ℝ) (339362731049279 / 10000000000000000 : ℝ)
    (cell12507 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · have h := gap_lower (n := 12507) (a := (20984738861849 / 25000000000000 : ℝ)) (b := (20590434499 / 12500000000000 : ℝ)) (q := (1137944098773 / 50000000000000 : ℝ))
      (E := (cell12507 ⟨4, by decide⟩).energy) (xi := (339362731049279 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12507 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12507]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12507])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12507) (a := (20984738861849 / 25000000000000 : ℝ)) (b := (20590434499 / 12500000000000 : ℝ)) (q := (1137944098773 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12507])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12507])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12507]

theorem cert12507_5 : CellCertificate 12507 (446081116767709 / 5000000000000000 : ℝ) (1679422345363421 / 1000000000000000000 : ℝ) (339362731049279 / 10000000000000000 : ℝ)
    (cell12507 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · have h := gap_lower (n := 12507) (a := (83904017812587 / 100000000000000 : ℝ)) (b := (20590434499 / 12500000000000 : ℝ)) (q := (2275892163651 / 100000000000000 : ℝ))
      (E := (cell12507 ⟨5, by decide⟩).energy) (xi := (339362731049279 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12507 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12507]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12507])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12507) (a := (83904017812587 / 100000000000000 : ℝ)) (b := (20590434499 / 12500000000000 : ℝ)) (q := (2275892163651 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12507])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12507])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12507]

theorem cert12507_6 : CellCertificate 12507 (446081116767709 / 5000000000000000 : ℝ) (1679422345363421 / 1000000000000000000 : ℝ) (339362731049279 / 10000000000000000 : ℝ)
    (cell12507 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · have h := gap_lower (n := 12507) (a := (41934552527453 / 50000000000000 : ℝ)) (b := (20590434499 / 12500000000000 : ℝ)) (q := (2275896158733 / 100000000000000 : ℝ))
      (E := (cell12507 ⟨6, by decide⟩).energy) (xi := (339362731049279 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12507 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12507]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12507])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12507) (a := (41934552527453 / 50000000000000 : ℝ)) (b := (20590434499 / 12500000000000 : ℝ)) (q := (2275896158733 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12507])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12507])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12507]

theorem cert12507_7 : CellCertificate 12507 (446081116767709 / 5000000000000000 : ℝ) (1679422345363421 / 1000000000000000000 : ℝ) (339362731049279 / 10000000000000000 : ℝ)
    (cell12507 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · have h := gap_lower (n := 12507) (a := (3353368685537 / 4000000000000 : ℝ)) (b := (20590434499 / 12500000000000 : ℝ)) (q := (2275900190999 / 100000000000000 : ℝ))
      (E := (cell12507 ⟨7, by decide⟩).energy) (xi := (339362731049279 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12507 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12507]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12507])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12507) (a := (3353368685537 / 4000000000000 : ℝ)) (b := (20590434499 / 12500000000000 : ℝ)) (q := (2275900190999 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12507])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12507])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12507]

theorem cert12507_8 : CellCertificate 12507 (446081116767709 / 5000000000000000 : ℝ) (1679422345363421 / 1000000000000000000 : ℝ) (339362731049279 / 10000000000000000 : ℝ)
    (cell12507 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · have h := gap_lower (n := 12507) (a := (41899677013701 / 50000000000000 : ℝ)) (b := (20590434499 / 12500000000000 : ℝ)) (q := (17780501191 / 781250000000 : ℝ))
      (E := (cell12507 ⟨8, by decide⟩).energy) (xi := (339362731049279 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12507 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12507]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12507])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12507) (a := (41899677013701 / 50000000000000 : ℝ)) (b := (20590434499 / 12500000000000 : ℝ)) (q := (17780501191 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12507])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12507])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12507]

theorem cert12507_9 : CellCertificate 12507 (446081116767709 / 5000000000000000 : ℝ) (1679422345363421 / 1000000000000000000 : ℝ) (339362731049279 / 10000000000000000 : ℝ)
    (cell12507 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · have h := gap_lower (n := 12507) (a := (41882257843141 / 50000000000000 : ℝ)) (b := (20590434499 / 12500000000000 : ℝ)) (q := (2275908166641 / 100000000000000 : ℝ))
      (E := (cell12507 ⟨9, by decide⟩).energy) (xi := (339362731049279 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12507 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12507]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12507])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12507) (a := (41882257843141 / 50000000000000 : ℝ)) (b := (20590434499 / 12500000000000 : ℝ)) (q := (2275908166641 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12507])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12507])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12507]

theorem cert12507_10 : CellCertificate 12507 (446081116767709 / 5000000000000000 : ℝ) (1679422345363421 / 1000000000000000000 : ℝ) (339362731049279 / 10000000000000000 : ℝ)
    (cell12507 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · have h := gap_lower (n := 12507) (a := (83729702079699 / 100000000000000 : ℝ)) (b := (20590434499 / 12500000000000 : ℝ)) (q := (2275912182999 / 100000000000000 : ℝ))
      (E := (cell12507 ⟨10, by decide⟩).energy) (xi := (339362731049279 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12507 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12507]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12507])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12507) (a := (83729702079699 / 100000000000000 : ℝ)) (b := (20590434499 / 12500000000000 : ℝ)) (q := (2275912182999 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12507])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12507])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12507]

theorem cert12507_11 : CellCertificate 12507 (446081116767709 / 5000000000000000 : ℝ) (1679422345363421 / 1000000000000000000 : ℝ) (339362731049279 / 10000000000000000 : ℝ)
    (cell12507 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · have h := gap_lower (n := 12507) (a := (20923728293117 / 25000000000000 : ℝ)) (b := (20590434499 / 12500000000000 : ℝ)) (q := (1137958075301 / 50000000000000 : ℝ))
      (E := (cell12507 ⟨11, by decide⟩).energy) (xi := (339362731049279 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12507 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12507]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12507])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12507) (a := (20923728293117 / 25000000000000 : ℝ)) (b := (20590434499 / 12500000000000 : ℝ)) (q := (1137958075301 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12507])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12507])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12507]

theorem cert12507_12 : CellCertificate 12507 (446081116767709 / 5000000000000000 : ℝ) (1679422345363421 / 1000000000000000000 : ℝ) (339362731049279 / 10000000000000000 : ℝ)
    (cell12507 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · have h := gap_lower (n := 12507) (a := (83660148929593 / 100000000000000 : ℝ)) (b := (20590434499 / 12500000000000 : ℝ)) (q := (2275920134321 / 100000000000000 : ℝ))
      (E := (cell12507 ⟨12, by decide⟩).energy) (xi := (339362731049279 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12507 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12507]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12507])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12507) (a := (83660148929593 / 100000000000000 : ℝ)) (b := (20590434499 / 12500000000000 : ℝ)) (q := (2275920134321 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12507])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12507])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12507]

theorem cert12507_13 : CellCertificate 12507 (446081116767709 / 5000000000000000 : ℝ) (1679422345363421 / 1000000000000000000 : ℝ) (339362731049279 / 10000000000000000 : ℝ)
    (cell12507 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · have h := gap_lower (n := 12507) (a := (16725081863251 / 20000000000000 : ℝ)) (b := (20590434499 / 12500000000000 : ℝ)) (q := (455184828157 / 20000000000000 : ℝ))
      (E := (cell12507 ⟨13, by decide⟩).energy) (xi := (339362731049279 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12507 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12507]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12507])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12507) (a := (16725081863251 / 20000000000000 : ℝ)) (b := (20590434499 / 12500000000000 : ℝ)) (q := (455184828157 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12507])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12507])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12507]

theorem cert12507_14 : CellCertificate 12507 (446081116767709 / 5000000000000000 : ℝ) (1679422345363421 / 1000000000000000000 : ℝ) (339362731049279 / 10000000000000000 : ℝ)
    (cell12507 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · have h := gap_lower (n := 12507) (a := (83590694297821 / 100000000000000 : ℝ)) (b := (20590434499 / 12500000000000 : ℝ)) (q := (2275928176369 / 100000000000000 : ℝ))
      (E := (cell12507 ⟨14, by decide⟩).energy) (xi := (339362731049279 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12507 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12507]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12507])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12507) (a := (83590694297821 / 100000000000000 : ℝ)) (b := (20590434499 / 12500000000000 : ℝ)) (q := (2275928176369 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12507])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12507])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12507]

theorem cert12507_15 : CellCertificate 12507 (446081116767709 / 5000000000000000 : ℝ) (1679422345363421 / 1000000000000000000 : ℝ) (339362731049279 / 10000000000000000 : ℝ)
    (cell12507 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · have h := gap_lower (n := 12507) (a := (20889000959959 / 25000000000000 : ℝ)) (b := (20590434499 / 12500000000000 : ℝ)) (q := (56898303273 / 2500000000000 : ℝ))
      (E := (cell12507 ⟨15, by decide⟩).energy) (xi := (339362731049279 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12507 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12507]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12507])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12507) (a := (20889000959959 / 25000000000000 : ℝ)) (b := (20590434499 / 12500000000000 : ℝ)) (q := (56898303273 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12507])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12507])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12507]

theorem cert12507_16 : CellCertificate 12507 (446081116767709 / 5000000000000000 : ℝ) (1679422345363421 / 1000000000000000000 : ℝ) (339362731049279 / 10000000000000000 : ℝ)
    (cell12507 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · have h := gap_lower (n := 12507) (a := (10440167238503 / 12500000000000 : ℝ)) (b := (20590434499 / 12500000000000 : ℝ)) (q := (2275936126511 / 100000000000000 : ℝ))
      (E := (cell12507 ⟨16, by decide⟩).energy) (xi := (339362731049279 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12507 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12507]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12507])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12507) (a := (10440167238503 / 12500000000000 : ℝ)) (b := (20590434499 / 12500000000000 : ℝ)) (q := (2275936126511 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12507])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12507])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12507]

theorem cert12507_17 : CellCertificate 12507 (446081116767709 / 5000000000000000 : ℝ) (1679422345363421 / 1000000000000000000 : ℝ) (339362731049279 / 10000000000000000 : ℝ)
    (cell12507 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · have h := gap_lower (n := 12507) (a := (1304479632317 / 1562500000000 : ℝ)) (b := (20590434499 / 12500000000000 : ℝ)) (q := (1137970084391 / 50000000000000 : ℝ))
      (E := (cell12507 ⟨17, by decide⟩).energy) (xi := (339362731049279 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12507 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12507]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12507])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12507) (a := (1304479632317 / 1562500000000 : ℝ)) (b := (20590434499 / 12500000000000 : ℝ)) (q := (1137970084391 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12507])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12507])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12507]

theorem cert12507_18 : CellCertificate 12507 (446081116767709 / 5000000000000000 : ℝ) (1679422345363421 / 1000000000000000000 : ℝ) (339362731049279 / 10000000000000000 : ℝ)
    (cell12507 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · have h := gap_lower (n := 12507) (a := (20863019871677 / 25000000000000 : ℝ)) (b := (20590434499 / 12500000000000 : ℝ)) (q := (2275944146703 / 100000000000000 : ℝ))
      (E := (cell12507 ⟨18, by decide⟩).energy) (xi := (339362731049279 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12507 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12507]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12507])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12507) (a := (20863019871677 / 25000000000000 : ℝ)) (b := (20590434499 / 12500000000000 : ℝ)) (q := (2275944146703 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12507])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12507])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12507]

theorem cert12507_19 : CellCertificate 12507 (446081116767709 / 5000000000000000 : ℝ) (1679422345363421 / 1000000000000000000 : ℝ) (339362731049279 / 10000000000000000 : ℝ)
    (cell12507 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · have h := gap_lower (n := 12507) (a := (41708743464769 / 50000000000000 : ℝ)) (b := (20590434499 / 12500000000000 : ℝ)) (q := (2275948123523 / 100000000000000 : ℝ))
      (E := (cell12507 ⟨19, by decide⟩).energy) (xi := (339362731049279 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12507 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12507]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12507])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12507) (a := (41708743464769 / 50000000000000 : ℝ)) (b := (20590434499 / 12500000000000 : ℝ)) (q := (2275948123523 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12507])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12507])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12507]

theorem cert12508_0 : CellCertificate 12508 (223033366160033 / 2500000000000000 : ℝ) (1679288032683669 / 1000000000000000000 : ℝ) (67866982605843 / 2000000000000000 : ℝ)
    (cell12508 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · have h := gap_lower (n := 12508) (a := (84078939884031 / 100000000000000 : ℝ)) (b := (32942027993 / 20000000000000 : ℝ)) (q := (2275741594299 / 100000000000000 : ℝ))
      (E := (cell12508 ⟨0, by decide⟩).energy) (xi := (67866982605843 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12508 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12508]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12508])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12508) (a := (84078939884031 / 100000000000000 : ℝ)) (b := (32942027993 / 20000000000000 : ℝ)) (q := (2275741594299 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12508])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12508])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12508]

theorem cert12508_1 : CellCertificate 12508 (223033366160033 / 2500000000000000 : ℝ) (1679288032683669 / 1000000000000000000 : ℝ) (67866982605843 / 2000000000000000 : ℝ)
    (cell12508 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · have h := gap_lower (n := 12508) (a := (84043902705297 / 100000000000000 : ℝ)) (b := (32942027993 / 20000000000000 : ℝ)) (q := (11378728009 / 500000000000 : ℝ))
      (E := (cell12508 ⟨1, by decide⟩).energy) (xi := (67866982605843 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12508 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12508]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12508])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12508) (a := (84043902705297 / 100000000000000 : ℝ)) (b := (32942027993 / 20000000000000 : ℝ)) (q := (11378728009 / 500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12508])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12508])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12508]

theorem cert12508_2 : CellCertificate 12508 (223033366160033 / 2500000000000000 : ℝ) (1679288032683669 / 1000000000000000000 : ℝ) (67866982605843 / 2000000000000000 : ℝ)
    (cell12508 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · have h := gap_lower (n := 12508) (a := (42004445274431 / 50000000000000 : ℝ)) (b := (32942027993 / 20000000000000 : ℝ)) (q := (2275749603699 / 100000000000000 : ℝ))
      (E := (cell12508 ⟨2, by decide⟩).energy) (xi := (67866982605843 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12508 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12508]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12508])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12508) (a := (42004445274431 / 50000000000000 : ℝ)) (b := (32942027993 / 20000000000000 : ℝ)) (q := (2275749603699 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12508])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12508])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12508]

theorem cert12508_3 : CellCertificate 12508 (223033366160033 / 2500000000000000 : ℝ) (1679288032683669 / 1000000000000000000 : ℝ) (67866982605843 / 2000000000000000 : ℝ)
    (cell12508 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · have h := gap_lower (n := 12508) (a := (83973903378027 / 100000000000000 : ℝ)) (b := (32942027993 / 20000000000000 : ℝ)) (q := (2275753609239 / 100000000000000 : ℝ))
      (E := (cell12508 ⟨3, by decide⟩).energy) (xi := (67866982605843 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12508 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12508]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12508])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12508) (a := (83973903378027 / 100000000000000 : ℝ)) (b := (32942027993 / 20000000000000 : ℝ)) (q := (2275753609239 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12508])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12508])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12508]

theorem cert12508_4 : CellCertificate 12508 (223033366160033 / 2500000000000000 : ℝ) (1679288032683669 / 1000000000000000000 : ℝ) (67866982605843 / 2000000000000000 : ℝ)
    (cell12508 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · have h := gap_lower (n := 12508) (a := (20984735289073 / 25000000000000 : ℝ)) (b := (32942027993 / 20000000000000 : ℝ)) (q := (2275757627397 / 100000000000000 : ℝ))
      (E := (cell12508 ⟨4, by decide⟩).energy) (xi := (67866982605843 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12508 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12508]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12508])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12508) (a := (20984735289073 / 25000000000000 : ℝ)) (b := (32942027993 / 20000000000000 : ℝ)) (q := (2275757627397 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12508])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12508])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12508]

theorem cert12508_5 : CellCertificate 12508 (223033366160033 / 2500000000000000 : ℝ) (1679288032683669 / 1000000000000000000 : ℝ) (67866982605843 / 2000000000000000 : ℝ)
    (cell12508 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · have h := gap_lower (n := 12508) (a := (5244000240459 / 6250000000000 : ℝ)) (b := (32942027993 / 20000000000000 : ℝ)) (q := (227576160899 / 10000000000000 : ℝ))
      (E := (cell12508 ⟨5, by decide⟩).energy) (xi := (67866982605843 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12508 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12508]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12508])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12508) (a := (5244000240459 / 6250000000000 : ℝ)) (b := (32942027993 / 20000000000000 : ℝ)) (q := (227576160899 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12508])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12508])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12508]

theorem cert12508_6 : CellCertificate 12508 (223033366160033 / 2500000000000000 : ℝ) (1679288032683669 / 1000000000000000000 : ℝ) (67866982605843 / 2000000000000000 : ℝ)
    (cell12508 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · have h := gap_lower (n := 12508) (a := (41934545707533 / 50000000000000 : ℝ)) (b := (32942027993 / 20000000000000 : ℝ)) (q := (113788281017 / 5000000000000 : ℝ))
      (E := (cell12508 ⟨6, by decide⟩).energy) (xi := (67866982605843 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12508 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12508]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12508])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12508) (a := (41934545707533 / 50000000000000 : ℝ)) (b := (32942027993 / 20000000000000 : ℝ)) (q := (113788281017 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12508])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12508])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12508]

theorem cert12508_7 : CellCertificate 12508 (223033366160033 / 2500000000000000 : ℝ) (1679288032683669 / 1000000000000000000 : ℝ) (67866982605843 / 2000000000000000 : ℝ)
    (cell12508 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · have h := gap_lower (n := 12508) (a := (83834203823527 / 100000000000000 : ℝ)) (b := (32942027993 / 20000000000000 : ℝ)) (q := (1137884805851 / 50000000000000 : ℝ))
      (E := (cell12508 ⟨7, by decide⟩).energy) (xi := (67866982605843 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12508 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12508]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12508])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12508) (a := (83834203823527 / 100000000000000 : ℝ)) (b := (32942027993 / 20000000000000 : ℝ)) (q := (1137884805851 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12508])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12508])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12508]

theorem cert12508_8 : CellCertificate 12508 (223033366160033 / 2500000000000000 : ℝ) (1679288032683669 / 1000000000000000000 : ℝ) (67866982605843 / 2000000000000000 : ℝ)
    (cell12508 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · have h := gap_lower (n := 12508) (a := (83799341036989 / 100000000000000 : ℝ)) (b := (32942027993 / 20000000000000 : ℝ)) (q := (2275773590957 / 100000000000000 : ℝ))
      (E := (cell12508 ⟨8, by decide⟩).energy) (xi := (67866982605843 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12508 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12508]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12508])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12508) (a := (83799341036989 / 100000000000000 : ℝ)) (b := (32942027993 / 20000000000000 : ℝ)) (q := (2275773590957 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12508])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12508])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12508]

theorem cert12508_9 : CellCertificate 12508 (223033366160033 / 2500000000000000 : ℝ) (1679288032683669 / 1000000000000000000 : ℝ) (67866982605843 / 2000000000000000 : ℝ)
    (cell12508 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · have h := gap_lower (n := 12508) (a := (10470562877487 / 12500000000000 : ℝ)) (b := (32942027993 / 20000000000000 : ℝ)) (q := (1137888782867 / 50000000000000 : ℝ))
      (E := (cell12508 ⟨9, by decide⟩).energy) (xi := (67866982605843 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12508 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12508]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12508])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12508) (a := (10470562877487 / 12500000000000 : ℝ)) (b := (32942027993 / 20000000000000 : ℝ)) (q := (1137888782867 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12508])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12508])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12508]

theorem cert12508_10 : CellCertificate 12508 (223033366160033 / 2500000000000000 : ℝ) (1679288032683669 / 1000000000000000000 : ℝ) (67866982605843 / 2000000000000000 : ℝ)
    (cell12508 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · have h := gap_lower (n := 12508) (a := (20932422434221 / 25000000000000 : ℝ)) (b := (32942027993 / 20000000000000 : ℝ)) (q := (284472700179 / 12500000000000 : ℝ))
      (E := (cell12508 ⟨10, by decide⟩).energy) (xi := (67866982605843 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12508 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12508]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12508])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12508) (a := (20932422434221 / 25000000000000 : ℝ)) (b := (32942027993 / 20000000000000 : ℝ)) (q := (284472700179 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12508])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12508])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12508]

theorem cert12508_11 : CellCertificate 12508 (223033366160033 / 2500000000000000 : ℝ) (1679288032683669 / 1000000000000000000 : ℝ) (67866982605843 / 2000000000000000 : ℝ)
    (cell12508 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · have h := gap_lower (n := 12508) (a := (8369490115277 / 10000000000000 : ℝ)) (b := (32942027993 / 20000000000000 : ℝ)) (q := (45515711783 / 2000000000000 : ℝ))
      (E := (cell12508 ⟨11, by decide⟩).energy) (xi := (67866982605843 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12508 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12508]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12508])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12508) (a := (8369490115277 / 10000000000000 : ℝ)) (b := (32942027993 / 20000000000000 : ℝ)) (q := (45515711783 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12508])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12508])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12508]

theorem cert12508_12 : CellCertificate 12508 (223033366160033 / 2500000000000000 : ℝ) (1679288032683669 / 1000000000000000000 : ℝ) (67866982605843 / 2000000000000000 : ℝ)
    (cell12508 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · have h := gap_lower (n := 12508) (a := (20915034308139 / 25000000000000 : ℝ)) (b := (32942027993 / 20000000000000 : ℝ)) (q := (2275789593763 / 100000000000000 : ℝ))
      (E := (cell12508 ⟨12, by decide⟩).energy) (xi := (67866982605843 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12508 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12508]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12508])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12508) (a := (20915034308139 / 25000000000000 : ℝ)) (b := (32942027993 / 20000000000000 : ℝ)) (q := (2275789593763 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12508])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12508])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12508]

theorem cert12508_13 : CellCertificate 12508 (223033366160033 / 2500000000000000 : ℝ) (1679288032683669 / 1000000000000000000 : ℝ) (67866982605843 / 2000000000000000 : ℝ)
    (cell12508 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · have h := gap_lower (n := 12508) (a := (41812698970713 / 50000000000000 : ℝ)) (b := (32942027993 / 20000000000000 : ℝ)) (q := (2275793563801 / 100000000000000 : ℝ))
      (E := (cell12508 ⟨13, by decide⟩).energy) (xi := (67866982605843 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12508 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12508]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12508])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12508) (a := (41812698970713 / 50000000000000 : ℝ)) (b := (32942027993 / 20000000000000 : ℝ)) (q := (2275793563801 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12508])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12508])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12508]

theorem cert12508_14 : CellCertificate 12508 (223033366160033 / 2500000000000000 : ℝ) (1679288032683669 / 1000000000000000000 : ℝ) (67866982605843 / 2000000000000000 : ℝ)
    (cell12508 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · have h := gap_lower (n := 12508) (a := (20897670811187 / 25000000000000 : ℝ)) (b := (32942027993 / 20000000000000 : ℝ)) (q := (1137898781843 / 50000000000000 : ℝ))
      (E := (cell12508 ⟨14, by decide⟩).energy) (xi := (67866982605843 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12508 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12508]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12508])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12508) (a := (20897670811187 / 25000000000000 : ℝ)) (b := (32942027993 / 20000000000000 : ℝ)) (q := (1137898781843 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12508])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12508])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12508]

theorem cert12508_15 : CellCertificate 12508 (223033366160033 / 2500000000000000 : ℝ) (1679288032683669 / 1000000000000000000 : ℝ) (67866982605843 / 2000000000000000 : ℝ)
    (cell12508 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · have h := gap_lower (n := 12508) (a := (83555993108067 / 100000000000000 : ℝ)) (b := (32942027993 / 20000000000000 : ℝ)) (q := (568950399887 / 25000000000000 : ℝ))
      (E := (cell12508 ⟨15, by decide⟩).energy) (xi := (67866982605843 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12508 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12508]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12508])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12508) (a := (83555993108067 / 100000000000000 : ℝ)) (b := (32942027993 / 20000000000000 : ℝ)) (q := (568950399887 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12508])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12508])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12508]

theorem cert12508_16 : CellCertificate 12508 (223033366160033 / 2500000000000000 : ℝ) (1679288032683669 / 1000000000000000000 : ℝ) (67866982605843 / 2000000000000000 : ℝ)
    (cell12508 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · have h := gap_lower (n := 12508) (a := (20880331874277 / 25000000000000 : ℝ)) (b := (32942027993 / 20000000000000 : ℝ)) (q := (2275805560941 / 100000000000000 : ℝ))
      (E := (cell12508 ⟨16, by decide⟩).energy) (xi := (67866982605843 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12508 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12508]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12508])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12508) (a := (20880331874277 / 25000000000000 : ℝ)) (b := (32942027993 / 20000000000000 : ℝ)) (q := (2275805560941 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12508])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12508])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12508]

theorem cert12508_17 : CellCertificate 12508 (223033366160033 / 2500000000000000 : ℝ) (1679288032683669 / 1000000000000000000 : ℝ) (67866982605843 / 2000000000000000 : ℝ)
    (cell12508 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · have h := gap_lower (n := 12508) (a := (83486686377777 / 100000000000000 : ℝ)) (b := (32942027993 / 20000000000000 : ℝ)) (q := (284476196217 / 12500000000000 : ℝ))
      (E := (cell12508 ⟨17, by decide⟩).energy) (xi := (67866982605843 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12508 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12508]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12508])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12508) (a := (83486686377777 / 100000000000000 : ℝ)) (b := (32942027993 / 20000000000000 : ℝ)) (q := (284476196217 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12508])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12508])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12508]

theorem cert12508_18 : CellCertificate 12508 (223033366160033 / 2500000000000000 : ℝ) (1679288032683669 / 1000000000000000000 : ℝ) (67866982605843 / 2000000000000000 : ℝ)
    (cell12508 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · have h := gap_lower (n := 12508) (a := (83452069716151 / 100000000000000 : ℝ)) (b := (32942027993 / 20000000000000 : ℝ)) (q := (2275813573119 / 100000000000000 : ℝ))
      (E := (cell12508 ⟨18, by decide⟩).energy) (xi := (67866982605843 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12508 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12508]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12508])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12508) (a := (83452069716151 / 100000000000000 : ℝ)) (b := (32942027993 / 20000000000000 : ℝ)) (q := (2275813573119 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12508])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12508])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12508]

theorem cert12508_19 : CellCertificate 12508 (223033366160033 / 2500000000000000 : ℝ) (1679288032683669 / 1000000000000000000 : ℝ) (67866982605843 / 2000000000000000 : ℝ)
    (cell12508 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · have h := gap_lower (n := 12508) (a := (83417477478489 / 100000000000000 : ℝ)) (b := (32942027993 / 20000000000000 : ℝ)) (q := (2275817576169 / 100000000000000 : ℝ))
      (E := (cell12508 ⟨19, by decide⟩).energy) (xi := (67866982605843 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12508 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12508]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12508])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12508) (a := (83417477478489 / 100000000000000 : ℝ)) (b := (32942027993 / 20000000000000 : ℝ)) (q := (2275817576169 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12508])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12508])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12508]

theorem cert12509_0 : CellCertificate 12509 (892104700167997 / 10000000000000000 : ℝ) (33583074829713 / 20000000000000000 : ℝ) (339307099652453 / 10000000000000000 : ℝ)
    (cell12509 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · have h := gap_lower (n := 12509) (a := (84078924287351 / 100000000000000 : ℝ)) (b := (164696806117 / 100000000000000 : ℝ)) (q := (142225692541 / 6250000000000 : ℝ))
      (E := (cell12509 ⟨0, by decide⟩).energy) (xi := (339307099652453 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12509 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12509]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12509])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12509) (a := (84078924287351 / 100000000000000 : ℝ)) (b := (164696806117 / 100000000000000 : ℝ)) (q := (142225692541 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12509])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12509])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12509]

theorem cert12509_1 : CellCertificate 12509 (892104700167997 / 10000000000000000 : ℝ) (33583074829713 / 20000000000000000 : ℝ) (339307099652453 / 10000000000000000 : ℝ)
    (cell12509 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · have h := gap_lower (n := 12509) (a := (84043887436291 / 100000000000000 : ℝ)) (b := (164696806117 / 100000000000000 : ℝ)) (q := (2275615100593 / 100000000000000 : ℝ))
      (E := (cell12509 ⟨1, by decide⟩).energy) (xi := (339307099652453 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12509 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12509]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12509])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12509) (a := (84043887436291 / 100000000000000 : ℝ)) (b := (164696806117 / 100000000000000 : ℝ)) (q := (2275615100593 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12509])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12509])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12509]

theorem cert12509_2 : CellCertificate 12509 (892104700167997 / 10000000000000000 : ℝ) (33583074829713 / 20000000000000000 : ℝ) (339307099652453 / 10000000000000000 : ℝ)
    (cell12509 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · have h := gap_lower (n := 12509) (a := (10501109450883 / 12500000000000 : ℝ)) (b := (164696806117 / 100000000000000 : ℝ)) (q := (568904778929 / 25000000000000 : ℝ))
      (E := (cell12509 ⟨2, by decide⟩).energy) (xi := (339307099652453 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12509 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12509]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12509])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12509) (a := (10501109450883 / 12500000000000 : ℝ)) (b := (164696806117 / 100000000000000 : ℝ)) (q := (568904778929 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12509])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12509])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12509]

theorem cert12509_3 : CellCertificate 12509 (892104700167997 / 10000000000000000 : ℝ) (33583074829713 / 20000000000000000 : ℝ) (339307099652453 / 10000000000000000 : ℝ)
    (cell12509 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · have h := gap_lower (n := 12509) (a := (3358955550519 / 4000000000000 : ℝ)) (b := (164696806117 / 100000000000000 : ℝ)) (q := (2275623077403 / 100000000000000 : ℝ))
      (E := (cell12509 ⟨3, by decide⟩).energy) (xi := (339307099652453 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12509 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12509]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12509])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12509) (a := (3358955550519 / 4000000000000 : ℝ)) (b := (164696806117 / 100000000000000 : ℝ)) (q := (2275623077403 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12509])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12509])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12509]

theorem cert12509_4 : CellCertificate 12509 (892104700167997 / 10000000000000000 : ℝ) (33583074829713 / 20000000000000000 : ℝ) (339307099652453 / 10000000000000000 : ℝ)
    (cell12509 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · have h := gap_lower (n := 12509) (a := (41969463433761 / 50000000000000 : ℝ)) (b := (164696806117 / 100000000000000 : ℝ)) (q := (2275627110331 / 100000000000000 : ℝ))
      (E := (cell12509 ⟨4, by decide⟩).energy) (xi := (339307099652453 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12509 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12509]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12509])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12509) (a := (41969463433761 / 50000000000000 : ℝ)) (b := (164696806117 / 100000000000000 : ℝ)) (q := (2275627110331 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12509])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12509])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12509]

theorem cert12509_5 : CellCertificate 12509 (892104700167997 / 10000000000000000 : ℝ) (33583074829713 / 20000000000000000 : ℝ) (339307099652453 / 10000000000000000 : ℝ)
    (cell12509 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · have h := gap_lower (n := 12509) (a := (83903989884397 / 100000000000000 : ℝ)) (b := (164696806117 / 100000000000000 : ℝ)) (q := (1137815553737 / 50000000000000 : ℝ))
      (E := (cell12509 ⟨5, by decide⟩).energy) (xi := (339307099652453 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12509 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12509]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12509])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12509) (a := (83903989884397 / 100000000000000 : ℝ)) (b := (164696806117 / 100000000000000 : ℝ)) (q := (1137815553737 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12509])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12509])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12509]

theorem cert12509_6 : CellCertificate 12509 (892104700167997 / 10000000000000000 : ℝ) (33583074829713 / 20000000000000000 : ℝ) (339307099652453 / 10000000000000000 : ℝ)
    (cell12509 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · have h := gap_lower (n := 12509) (a := (2096726944437 / 2500000000000 : ℝ)) (b := (164696806117 / 100000000000000 : ℝ)) (q := (2275635077227 / 100000000000000 : ℝ))
      (E := (cell12509 ⟨6, by decide⟩).energy) (xi := (339307099652453 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12509 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12509]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12509])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12509) (a := (2096726944437 / 2500000000000 : ℝ)) (b := (164696806117 / 100000000000000 : ℝ)) (q := (2275635077227 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12509])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12509])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12509]

theorem cert12509_7 : CellCertificate 12509 (892104700167997 / 10000000000000000 : ℝ) (33583074829713 / 20000000000000000 : ℝ) (339307099652453 / 10000000000000000 : ℝ)
    (cell12509 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · have h := gap_lower (n := 12509) (a := (16766838102169 / 20000000000000 : ℝ)) (b := (164696806117 / 100000000000000 : ℝ)) (q := (2275639085679 / 100000000000000 : ℝ))
      (E := (cell12509 ⟨7, by decide⟩).energy) (xi := (339307099652453 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12509 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12509]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12509])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12509) (a := (16766838102169 / 20000000000000 : ℝ)) (b := (164696806117 / 100000000000000 : ℝ)) (q := (2275639085679 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12509])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12509])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12509]

theorem cert12509_8 : CellCertificate 12509 (892104700167997 / 10000000000000000 : ℝ) (33583074829713 / 20000000000000000 : ℝ) (339307099652453 / 10000000000000000 : ℝ)
    (cell12509 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · have h := gap_lower (n := 12509) (a := (83799328048751 / 100000000000000 : ℝ)) (b := (164696806117 / 100000000000000 : ℝ)) (q := (568910770701 / 25000000000000 : ℝ))
      (E := (cell12509 ⟨8, by decide⟩).energy) (xi := (339307099652453 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12509 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12509]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12509])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12509) (a := (83799328048751 / 100000000000000 : ℝ)) (b := (164696806117 / 100000000000000 : ℝ)) (q := (568910770701 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12509])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12509])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12509]

theorem cert12509_9 : CellCertificate 12509 (892104700167997 / 10000000000000000 : ℝ) (33583074829713 / 20000000000000000 : ℝ) (339307099652453 / 10000000000000000 : ℝ)
    (cell12509 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · have h := gap_lower (n := 12509) (a := (41882245177823 / 50000000000000 : ℝ)) (b := (164696806117 / 100000000000000 : ℝ)) (q := (227564707623 / 10000000000000 : ℝ))
      (E := (cell12509 ⟨9, by decide⟩).energy) (xi := (339307099652453 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12509 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12509]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12509])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12509) (a := (41882245177823 / 50000000000000 : ℝ)) (b := (164696806117 / 100000000000000 : ℝ)) (q := (227564707623 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12509])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12509])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12509]

theorem cert12509_10 : CellCertificate 12509 (892104700167997 / 10000000000000000 : ℝ) (33583074829713 / 20000000000000000 : ℝ) (339307099652453 / 10000000000000000 : ℝ)
    (cell12509 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · have h := gap_lower (n := 12509) (a := (16745935479233 / 20000000000000 : ℝ)) (b := (164696806117 / 100000000000000 : ℝ)) (q := (568912768333 / 25000000000000 : ℝ))
      (E := (cell12509 ⟨10, by decide⟩).energy) (xi := (339307099652453 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12509 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12509]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12509])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12509) (a := (16745935479233 / 20000000000000 : ℝ)) (b := (164696806117 / 100000000000000 : ℝ)) (q := (568912768333 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12509])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12509])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12509]

theorem cert12509_11 : CellCertificate 12509 (892104700167997 / 10000000000000000 : ℝ) (33583074829713 / 20000000000000000 : ℝ) (339307099652453 / 10000000000000000 : ℝ)
    (cell12509 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · have h := gap_lower (n := 12509) (a := (83694889135127 / 100000000000000 : ℝ)) (b := (164696806117 / 100000000000000 : ℝ)) (q := (2275655081231 / 100000000000000 : ℝ))
      (E := (cell12509 ⟨11, by decide⟩).energy) (xi := (339307099652453 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12509 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12509]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12509])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12509) (a := (83694889135127 / 100000000000000 : ℝ)) (b := (164696806117 / 100000000000000 : ℝ)) (q := (2275655081231 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12509])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12509])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12509]

theorem cert12509_12 : CellCertificate 12509 (892104700167997 / 10000000000000000 : ℝ) (33583074829713 / 20000000000000000 : ℝ) (339307099652453 / 10000000000000000 : ℝ)
    (cell12509 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · have h := gap_lower (n := 12509) (a := (41830062768767 / 50000000000000 : ℝ)) (b := (164696806117 / 100000000000000 : ℝ)) (q := (2275659048731 / 100000000000000 : ℝ))
      (E := (cell12509 ⟨12, by decide⟩).energy) (xi := (339307099652453 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12509 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12509]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12509])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12509) (a := (41830062768767 / 50000000000000 : ℝ)) (b := (164696806117 / 100000000000000 : ℝ)) (q := (2275659048731 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12509])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12509])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12509]

theorem cert12509_13 : CellCertificate 12509 (892104700167997 / 10000000000000000 : ℝ) (33583074829713 / 20000000000000000 : ℝ) (339307099652453 / 10000000000000000 : ℝ)
    (cell12509 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · have h := gap_lower (n := 12509) (a := (83625386568573 / 100000000000000 : ℝ)) (b := (164696806117 / 100000000000000 : ℝ)) (q := (2275663040477 / 100000000000000 : ℝ))
      (E := (cell12509 ⟨13, by decide⟩).energy) (xi := (339307099652453 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12509 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12509]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12509])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12509) (a := (83625386568573 / 100000000000000 : ℝ)) (b := (164696806117 / 100000000000000 : ℝ)) (q := (2275663040477 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12509])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12509])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12509]

theorem cert12509_14 : CellCertificate 12509 (892104700167997 / 10000000000000000 : ℝ) (33583074829713 / 20000000000000000 : ℝ) (339307099652453 / 10000000000000000 : ℝ)
    (cell12509 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · have h := gap_lower (n := 12509) (a := (8359067219361 / 10000000000000 : ℝ)) (b := (164696806117 / 100000000000000 : ℝ)) (q := (2275667062847 / 100000000000000 : ℝ))
      (E := (cell12509 ⟨14, by decide⟩).energy) (xi := (339307099652453 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12509 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12509]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12509])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12509) (a := (8359067219361 / 10000000000000 : ℝ)) (b := (164696806117 / 100000000000000 : ℝ)) (q := (2275667062847 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12509])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12509])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12509]

theorem cert12509_15 : CellCertificate 12509 (892104700167997 / 10000000000000000 : ℝ) (33583074829713 / 20000000000000000 : ℝ) (339307099652453 / 10000000000000000 : ℝ)
    (cell12509 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · have h := gap_lower (n := 12509) (a := (41777991189097 / 50000000000000 : ℝ)) (b := (164696806117 / 100000000000000 : ℝ)) (q := (142229441489 / 6250000000000 : ℝ))
      (E := (cell12509 ⟨15, by decide⟩).energy) (xi := (339307099652453 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12509 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12509]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12509])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12509) (a := (41777991189097 / 50000000000000 : ℝ)) (b := (164696806117 / 100000000000000 : ℝ)) (q := (142229441489 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12509])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12509])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12509]

theorem cert12509_16 : CellCertificate 12509 (892104700167997 / 10000000000000000 : ℝ) (33583074829713 / 20000000000000000 : ℝ) (339307099652453 / 10000000000000000 : ℝ)
    (cell12509 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · have h := gap_lower (n := 12509) (a := (1670426341761 / 2000000000000 : ℝ)) (b := (164696806117 / 100000000000000 : ℝ)) (q := (1137837524611 / 50000000000000 : ℝ))
      (E := (cell12509 ⟨16, by decide⟩).energy) (xi := (339307099652453 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12509 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12509]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12509])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12509) (a := (1670426341761 / 2000000000000 : ℝ)) (b := (164696806117 / 100000000000000 : ℝ)) (q := (1137837524611 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12509])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12509])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12509]

theorem cert12509_17 : CellCertificate 12509 (892104700167997 / 10000000000000000 : ℝ) (33583074829713 / 20000000000000000 : ℝ) (339307099652453 / 10000000000000000 : ℝ)
    (cell12509 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · have h := gap_lower (n := 12509) (a := (41743338144541 / 50000000000000 : ℝ)) (b := (164696806117 / 100000000000000 : ℝ)) (q := (2275679024607 / 100000000000000 : ℝ))
      (E := (cell12509 ⟨17, by decide⟩).energy) (xi := (339307099652453 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12509 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12509]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12509])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12509) (a := (41743338144541 / 50000000000000 : ℝ)) (b := (164696806117 / 100000000000000 : ℝ)) (q := (2275679024607 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12509])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12509])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12509]

theorem cert12509_18 : CellCertificate 12509 (892104700167997 / 10000000000000000 : ℝ) (33583074829713 / 20000000000000000 : ℝ) (339307099652453 / 10000000000000000 : ℝ)
    (cell12509 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · have h := gap_lower (n := 12509) (a := (83452059947373 / 100000000000000 : ℝ)) (b := (164696806117 / 100000000000000 : ℝ)) (q := (455136610703 / 20000000000000 : ℝ))
      (E := (cell12509 ⟨18, by decide⟩).energy) (xi := (339307099652453 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12509 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12509]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12509])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12509) (a := (83452059947373 / 100000000000000 : ℝ)) (b := (164696806117 / 100000000000000 : ℝ)) (q := (455136610703 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12509])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12509])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12509]

theorem cert12509_19 : CellCertificate 12509 (892104700167997 / 10000000000000000 : ℝ) (33583074829713 / 20000000000000000 : ℝ) (339307099652453 / 10000000000000000 : ℝ)
    (cell12509 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · have h := gap_lower (n := 12509) (a := (83417468029179 / 100000000000000 : ℝ)) (b := (164696806117 / 100000000000000 : ℝ)) (q := (142230439039 / 6250000000000 : ℝ))
      (E := (cell12509 ⟨19, by decide⟩).energy) (xi := (339307099652453 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12509 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12509]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12509])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12509) (a := (83417468029179 / 100000000000000 : ℝ)) (b := (164696806117 / 100000000000000 : ℝ)) (q := (142230439039 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12509])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12509])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12509]

theorem cert12510_0 : CellCertificate 12510 (111509492514743 / 1250000000000000 : ℝ) (1679019471764211 / 1000000000000000000 : ℝ) (84819822729427 / 2500000000000000 : ℝ)
    (cell12510 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · have h := gap_lower (n := 12510) (a := (5254931793323 / 6250000000000 : ℝ)) (b := (10292717153 / 6250000000000 : ℝ)) (q := (2275480619833 / 100000000000000 : ℝ))
      (E := (cell12510 ⟨0, by decide⟩).energy) (xi := (84819822729427 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12510 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12510]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12510])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12510) (a := (5254931793323 / 6250000000000 : ℝ)) (b := (10292717153 / 6250000000000 : ℝ)) (q := (2275480619833 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12510])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12510])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12510]

theorem cert12510_1 : CellCertificate 12510 (111509492514743 / 1250000000000000 : ℝ) (1679019471764211 / 1000000000000000000 : ℝ) (84819822729427 / 2500000000000000 : ℝ)
    (cell12510 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · have h := gap_lower (n := 12510) (a := (4202193608487 / 5000000000000 : ℝ)) (b := (10292717153 / 6250000000000 : ℝ)) (q := (2275484594459 / 100000000000000 : ℝ))
      (E := (cell12510 ⟨1, by decide⟩).energy) (xi := (84819822729427 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12510 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12510]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12510])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12510) (a := (4202193608487 / 5000000000000 : ℝ)) (b := (10292717153 / 6250000000000 : ℝ)) (q := (2275484594459 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12510])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12510])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12510]

theorem cert12510_2 : CellCertificate 12510 (111509492514743 / 1250000000000000 : ℝ) (1679019471764211 / 1000000000000000000 : ℝ) (84819822729427 / 2500000000000000 : ℝ)
    (cell12510 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · have h := gap_lower (n := 12510) (a := (42004430333841 / 50000000000000 : ℝ)) (b := (10292717153 / 6250000000000 : ℝ)) (q := (1137744311423 / 50000000000000 : ℝ))
      (E := (cell12510 ⟨2, by decide⟩).energy) (xi := (84819822729427 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12510 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12510]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12510])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12510) (a := (42004430333841 / 50000000000000 : ℝ)) (b := (10292717153 / 6250000000000 : ℝ)) (q := (1137744311423 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12510])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12510])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12510]

theorem cert12510_3 : CellCertificate 12510 (111509492514743 / 1250000000000000 : ℝ) (1679019471764211 / 1000000000000000000 : ℝ) (84819822729427 / 2500000000000000 : ℝ)
    (cell12510 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · have h := gap_lower (n := 12510) (a := (41986937075149 / 50000000000000 : ℝ)) (b := (10292717153 / 6250000000000 : ℝ)) (q := (1137746299291 / 50000000000000 : ℝ))
      (E := (cell12510 ⟨3, by decide⟩).energy) (xi := (84819822729427 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12510 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12510]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12510])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12510) (a := (41986937075149 / 50000000000000 : ℝ)) (b := (10292717153 / 6250000000000 : ℝ)) (q := (1137746299291 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12510])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12510])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12510]

theorem cert12510_4 : CellCertificate 12510 (111509492514743 / 1250000000000000 : ℝ) (1679019471764211 / 1000000000000000000 : ℝ) (84819822729427 / 2500000000000000 : ℝ)
    (cell12510 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · have h := gap_lower (n := 12510) (a := (2623091018159 / 3125000000000 : ℝ)) (b := (10292717153 / 6250000000000 : ℝ)) (q := (2275496588459 / 100000000000000 : ℝ))
      (E := (cell12510 ⟨4, by decide⟩).energy) (xi := (84819822729427 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12510 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12510]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12510])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12510) (a := (2623091018159 / 3125000000000 : ℝ)) (b := (10292717153 / 6250000000000 : ℝ)) (q := (2275496588459 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12510])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12510])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12510]

theorem cert12510_5 : CellCertificate 12510 (111509492514743 / 1250000000000000 : ℝ) (1679019471764211 / 1000000000000000000 : ℝ) (84819822729427 / 2500000000000000 : ℝ)
    (cell12510 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · have h := gap_lower (n := 12510) (a := (16780795184749 / 20000000000000 : ℝ)) (b := (10292717153 / 6250000000000 : ℝ)) (q := (455100120239 / 20000000000000 : ℝ))
      (E := (cell12510 ⟨5, by decide⟩).energy) (xi := (84819822729427 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12510 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12510]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12510])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12510) (a := (16780795184749 / 20000000000000 : ℝ)) (b := (10292717153 / 6250000000000 : ℝ)) (q := (455100120239 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12510])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12510])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12510]

theorem cert12510_6 : CellCertificate 12510 (111509492514743 / 1250000000000000 : ℝ) (1679019471764211 / 1000000000000000000 : ℝ) (84819822729427 / 2500000000000000 : ℝ)
    (cell12510 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · have h := gap_lower (n := 12510) (a := (1677381282843 / 2000000000000 : ℝ)) (b := (10292717153 / 6250000000000 : ℝ)) (q := (1137752293661 / 50000000000000 : ℝ))
      (E := (cell12510 ⟨6, by decide⟩).energy) (xi := (84819822729427 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12510 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12510]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12510])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12510) (a := (1677381282843 / 2000000000000 : ℝ)) (b := (10292717153 / 6250000000000 : ℝ)) (q := (1137752293661 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12510])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12510])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12510]

theorem cert12510_7 : CellCertificate 12510 (111509492514743 / 1250000000000000 : ℝ) (1679019471764211 / 1000000000000000000 : ℝ) (84819822729427 / 2500000000000000 : ℝ)
    (cell12510 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · have h := gap_lower (n := 12510) (a := (83834177200377 / 100000000000000 : ℝ)) (b := (10292717153 / 6250000000000 : ℝ)) (q := (227550861293 / 10000000000000 : ℝ))
      (E := (cell12510 ⟨7, by decide⟩).energy) (xi := (84819822729427 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12510 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12510]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12510])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12510) (a := (83834177200377 / 100000000000000 : ℝ)) (b := (10292717153 / 6250000000000 : ℝ)) (q := (227550861293 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12510])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12510])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12510]

theorem cert12510_8 : CellCertificate 12510 (111509492514743 / 1250000000000000 : ℝ) (1679019471764211 / 1000000000000000000 : ℝ) (84819822729427 / 2500000000000000 : ℝ)
    (cell12510 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · have h := gap_lower (n := 12510) (a := (2618728595709 / 3125000000000 : ℝ)) (b := (10292717153 / 6250000000000 : ℝ)) (q := (568878142503 / 25000000000000 : ℝ))
      (E := (cell12510 ⟨8, by decide⟩).energy) (xi := (84819822729427 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12510 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12510]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12510])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12510) (a := (2618728595709 / 3125000000000 : ℝ)) (b := (10292717153 / 6250000000000 : ℝ)) (q := (568878142503 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12510])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12510])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12510]

theorem cert12510_9 : CellCertificate 12510 (111509492514743 / 1250000000000000 : ℝ) (1679019471764211 / 1000000000000000000 : ℝ) (84819822729427 / 2500000000000000 : ℝ)
    (cell12510 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · have h := gap_lower (n := 12510) (a := (8376447769353 / 10000000000000 : ℝ)) (b := (10292717153 / 6250000000000 : ℝ)) (q := (227551658213 / 10000000000000 : ℝ))
      (E := (cell12510 ⟨9, by decide⟩).energy) (xi := (84819822729427 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12510 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12510]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12510])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12510) (a := (8376447769353 / 10000000000000 : ℝ)) (b := (10292717153 / 6250000000000 : ℝ)) (q := (227551658213 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12510])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12510])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12510]

theorem cert12510_10 : CellCertificate 12510 (111509492514743 / 1250000000000000 : ℝ) (1679019471764211 / 1000000000000000000 : ℝ) (84819822729427 / 2500000000000000 : ℝ)
    (cell12510 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · have h := gap_lower (n := 12510) (a := (4186483252877 / 5000000000000 : ℝ)) (b := (10292717153 / 6250000000000 : ℝ)) (q := (22755205987 / 1000000000000 : ℝ))
      (E := (cell12510 ⟨10, by decide⟩).energy) (xi := (84819822729427 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12510 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12510]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12510])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12510) (a := (4186483252877 / 5000000000000 : ℝ)) (b := (10292717153 / 6250000000000 : ℝ)) (q := (22755205987 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12510])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12510])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12510]

theorem cert12510_11 : CellCertificate 12510 (111509492514743 / 1250000000000000 : ℝ) (1679019471764211 / 1000000000000000000 : ℝ) (84819822729427 / 2500000000000000 : ℝ)
    (cell12510 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · have h := gap_lower (n := 12510) (a := (41847438559769 / 50000000000000 : ℝ)) (b := (10292717153 / 6250000000000 : ℝ)) (q := (2275524568797 / 100000000000000 : ℝ))
      (E := (cell12510 ⟨11, by decide⟩).energy) (xi := (84819822729427 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12510 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12510]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12510])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12510) (a := (41847438559769 / 50000000000000 : ℝ)) (b := (10292717153 / 6250000000000 : ℝ)) (q := (2275524568797 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12510])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12510])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12510]

theorem cert12510_12 : CellCertificate 12510 (111509492514743 / 1250000000000000 : ℝ) (1679019471764211 / 1000000000000000000 : ℝ) (84819822729427 / 2500000000000000 : ℝ)
    (cell12510 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · have h := gap_lower (n := 12510) (a := (83660113844527 / 100000000000000 : ℝ)) (b := (10292717153 / 6250000000000 : ℝ)) (q := (455105711459 / 20000000000000 : ℝ))
      (E := (cell12510 ⟨12, by decide⟩).energy) (xi := (84819822729427 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12510 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12510]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12510])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12510) (a := (83660113844527 / 100000000000000 : ℝ)) (b := (10292717153 / 6250000000000 : ℝ)) (q := (455105711459 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12510])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12510])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12510]

theorem cert12510_13 : CellCertificate 12510 (111509492514743 / 1250000000000000 : ℝ) (1679019471764211 / 1000000000000000000 : ℝ) (84819822729427 / 2500000000000000 : ℝ)
    (cell12510 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · have h := gap_lower (n := 12510) (a := (16725075039539 / 20000000000000 : ℝ)) (b := (10292717153 / 6250000000000 : ℝ)) (q := (455106514163 / 20000000000000 : ℝ))
      (E := (cell12510 ⟨13, by decide⟩).energy) (xi := (84819822729427 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12510 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12510]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12510])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12510) (a := (16725075039539 / 20000000000000 : ℝ)) (b := (10292717153 / 6250000000000 : ℝ)) (q := (455106514163 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12510])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12510])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12510]

theorem cert12510_14 : CellCertificate 12510 (111509492514743 / 1250000000000000 : ℝ) (1679019471764211 / 1000000000000000000 : ℝ) (84819822729427 / 2500000000000000 : ℝ)
    (cell12510 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · have h := gap_lower (n := 12510) (a := (10448832643051 / 12500000000000 : ℝ)) (b := (10292717153 / 6250000000000 : ℝ)) (q := (1137768278807 / 50000000000000 : ℝ))
      (E := (cell12510 ⟨14, by decide⟩).energy) (xi := (84819822729427 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12510 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12510]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12510])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12510) (a := (10448832643051 / 12500000000000 : ℝ)) (b := (10292717153 / 6250000000000 : ℝ)) (q := (1137768278807 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12510])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12510])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12510]

theorem cert12510_15 : CellCertificate 12510 (111509492514743 / 1250000000000000 : ℝ) (1679019471764211 / 1000000000000000000 : ℝ) (84819822729427 / 2500000000000000 : ℝ)
    (cell12510 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · have h := gap_lower (n := 12510) (a := (83555971650217 / 100000000000000 : ℝ)) (b := (10292717153 / 6250000000000 : ℝ)) (q := (2275540581889 / 100000000000000 : ℝ))
      (E := (cell12510 ⟨15, by decide⟩).energy) (xi := (84819822729427 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12510 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12510]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12510])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12510) (a := (83555971650217 / 100000000000000 : ℝ)) (b := (10292717153 / 6250000000000 : ℝ)) (q := (2275540581889 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12510])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12510])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12510]

theorem cert12510_16 : CellCertificate 12510 (111509492514743 / 1250000000000000 : ℝ) (1679019471764211 / 1000000000000000000 : ℝ) (84819822729427 / 2500000000000000 : ℝ)
    (cell12510 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · have h := gap_lower (n := 12510) (a := (83521306680847 / 100000000000000 : ℝ)) (b := (10292717153 / 6250000000000 : ℝ)) (q := (2275544591357 / 100000000000000 : ℝ))
      (E := (cell12510 ⟨16, by decide⟩).energy) (xi := (84819822729427 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12510 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12510]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12510])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12510) (a := (83521306680847 / 100000000000000 : ℝ)) (b := (10292717153 / 6250000000000 : ℝ)) (q := (2275544591357 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12510])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12510])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12510]

theorem cert12510_17 : CellCertificate 12510 (111509492514743 / 1250000000000000 : ℝ) (1679019471764211 / 1000000000000000000 : ℝ) (84819822729427 / 2500000000000000 : ℝ)
    (cell12510 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · have h := gap_lower (n := 12510) (a := (16697333240441 / 20000000000000 : ℝ)) (b := (10292717153 / 6250000000000 : ℝ)) (q := (71110893487 / 3125000000000 : ℝ))
      (E := (cell12510 ⟨17, by decide⟩).energy) (xi := (84819822729427 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12510 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12510]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12510])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12510) (a := (16697333240441 / 20000000000000 : ℝ)) (b := (10292717153 / 6250000000000 : ℝ)) (q := (71110893487 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12510])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12510])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12510]

theorem cert12510_18 : CellCertificate 12510 (111509492514743 / 1250000000000000 : ℝ) (1679019471764211 / 1000000000000000000 : ℝ) (84819822729427 / 2500000000000000 : ℝ)
    (cell12510 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · have h := gap_lower (n := 12510) (a := (20863012545093 / 25000000000000 : ℝ)) (b := (10292717153 / 6250000000000 : ℝ)) (q := (568888146973 / 25000000000000 : ℝ))
      (E := (cell12510 ⟨18, by decide⟩).energy) (xi := (84819822729427 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12510 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12510]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12510])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12510) (a := (20863012545093 / 25000000000000 : ℝ)) (b := (10292717153 / 6250000000000 : ℝ)) (q := (568888146973 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12510])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12510])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12510]

theorem cert12510_19 : CellCertificate 12510 (111509492514743 / 1250000000000000 : ℝ) (1679019471764211 / 1000000000000000000 : ℝ) (84819822729427 / 2500000000000000 : ℝ)
    (cell12510 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · have h := gap_lower (n := 12510) (a := (41708729290803 / 50000000000000 : ℝ)) (b := (10292717153 / 6250000000000 : ℝ)) (q := (28444457317 / 1250000000000 : ℝ))
      (E := (cell12510 ⟨19, by decide⟩).energy) (xi := (84819822729427 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12510 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12510]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12510])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12510) (a := (41708729290803 / 50000000000000 : ℝ)) (b := (10292717153 / 6250000000000 : ℝ)) (q := (28444457317 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12510])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12510])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12510]

theorem cert12511_0 : CellCertificate 12511 (111505898061113 / 1250000000000000 : ℝ) (1678885223514201 / 1000000000000000000 : ℝ) (67850297364739 / 2000000000000000 : ℝ)
    (cell12511 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · have h := gap_lower (n := 12511) (a := (42039446550741 / 50000000000000 : ℝ)) (b := (164670144957 / 100000000000000 : ℝ)) (q := (2275350211833 / 100000000000000 : ℝ))
      (E := (cell12511 ⟨0, by decide⟩).energy) (xi := (67850297364739 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12511 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12511]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12511])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12511) (a := (42039446550741 / 50000000000000 : ℝ)) (b := (164670144957 / 100000000000000 : ℝ)) (q := (2275350211833 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12511])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12511])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12511]

theorem cert12511_1 : CellCertificate 12511 (111505898061113 / 1250000000000000 : ℝ) (1678885223514201 / 1000000000000000000 : ℝ) (67850297364739 / 2000000000000000 : ℝ)
    (cell12511 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · have h := gap_lower (n := 12511) (a := (42021928452823 / 50000000000000 : ℝ)) (b := (164670144957 / 100000000000000 : ℝ)) (q := (1137677099513 / 50000000000000 : ℝ))
      (E := (cell12511 ⟨1, by decide⟩).energy) (xi := (67850297364739 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12511 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12511]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12511])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12511) (a := (42021928452823 / 50000000000000 : ℝ)) (b := (164670144957 / 100000000000000 : ℝ)) (q := (1137677099513 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12511])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12511])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12511]

theorem cert12511_2 : CellCertificate 12511 (111505898061113 / 1250000000000000 : ℝ) (1678885223514201 / 1000000000000000000 : ℝ) (67850297364739 / 2000000000000000 : ℝ)
    (cell12511 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · have h := gap_lower (n := 12511) (a := (16801769146143 / 20000000000000 : ℝ)) (b := (164670144957 / 100000000000000 : ℝ)) (q := (2275358182929 / 100000000000000 : ℝ))
      (E := (cell12511 ⟨2, by decide⟩).energy) (xi := (67850297364739 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12511 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12511]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12511])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12511) (a := (16801769146143 / 20000000000000 : ℝ)) (b := (164670144957 / 100000000000000 : ℝ)) (q := (2275358182929 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12511])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12511])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12511]

theorem cert12511_3 : CellCertificate 12511 (111505898061113 / 1250000000000000 : ℝ) (1678885223514201 / 1000000000000000000 : ℝ) (67850297364739 / 2000000000000000 : ℝ)
    (cell12511 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · have h := gap_lower (n := 12511) (a := (20993464884999 / 25000000000000 : ℝ)) (b := (164670144957 / 100000000000000 : ℝ)) (q := (113768108639 / 5000000000000 : ℝ))
      (E := (cell12511 ⟨3, by decide⟩).energy) (xi := (67850297364739 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12511 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12511]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12511])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12511) (a := (20993464884999 / 25000000000000 : ℝ)) (b := (164670144957 / 100000000000000 : ℝ)) (q := (113768108639 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12511])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12511])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12511]

theorem cert12511_4 : CellCertificate 12511 (111505898061113 / 1250000000000000 : ℝ) (1678885223514201 / 1000000000000000000 : ℝ) (67850297364739 / 2000000000000000 : ℝ)
    (cell12511 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · have h := gap_lower (n := 12511) (a := (83938898296989 / 100000000000000 : ℝ)) (b := (164670144957 / 100000000000000 : ℝ)) (q := (1137683088777 / 50000000000000 : ℝ))
      (E := (cell12511 ⟨4, by decide⟩).energy) (xi := (67850297364739 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12511 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12511]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12511])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12511) (a := (83938898296989 / 100000000000000 : ℝ)) (b := (164670144957 / 100000000000000 : ℝ)) (q := (1137683088777 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12511])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12511])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12511]

theorem cert12511_5 : CellCertificate 12511 (111505898061113 / 1250000000000000 : ℝ) (1678885223514201 / 1000000000000000000 : ℝ) (67850297364739 / 2000000000000000 : ℝ)
    (cell12511 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · have h := gap_lower (n := 12511) (a := (83903961965387 / 100000000000000 : ℝ)) (b := (164670144957 / 100000000000000 : ℝ)) (q := (568842551493 / 25000000000000 : ℝ))
      (E := (cell12511 ⟨5, by decide⟩).energy) (xi := (67850297364739 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12511 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12511]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12511])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12511) (a := (83903961965387 / 100000000000000 : ℝ)) (b := (164670144957 / 100000000000000 : ℝ)) (q := (568842551493 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12511])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12511])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12511]

theorem cert12511_6 : CellCertificate 12511 (111505898061113 / 1250000000000000 : ℝ) (1678885223514201 / 1000000000000000000 : ℝ) (67850297364739 / 2000000000000000 : ℝ)
    (cell12511 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · have h := gap_lower (n := 12511) (a := (41934525254537 / 50000000000000 : ℝ)) (b := (164670144957 / 100000000000000 : ℝ)) (q := (227537415063 / 10000000000000 : ℝ))
      (E := (cell12511 ⟨6, by decide⟩).energy) (xi := (67850297364739 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12511 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12511]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12511])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12511) (a := (41934525254537 / 50000000000000 : ℝ)) (b := (164670144957 / 100000000000000 : ℝ)) (q := (227537415063 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12511])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12511])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12511]

theorem cert12511_7 : CellCertificate 12511 (111505898061113 / 1250000000000000 : ℝ) (1678885223514201 / 1000000000000000000 : ℝ) (67850297364739 / 2000000000000000 : ℝ)
    (cell12511 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · have h := gap_lower (n := 12511) (a := (83834163892123 / 100000000000000 : ℝ)) (b := (164670144957 / 100000000000000 : ℝ)) (q := (1137689096729 / 50000000000000 : ℝ))
      (E := (cell12511 ⟨7, by decide⟩).energy) (xi := (67850297364739 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12511 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12511]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12511])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12511) (a := (83834163892123 / 100000000000000 : ℝ)) (b := (164670144957 / 100000000000000 : ℝ)) (q := (1137689096729 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12511])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12511])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12511]

theorem cert12511_8 : CellCertificate 12511 (111505898061113 / 1250000000000000 : ℝ) (1678885223514201 / 1000000000000000000 : ℝ) (67850297364739 / 2000000000000000 : ℝ)
    (cell12511 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · have h := gap_lower (n := 12511) (a := (41899651039399 / 50000000000000 : ℝ)) (b := (164670144957 / 100000000000000 : ℝ)) (q := (113769108427 / 5000000000000 : ℝ))
      (E := (cell12511 ⟨8, by decide⟩).energy) (xi := (67850297364739 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12511 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12511]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12511])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12511) (a := (41899651039399 / 50000000000000 : ℝ)) (b := (164670144957 / 100000000000000 : ℝ)) (q := (113769108427 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12511])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12511])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12511]

theorem cert12511_9 : CellCertificate 12511 (111505898061113 / 1250000000000000 : ℝ) (1678885223514201 / 1000000000000000000 : ℝ) (67850297364739 / 2000000000000000 : ℝ)
    (cell12511 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · have h := gap_lower (n := 12511) (a := (20941116258387 / 25000000000000 : ℝ)) (b := (164670144957 / 100000000000000 : ℝ)) (q := (455077228287 / 20000000000000 : ℝ))
      (E := (cell12511 ⟨9, by decide⟩).energy) (xi := (67850297364739 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12511 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12511]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12511])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12511) (a := (20941116258387 / 25000000000000 : ℝ)) (b := (164670144957 / 100000000000000 : ℝ)) (q := (455077228287 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12511])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12511])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12511]

theorem cert12511_10 : CellCertificate 12511 (111505898061113 / 1250000000000000 : ℝ) (1678885223514201 / 1000000000000000000 : ℝ) (67850297364739 / 2000000000000000 : ℝ)
    (cell12511 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · have h := gap_lower (n := 12511) (a := (8372965272101 / 10000000000000 : ℝ)) (b := (164670144957 / 100000000000000 : ℝ)) (q := (1137695088769 / 50000000000000 : ℝ))
      (E := (cell12511 ⟨10, by decide⟩).energy) (xi := (67850297364739 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12511 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12511]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12511])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12511) (a := (8372965272101 / 10000000000000 : ℝ)) (b := (164670144957 / 100000000000000 : ℝ)) (q := (1137695088769 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12511])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12511])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12511]

theorem cert12511_11 : CellCertificate 12511 (111505898061113 / 1250000000000000 : ℝ) (1678885223514201 / 1000000000000000000 : ℝ) (67850297364739 / 2000000000000000 : ℝ)
    (cell12511 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · have h := gap_lower (n := 12511) (a := (20923716276501 / 25000000000000 : ℝ)) (b := (164670144957 / 100000000000000 : ℝ)) (q := (455078833589 / 20000000000000 : ℝ))
      (E := (cell12511 ⟨11, by decide⟩).energy) (xi := (67850297364739 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12511 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12511]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12511])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12511) (a := (20923716276501 / 25000000000000 : ℝ)) (b := (164670144957 / 100000000000000 : ℝ)) (q := (455078833589 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12511])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12511])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12511]

theorem cert12511_12 : CellCertificate 12511 (111505898061113 / 1250000000000000 : ℝ) (1678885223514201 / 1000000000000000000 : ℝ) (67850297364739 / 2000000000000000 : ℝ)
    (cell12511 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · have h := gap_lower (n := 12511) (a := (16732020430707 / 20000000000000 : ℝ)) (b := (164670144957 / 100000000000000 : ℝ)) (q := (2275398177529 / 100000000000000 : ℝ))
      (E := (cell12511 ⟨12, by decide⟩).energy) (xi := (67850297364739 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12511 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12511]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12511])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12511) (a := (16732020430707 / 20000000000000 : ℝ)) (b := (164670144957 / 100000000000000 : ℝ)) (q := (2275398177529 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12511])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12511])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12511]

theorem cert12511_13 : CellCertificate 12511 (111505898061113 / 1250000000000000 : ℝ) (1678885223514201 / 1000000000000000000 : ℝ) (67850297364739 / 2000000000000000 : ℝ)
    (cell12511 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · have h := gap_lower (n := 12511) (a := (83625363828791 / 100000000000000 : ℝ)) (b := (164670144957 / 100000000000000 : ℝ)) (q := (35553158669 / 1562500000000 : ℝ))
      (E := (cell12511 ⟨13, by decide⟩).energy) (xi := (67850297364739 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12511 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12511]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12511])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12511) (a := (83625363828791 / 100000000000000 : ℝ)) (b := (164670144957 / 100000000000000 : ℝ)) (q := (35553158669 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12511])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12511])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12511]

theorem cert12511_14 : CellCertificate 12511 (111505898061113 / 1250000000000000 : ℝ) (1678885223514201 / 1000000000000000000 : ℝ) (67850297364739 / 2000000000000000 : ℝ)
    (cell12511 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · have h := gap_lower (n := 12511) (a := (83590650097141 / 100000000000000 : ℝ)) (b := (164670144957 / 100000000000000 : ℝ)) (q := (2275406164227 / 100000000000000 : ℝ))
      (E := (cell12511 ⟨14, by decide⟩).energy) (xi := (67850297364739 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12511 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12511]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12511])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12511) (a := (83590650097141 / 100000000000000 : ℝ)) (b := (164670144957 / 100000000000000 : ℝ)) (q := (2275406164227 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12511])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12511])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12511]

theorem cert12511_15 : CellCertificate 12511 (111505898061113 / 1250000000000000 : ℝ) (1678885223514201 / 1000000000000000000 : ℝ) (67850297364739 / 2000000000000000 : ℝ)
    (cell12511 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · have h := gap_lower (n := 12511) (a := (16711192184827 / 20000000000000 : ℝ)) (b := (164670144957 / 100000000000000 : ℝ)) (q := (455082030749 / 20000000000000 : ℝ))
      (E := (cell12511 ⟨15, by decide⟩).energy) (xi := (67850297364739 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12511 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12511]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12511])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12511) (a := (16711192184827 / 20000000000000 : ℝ)) (b := (164670144957 / 100000000000000 : ℝ)) (q := (455082030749 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12511])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12511])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12511]

theorem cert12511_16 : CellCertificate 12511 (111505898061113 / 1250000000000000 : ℝ) (1678885223514201 / 1000000000000000000 : ℝ) (67850297364739 / 2000000000000000 : ℝ)
    (cell12511 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · have h := gap_lower (n := 12511) (a := (167042592551 / 200000000000 : ℝ)) (b := (164670144957 / 100000000000000 : ℝ)) (q := (1137707064591 / 50000000000000 : ℝ))
      (E := (cell12511 ⟨16, by decide⟩).energy) (xi := (67850297364739 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12511 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12511]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12511])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12511) (a := (167042592551 / 200000000000 : ℝ)) (b := (164670144957 / 100000000000000 : ℝ)) (q := (1137707064591 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12511])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12511])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12511]

theorem cert12511_17 : CellCertificate 12511 (111505898061113 / 1250000000000000 : ℝ) (1678885223514201 / 1000000000000000000 : ℝ) (67850297364739 / 2000000000000000 : ℝ)
    (cell12511 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · have h := gap_lower (n := 12511) (a := (83486656117143 / 100000000000000 : ℝ)) (b := (164670144957 / 100000000000000 : ℝ)) (q := (568854538573 / 25000000000000 : ℝ))
      (E := (cell12511 ⟨17, by decide⟩).energy) (xi := (67850297364739 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12511 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12511]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12511])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12511) (a := (83486656117143 / 100000000000000 : ℝ)) (b := (164670144957 / 100000000000000 : ℝ)) (q := (568854538573 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12511])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12511])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12511]

theorem cert12511_18 : CellCertificate 12511 (111505898061113 / 1250000000000000 : ℝ) (1678885223514201 / 1000000000000000000 : ℝ) (67850297364739 / 2000000000000000 : ℝ)
    (cell12511 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · have h := gap_lower (n := 12511) (a := (83452040415147 / 100000000000000 : ℝ)) (b := (164670144957 / 100000000000000 : ℝ)) (q := (56885552951 / 2500000000000 : ℝ))
      (E := (cell12511 ⟨18, by decide⟩).energy) (xi := (67850297364739 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12511 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12511]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12511])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12511) (a := (83452040415147 / 100000000000000 : ℝ)) (b := (164670144957 / 100000000000000 : ℝ)) (q := (56885552951 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12511])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12511])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12511]

theorem cert12511_19 : CellCertificate 12511 (111505898061113 / 1250000000000000 : ℝ) (1678885223514201 / 1000000000000000000 : ℝ) (67850297364739 / 2000000000000000 : ℝ)
    (cell12511 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · have h := gap_lower (n := 12511) (a := (83417449135771 / 100000000000000 : ℝ)) (b := (164670144957 / 100000000000000 : ℝ)) (q := (2275426141907 / 100000000000000 : ℝ))
      (E := (cell12511 ⟨19, by decide⟩).energy) (xi := (67850297364739 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12511 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12511]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12511])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12511) (a := (83417449135771 / 100000000000000 : ℝ)) (b := (164670144957 / 100000000000000 : ℝ)) (q := (2275426141907 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12511])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12511])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12511]

theorem cert12512_0 : CellCertificate 12512 (892018433279809 / 10000000000000000 : ℝ) (167875099673047 / 100000000000000000 : ℝ) (339223687369131 / 10000000000000000 : ℝ)
    (cell12512 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · have h := gap_lower (n := 12512) (a := (84078877512291 / 100000000000000 : ℝ)) (b := (41164204411 / 25000000000000 : ℝ)) (q := (1137609899433 / 50000000000000 : ℝ))
      (E := (cell12512 ⟨0, by decide⟩).energy) (xi := (339223687369131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12512 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12512]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12512])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12512) (a := (84078877512291 / 100000000000000 : ℝ)) (b := (41164204411 / 25000000000000 : ℝ)) (q := (1137609899433 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12512])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12512])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12512]

theorem cert12512_1 : CellCertificate 12512 (892018433279809 / 10000000000000000 : ℝ) (167875099673047 / 100000000000000000 : ℝ) (339223687369131 / 10000000000000000 : ℝ)
    (cell12512 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · have h := gap_lower (n := 12512) (a := (42021920822003 / 50000000000000 : ℝ)) (b := (41164204411 / 25000000000000 : ℝ)) (q := (2275223798669 / 100000000000000 : ℝ))
      (E := (cell12512 ⟨1, by decide⟩).energy) (xi := (339223687369131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12512 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12512]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12512])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12512) (a := (42021920822003 / 50000000000000 : ℝ)) (b := (41164204411 / 25000000000000 : ℝ)) (q := (2275223798669 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12512])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12512])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12512]

theorem cert12512_2 : CellCertificate 12512 (892018433279809 / 10000000000000000 : ℝ) (167875099673047 / 100000000000000000 : ℝ) (339223687369131 / 10000000000000000 : ℝ)
    (cell12512 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · have h := gap_lower (n := 12512) (a := (84008830796163 / 100000000000000 : ℝ)) (b := (41164204411 / 25000000000000 : ℝ)) (q := (1137613897983 / 50000000000000 : ℝ))
      (E := (cell12512 ⟨2, by decide⟩).energy) (xi := (339223687369131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12512 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12512]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12512])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12512) (a := (84008830796163 / 100000000000000 : ℝ)) (b := (41164204411 / 25000000000000 : ℝ)) (q := (1137613897983 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12512])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12512])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12512]

theorem cert12512_3 : CellCertificate 12512 (892018433279809 / 10000000000000000 : ℝ) (167875099673047 / 100000000000000000 : ℝ) (339223687369131 / 10000000000000000 : ℝ)
    (cell12512 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · have h := gap_lower (n := 12512) (a := (20993461233017 / 25000000000000 : ℝ)) (b := (41164204411 / 25000000000000 : ℝ)) (q := (568807949999 / 25000000000000 : ℝ))
      (E := (cell12512 ⟨3, by decide⟩).energy) (xi := (339223687369131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12512 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12512]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12512])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12512) (a := (20993461233017 / 25000000000000 : ℝ)) (b := (41164204411 / 25000000000000 : ℝ)) (q := (568807949999 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12512])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12512])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12512]

theorem cert12512_4 : CellCertificate 12512 (892018433279809 / 10000000000000000 : ℝ) (167875099673047 / 100000000000000000 : ℝ) (339223687369131 / 10000000000000000 : ℝ)
    (cell12512 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · have h := gap_lower (n := 12512) (a := (10492360501903 / 12500000000000 : ℝ)) (b := (41164204411 / 25000000000000 : ℝ)) (q := (2275235819733 / 100000000000000 : ℝ))
      (E := (cell12512 ⟨4, by decide⟩).energy) (xi := (339223687369131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12512 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12512]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12512])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12512) (a := (10492360501903 / 12500000000000 : ℝ)) (b := (41164204411 / 25000000000000 : ℝ)) (q := (2275235819733 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12512])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12512])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12512]

theorem cert12512_5 : CellCertificate 12512 (892018433279809 / 10000000000000000 : ℝ) (167875099673047 / 100000000000000000 : ℝ) (339223687369131 / 10000000000000000 : ℝ)
    (cell12512 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · have h := gap_lower (n := 12512) (a := (83903948009323 / 100000000000000 : ℝ)) (b := (41164204411 / 25000000000000 : ℝ)) (q := (568809951497 / 25000000000000 : ℝ))
      (E := (cell12512 ⟨5, by decide⟩).energy) (xi := (339223687369131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12512 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12512]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12512])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12512) (a := (83903948009323 / 100000000000000 : ℝ)) (b := (41164204411 / 25000000000000 : ℝ)) (q := (568809951497 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12512])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12512])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12512]

theorem cert12512_6 : CellCertificate 12512 (892018433279809 / 10000000000000000 : ℝ) (167875099673047 / 100000000000000000 : ℝ) (339223687369131 / 10000000000000000 : ℝ)
    (cell12512 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · have h := gap_lower (n := 12512) (a := (83869036878251 / 100000000000000 : ℝ)) (b := (41164204411 / 25000000000000 : ℝ)) (q := (2275243767151 / 100000000000000 : ℝ))
      (E := (cell12512 ⟨6, by decide⟩).energy) (xi := (339223687369131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12512 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12512]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12512])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12512) (a := (83869036878251 / 100000000000000 : ℝ)) (b := (41164204411 / 25000000000000 : ℝ)) (q := (2275243767151 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12512])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12512])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12512]

theorem cert12512_7 : CellCertificate 12512 (892018433279809 / 10000000000000000 : ℝ) (167875099673047 / 100000000000000000 : ℝ) (339223687369131 / 10000000000000000 : ℝ)
    (cell12512 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · have h := gap_lower (n := 12512) (a := (83834150586083 / 100000000000000 : ℝ)) (b := (41164204411 / 25000000000000 : ℝ)) (q := (568811942327 / 25000000000000 : ℝ))
      (E := (cell12512 ⟨7, by decide⟩).energy) (xi := (339223687369131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12512 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12512]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12512])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12512) (a := (83834150586083 / 100000000000000 : ℝ)) (b := (41164204411 / 25000000000000 : ℝ)) (q := (568811942327 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12512])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12512])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12512]

theorem cert12512_8 : CellCertificate 12512 (892018433279809 / 10000000000000000 : ℝ) (167875099673047 / 100000000000000000 : ℝ) (339223687369131 / 10000000000000000 : ℝ)
    (cell12512 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · have h := gap_lower (n := 12512) (a := (83799289097083 / 100000000000000 : ℝ)) (b := (41164204411 / 25000000000000 : ℝ)) (q := (2275251762431 / 100000000000000 : ℝ))
      (E := (cell12512 ⟨8, by decide⟩).energy) (xi := (339223687369131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12512 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12512]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12512])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12512) (a := (83799289097083 / 100000000000000 : ℝ)) (b := (41164204411 / 25000000000000 : ℝ)) (q := (2275251762431 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12512])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12512])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12512]

theorem cert12512_9 : CellCertificate 12512 (892018433279809 / 10000000000000000 : ℝ) (167875099673047 / 100000000000000000 : ℝ) (339223687369131 / 10000000000000000 : ℝ)
    (cell12512 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · have h := gap_lower (n := 12512) (a := (837644523757 / 1000000000000 : ℝ)) (b := (41164204411 / 25000000000000 : ℝ)) (q := (2275255812147 / 100000000000000 : ℝ))
      (E := (cell12512 ⟨9, by decide⟩).energy) (xi := (339223687369131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12512 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12512]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12512])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12512) (a := (837644523757 / 1000000000000 : ℝ)) (b := (41164204411 / 25000000000000 : ℝ)) (q := (2275255812147 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12512])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12512])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12512]

theorem cert12512_10 : CellCertificate 12512 (892018433279809 / 10000000000000000 : ℝ) (167875099673047 / 100000000000000000 : ℝ) (339223687369131 / 10000000000000000 : ℝ)
    (cell12512 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · have h := gap_lower (n := 12512) (a := (83729640386573 / 100000000000000 : ℝ)) (b := (41164204411 / 25000000000000 : ℝ)) (q := (1137629904923 / 50000000000000 : ℝ))
      (E := (cell12512 ⟨10, by decide⟩).energy) (xi := (339223687369131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12512 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12512]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12512])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12512) (a := (83729640386573 / 100000000000000 : ℝ)) (b := (41164204411 / 25000000000000 : ℝ)) (q := (1137629904923 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12512])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12512])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12512]

theorem cert12512_11 : CellCertificate 12512 (892018433279809 / 10000000000000000 : ℝ) (167875099673047 / 100000000000000000 : ℝ) (339223687369131 / 10000000000000000 : ℝ)
    (cell12512 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · have h := gap_lower (n := 12512) (a := (83694853094523 / 100000000000000 : ℝ)) (b := (41164204411 / 25000000000000 : ℝ)) (q := (113763188129 / 5000000000000 : ℝ))
      (E := (cell12512 ⟨11, by decide⟩).energy) (xi := (339223687369131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12512 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12512]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12512])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12512) (a := (83694853094523 / 100000000000000 : ℝ)) (b := (41164204411 / 25000000000000 : ℝ)) (q := (113763188129 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12512])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12512])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12512]

theorem cert12512_12 : CellCertificate 12512 (892018433279809 / 10000000000000000 : ℝ) (167875099673047 / 100000000000000000 : ℝ) (339223687369131 / 10000000000000000 : ℝ)
    (cell12512 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · have h := gap_lower (n := 12512) (a := (20915022616139 / 25000000000000 : ℝ)) (b := (41164204411 / 25000000000000 : ℝ)) (q := (568816948323 / 25000000000000 : ℝ))
      (E := (cell12512 ⟨12, by decide⟩).energy) (xi := (339223687369131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12512 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12512]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12512])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12512) (a := (20915022616139 / 25000000000000 : ℝ)) (b := (41164204411 / 25000000000000 : ℝ)) (q := (568816948323 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12512])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12512])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12512]

theorem cert12512_13 : CellCertificate 12512 (892018433279809 / 10000000000000000 : ℝ) (167875099673047 / 100000000000000000 : ℝ) (339223687369131 / 10000000000000000 : ℝ)
    (cell12512 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · have h := gap_lower (n := 12512) (a := (41812676230931 / 50000000000000 : ℝ)) (b := (41164204411 / 25000000000000 : ℝ)) (q := (14220448703 / 625000000000 : ℝ))
      (E := (cell12512 ⟨13, by decide⟩).energy) (xi := (339223687369131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12512 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12512]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12512])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12512) (a := (41812676230931 / 50000000000000 : ℝ)) (b := (41164204411 / 25000000000000 : ℝ)) (q := (14220448703 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12512])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12512])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12512]

theorem cert12512_14 : CellCertificate 12512 (892018433279809 / 10000000000000000 : ℝ) (167875099673047 / 100000000000000000 : ℝ) (339223687369131 / 10000000000000000 : ℝ)
    (cell12512 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · have h := gap_lower (n := 12512) (a := (83590639051809 / 100000000000000 : ℝ)) (b := (41164204411 / 25000000000000 : ℝ)) (q := (142204735403 / 6250000000000 : ℝ))
      (E := (cell12512 ⟨14, by decide⟩).energy) (xi := (339223687369131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12512 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12512]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12512])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12512) (a := (83590639051809 / 100000000000000 : ℝ)) (b := (41164204411 / 25000000000000 : ℝ)) (q := (142204735403 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12512])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12512])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12512]

theorem cert12512_15 : CellCertificate 12512 (892018433279809 / 10000000000000000 : ℝ) (167875099673047 / 100000000000000000 : ℝ) (339223687369131 / 10000000000000000 : ℝ)
    (cell12512 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · have h := gap_lower (n := 12512) (a := (20888987549987 / 25000000000000 : ℝ)) (b := (41164204411 / 25000000000000 : ℝ)) (q := (2275279779393 / 100000000000000 : ℝ))
      (E := (cell12512 ⟨15, by decide⟩).energy) (xi := (339223687369131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12512 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12512]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12512])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12512) (a := (20888987549987 / 25000000000000 : ℝ)) (b := (41164204411 / 25000000000000 : ℝ)) (q := (2275279779393 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12512])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12512])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12512]

theorem cert12512_16 : CellCertificate 12512 (892018433279809 / 10000000000000000 : ℝ) (167875099673047 / 100000000000000000 : ℝ) (339223687369131 / 10000000000000000 : ℝ)
    (cell12512 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · have h := gap_lower (n := 12512) (a := (83521285872009 / 100000000000000 : ℝ)) (b := (41164204411 / 25000000000000 : ℝ)) (q := (568820944757 / 25000000000000 : ℝ))
      (E := (cell12512 ⟨16, by decide⟩).energy) (xi := (339223687369131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12512 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12512]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12512])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12512) (a := (83521285872009 / 100000000000000 : ℝ)) (b := (41164204411 / 25000000000000 : ℝ)) (q := (568820944757 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12512])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12512])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12512]

theorem cert12512_17 : CellCertificate 12512 (892018433279809 / 10000000000000000 : ℝ) (167875099673047 / 100000000000000000 : ℝ) (339223687369131 / 10000000000000000 : ℝ)
    (cell12512 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · have h := gap_lower (n := 12512) (a := (41743323016949 / 50000000000000 : ℝ)) (b := (41164204411 / 25000000000000 : ℝ)) (q := (1137643885459 / 50000000000000 : ℝ))
      (E := (cell12512 ⟨17, by decide⟩).energy) (xi := (339223687369131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12512 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12512]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12512])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12512) (a := (41743323016949 / 50000000000000 : ℝ)) (b := (41164204411 / 25000000000000 : ℝ)) (q := (1137643885459 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12512])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12512])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12512]

theorem cert12512_18 : CellCertificate 12512 (892018433279809 / 10000000000000000 : ℝ) (167875099673047 / 100000000000000000 : ℝ) (339223687369131 / 10000000000000000 : ℝ)
    (cell12512 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · have h := gap_lower (n := 12512) (a := (83452030651699 / 100000000000000 : ℝ)) (b := (41164204411 / 25000000000000 : ℝ)) (q := (8887858439 / 390625000000 : ℝ))
      (E := (cell12512 ⟨18, by decide⟩).energy) (xi := (339223687369131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12512 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12512]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12512])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12512) (a := (83452030651699 / 100000000000000 : ℝ)) (b := (41164204411 / 25000000000000 : ℝ)) (q := (8887858439 / 390625000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12512])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12512])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12512]

theorem cert12512_19 : CellCertificate 12512 (892018433279809 / 10000000000000000 : ℝ) (167875099673047 / 100000000000000000 : ℝ) (339223687369131 / 10000000000000000 : ℝ)
    (cell12512 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · have h := gap_lower (n := 12512) (a := (83417439691673 / 100000000000000 : ℝ)) (b := (41164204411 / 25000000000000 : ℝ)) (q := (1137647876251 / 50000000000000 : ℝ))
      (E := (cell12512 ⟨19, by decide⟩).energy) (xi := (339223687369131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12512 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12512]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12512])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12512) (a := (83417439691673 / 100000000000000 : ℝ)) (b := (41164204411 / 25000000000000 : ℝ)) (q := (1137647876251 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12512])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12512])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12512]

theorem cert12513_0 : CellCertificate 12513 (111498710811199 / 1250000000000000 : ℝ) (1678616791407869 / 1000000000000000000 : ℝ) (84798973138183 / 2500000000000000 : ℝ)
    (cell12513 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · have h := gap_lower (n := 12513) (a := (16815772385119 / 20000000000000 : ℝ)) (b := (164643492509 / 100000000000000 : ℝ)) (q := (455017899303 / 20000000000000 : ℝ))
      (E := (cell12513 ⟨0, by decide⟩).energy) (xi := (84798973138183 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12513 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12513]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12513])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12513) (a := (16815772385119 / 20000000000000 : ℝ)) (b := (164643492509 / 100000000000000 : ℝ)) (q := (455017899303 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12513])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12513])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12513]

theorem cert12513_1 : CellCertificate 12513 (111498710811199 / 1250000000000000 : ℝ) (1678616791407869 / 1000000000000000000 : ℝ) (84798973138183 / 2500000000000000 : ℝ)
    (cell12513 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · have h := gap_lower (n := 12513) (a := (84043826384821 / 100000000000000 : ℝ)) (b := (164643492509 / 100000000000000 : ℝ)) (q := (1421933407 / 62500000000 : ℝ))
      (E := (cell12513 ⟨1, by decide⟩).energy) (xi := (84798973138183 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12513 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12513]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12513])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12513) (a := (84043826384821 / 100000000000000 : ℝ)) (b := (164643492509 / 100000000000000 : ℝ)) (q := (1421933407 / 62500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12513])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12513])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12513]

theorem cert12513_2 : CellCertificate 12513 (111498710811199 / 1250000000000000 : ℝ) (1678616791407869 / 1000000000000000000 : ℝ) (84798973138183 / 2500000000000000 : ℝ)
    (cell12513 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · have h := gap_lower (n := 12513) (a := (3360352634561 / 4000000000000 : ℝ)) (b := (164643492509 / 100000000000000 : ℝ)) (q := (2275097461957 / 100000000000000 : ℝ))
      (E := (cell12513 ⟨2, by decide⟩).energy) (xi := (84798973138183 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12513 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12513]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12513])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12513) (a := (3360352634561 / 4000000000000 : ℝ)) (b := (164643492509 / 100000000000000 : ℝ)) (q := (2275097461957 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12513])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12513])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12513]

theorem cert12513_3 : CellCertificate 12513 (111498710811199 / 1250000000000000 : ℝ) (1678616791407869 / 1000000000000000000 : ℝ) (84798973138183 / 2500000000000000 : ℝ)
    (cell12513 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · have h := gap_lower (n := 12513) (a := (41986915163257 / 50000000000000 : ℝ)) (b := (164643492509 / 100000000000000 : ℝ)) (q := (2275101480231 / 100000000000000 : ℝ))
      (E := (cell12513 ⟨3, by decide⟩).energy) (xi := (84798973138183 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12513 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12513]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12513])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12513) (a := (41986915163257 / 50000000000000 : ℝ)) (b := (164643492509 / 100000000000000 : ℝ)) (q := (2275101480231 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12513])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12513])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12513]

theorem cert12513_4 : CellCertificate 12513 (111498710811199 / 1250000000000000 : ℝ) (1678616791407869 / 1000000000000000000 : ℝ) (84798973138183 / 2500000000000000 : ℝ)
    (cell12513 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · have h := gap_lower (n := 12513) (a := (5246179358487 / 6250000000000 : ℝ)) (b := (164643492509 / 100000000000000 : ℝ)) (q := (284388182139 / 12500000000000 : ℝ))
      (E := (cell12513 ⟨4, by decide⟩).energy) (xi := (84798973138183 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12513 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12513]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12513])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12513) (a := (5246179358487 / 6250000000000 : ℝ)) (b := (164643492509 / 100000000000000 : ℝ)) (q := (284388182139 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12513])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12513])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12513]

theorem cert12513_5 : CellCertificate 12513 (111498710811199 / 1250000000000000 : ℝ) (1678616791407869 / 1000000000000000000 : ℝ) (84798973138183 / 2500000000000000 : ℝ)
    (cell12513 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · have h := gap_lower (n := 12513) (a := (655499484809 / 781250000000 : ℝ)) (b := (164643492509 / 100000000000000 : ℝ)) (q := (1137554729577 / 50000000000000 : ℝ))
      (E := (cell12513 ⟨5, by decide⟩).energy) (xi := (84798973138183 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12513 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12513]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12513])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12513) (a := (655499484809 / 781250000000 : ℝ)) (b := (164643492509 / 100000000000000 : ℝ)) (q := (1137554729577 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12513])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12513])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12513]

theorem cert12513_6 : CellCertificate 12513 (111498710811199 / 1250000000000000 : ℝ) (1678616791407869 / 1000000000000000000 : ℝ) (84798973138183 / 2500000000000000 : ℝ)
    (cell12513 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · have h := gap_lower (n := 12513) (a := (41934511624841 / 50000000000000 : ℝ)) (b := (164643492509 / 100000000000000 : ℝ)) (q := (568778359221 / 25000000000000 : ℝ))
      (E := (cell12513 ⟨6, by decide⟩).energy) (xi := (84798973138183 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12513 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12513]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12513])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12513) (a := (41934511624841 / 50000000000000 : ℝ)) (b := (164643492509 / 100000000000000 : ℝ)) (q := (568778359221 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12513])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12513])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12513]

theorem cert12513_7 : CellCertificate 12513 (111498710811199 / 1250000000000000 : ℝ) (1678616791407869 / 1000000000000000000 : ℝ) (84798973138183 / 2500000000000000 : ℝ)
    (cell12513 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · have h := gap_lower (n := 12513) (a := (5239633580141 / 6250000000000 : ℝ)) (b := (164643492509 / 100000000000000 : ℝ)) (q := (2275117456391 / 100000000000000 : ℝ))
      (E := (cell12513 ⟨7, by decide⟩).energy) (xi := (84798973138183 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12513 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12513]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12513])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12513) (a := (5239633580141 / 6250000000000 : ℝ)) (b := (164643492509 / 100000000000000 : ℝ)) (q := (2275117456391 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12513])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12513])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12513]

theorem cert12513_8 : CellCertificate 12513 (111498710811199 / 1250000000000000 : ℝ) (1678616791407869 / 1000000000000000000 : ℝ) (84798973138183 / 2500000000000000 : ℝ)
    (cell12513 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · have h := gap_lower (n := 12513) (a := (4189963805877 / 5000000000000 : ℝ)) (b := (164643492509 / 100000000000000 : ℝ)) (q := (2275121467643 / 100000000000000 : ℝ))
      (E := (cell12513 ⟨8, by decide⟩).energy) (xi := (84798973138183 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12513 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12513]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12513])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12513) (a := (4189963805877 / 5000000000000 : ℝ)) (b := (164643492509 / 100000000000000 : ℝ)) (q := (2275121467643 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12513])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12513])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12513]

theorem cert12513_9 : CellCertificate 12513 (111498710811199 / 1250000000000000 : ℝ) (1678616791407869 / 1000000000000000000 : ℝ) (84798973138183 / 2500000000000000 : ℝ)
    (cell12513 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · have h := gap_lower (n := 12513) (a := (16752887943997 / 20000000000000 : ℝ)) (b := (164643492509 / 100000000000000 : ℝ)) (q := (455025095653 / 20000000000000 : ℝ))
      (E := (cell12513 ⟨9, by decide⟩).energy) (xi := (84798973138183 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12513 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12513]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12513])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12513) (a := (16752887943997 / 20000000000000 : ℝ)) (b := (164643492509 / 100000000000000 : ℝ)) (q := (455025095653 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12513])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12513])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12513]

theorem cert12513_10 : CellCertificate 12513 (111498710811199 / 1250000000000000 : ℝ) (1678616791407869 / 1000000000000000000 : ℝ) (84798973138183 / 2500000000000000 : ℝ)
    (cell12513 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · have h := gap_lower (n := 12513) (a := (83729628054229 / 100000000000000 : ℝ)) (b := (164643492509 / 100000000000000 : ℝ)) (q := (1137564718801 / 50000000000000 : ℝ))
      (E := (cell12513 ⟨10, by decide⟩).energy) (xi := (84798973138183 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12513 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12513]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12513])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12513) (a := (83729628054229 / 100000000000000 : ℝ)) (b := (164643492509 / 100000000000000 : ℝ)) (q := (1137564718801 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12513])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12513])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12513]

theorem cert12513_11 : CellCertificate 12513 (111498710811199 / 1250000000000000 : ℝ) (1678616791407869 / 1000000000000000000 : ℝ) (84798973138183 / 2500000000000000 : ℝ)
    (cell12513 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · have h := gap_lower (n := 12513) (a := (10461855135637 / 12500000000000 : ℝ)) (b := (164643492509 / 100000000000000 : ℝ)) (q := (2275133468799 / 100000000000000 : ℝ))
      (E := (cell12513 ⟨11, by decide⟩).energy) (xi := (84798973138183 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12513 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12513]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12513])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12513) (a := (10461855135637 / 12500000000000 : ℝ)) (b := (164643492509 / 100000000000000 : ℝ)) (q := (2275133468799 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12513])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12513])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12513]

theorem cert12513_12 : CellCertificate 12513 (111498710811199 / 1250000000000000 : ℝ) (1678616791407869 / 1000000000000000000 : ℝ) (84798973138183 / 2500000000000000 : ℝ)
    (cell12513 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · have h := gap_lower (n := 12513) (a := (83660078777591 / 100000000000000 : ℝ)) (b := (164643492509 / 100000000000000 : ℝ)) (q := (1137568731327 / 50000000000000 : ℝ))
      (E := (cell12513 ⟨12, by decide⟩).energy) (xi := (84798973138183 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12513 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12513]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12513])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12513) (a := (83660078777591 / 100000000000000 : ℝ)) (b := (164643492509 / 100000000000000 : ℝ)) (q := (1137568731327 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12513])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12513])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12513]

theorem cert12513_13 : CellCertificate 12513 (111498710811199 / 1250000000000000 : ℝ) (1678616791407869 / 1000000000000000000 : ℝ) (84798973138183 / 2500000000000000 : ℝ)
    (cell12513 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · have h := gap_lower (n := 12513) (a := (41812670548453 / 50000000000000 : ℝ)) (b := (164643492509 / 100000000000000 : ℝ)) (q := (2275141425713 / 100000000000000 : ℝ))
      (E := (cell12513 ⟨13, by decide⟩).energy) (xi := (84798973138183 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12513 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12513]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12513])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12513) (a := (41812670548453 / 50000000000000 : ℝ)) (b := (164643492509 / 100000000000000 : ℝ)) (q := (2275141425713 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12513])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12513])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12513]

theorem cert12513_14 : CellCertificate 12513 (111498710811199 / 1250000000000000 : ℝ) (1678616791407869 / 1000000000000000000 : ℝ) (84798973138183 / 2500000000000000 : ℝ)
    (cell12513 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · have h := gap_lower (n := 12513) (a := (83590628008411 / 100000000000000 : ℝ)) (b := (164643492509 / 100000000000000 : ℝ)) (q := (1137572711199 / 50000000000000 : ℝ))
      (E := (cell12513 ⟨14, by decide⟩).energy) (xi := (84798973138183 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12513 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12513]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12513])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12513) (a := (83590628008411 / 100000000000000 : ℝ)) (b := (164643492509 / 100000000000000 : ℝ)) (q := (1137572711199 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12513])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12513])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12513]

theorem cert12513_15 : CellCertificate 12513 (111498710811199 / 1250000000000000 : ℝ) (1678616791407869 / 1000000000000000000 : ℝ) (84798973138183 / 2500000000000000 : ℝ)
    (cell12513 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · have h := gap_lower (n := 12513) (a := (10444492434707 / 12500000000000 : ℝ)) (b := (164643492509 / 100000000000000 : ℝ)) (q := (1137574729417 / 50000000000000 : ℝ))
      (E := (cell12513 ⟨15, by decide⟩).energy) (xi := (84798973138183 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12513 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12513]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12513])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12513) (a := (10444492434707 / 12500000000000 : ℝ)) (b := (164643492509 / 100000000000000 : ℝ)) (q := (1137574729417 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12513])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12513])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12513]

theorem cert12513_16 : CellCertificate 12513 (111498710811199 / 1250000000000000 : ℝ) (1678616791407869 / 1000000000000000000 : ℝ) (84798973138183 / 2500000000000000 : ℝ)
    (cell12513 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · have h := gap_lower (n := 12513) (a := (20880318867593 / 25000000000000 : ℝ)) (b := (164643492509 / 100000000000000 : ℝ)) (q := (1137576712283 / 50000000000000 : ℝ))
      (E := (cell12513 ⟨16, by decide⟩).energy) (xi := (84798973138183 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12513 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12513]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12513])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12513) (a := (20880318867593 / 25000000000000 : ℝ)) (b := (164643492509 / 100000000000000 : ℝ)) (q := (1137576712283 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12513])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12513])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12513]

theorem cert12513_17 : CellCertificate 12513 (111498710811199 / 1250000000000000 : ℝ) (1678616791407869 / 1000000000000000000 : ℝ) (84798973138183 / 2500000000000000 : ℝ)
    (cell12513 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · have h := gap_lower (n := 12513) (a := (83486635952467 / 100000000000000 : ℝ)) (b := (164643492509 / 100000000000000 : ℝ)) (q := (2275157441467 / 100000000000000 : ℝ))
      (E := (cell12513 ⟨17, by decide⟩).energy) (xi := (84798973138183 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12513 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12513]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12513])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12513) (a := (83486635952467 / 100000000000000 : ℝ)) (b := (164643492509 / 100000000000000 : ℝ)) (q := (2275157441467 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12513])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12513])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12513]

theorem cert12513_18 : CellCertificate 12513 (111498710811199 / 1250000000000000 : ℝ) (1678616791407869 / 1000000000000000000 : ℝ) (84798973138183 / 2500000000000000 : ℝ)
    (cell12513 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · have h := gap_lower (n := 12513) (a := (83452020890027 / 100000000000000 : ℝ)) (b := (164643492509 / 100000000000000 : ℝ)) (q := (2275161456713 / 100000000000000 : ℝ))
      (E := (cell12513 ⟨18, by decide⟩).energy) (xi := (84798973138183 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12513 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12513]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12513])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12513) (a := (83452020890027 / 100000000000000 : ℝ)) (b := (164643492509 / 100000000000000 : ℝ)) (q := (2275161456713 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12513])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12513])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12513]

theorem cert12513_19 : CellCertificate 12513 (111498710811199 / 1250000000000000 : ℝ) (1678616791407869 / 1000000000000000000 : ℝ) (84798973138183 / 2500000000000000 : ℝ)
    (cell12513 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · have h := gap_lower (n := 12513) (a := (83417430249311 / 100000000000000 : ℝ)) (b := (164643492509 / 100000000000000 : ℝ)) (q := (1137582708573 / 50000000000000 : ℝ))
      (E := (cell12513 ⟨19, by decide⟩).energy) (xi := (84798973138183 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12513 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12513]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12513])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12513) (a := (83417430249311 / 100000000000000 : ℝ)) (b := (164643492509 / 100000000000000 : ℝ)) (q := (1137582708573 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12513])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12513])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12513]

theorem cert12514_0 : CellCertificate 12514 (178392188823437 / 2000000000000000 : ℝ) (419620651885313 / 250000000000000000 : ℝ) (339168102373217 / 10000000000000000 : ℝ)
    (cell12514 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · have h := gap_lower (n := 12514) (a := (84078846341393 / 100000000000000 : ℝ)) (b := (3292603391 / 2000000000000 : ℝ)) (q := (2274959189201 / 100000000000000 : ℝ))
      (E := (cell12514 ⟨0, by decide⟩).energy) (xi := (339168102373217 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12514 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12514]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12514])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12514) (a := (84078846341393 / 100000000000000 : ℝ)) (b := (3292603391 / 2000000000000 : ℝ)) (q := (2274959189201 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12514])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12514])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12514]

theorem cert12514_1 : CellCertificate 12514 (178392188823437 / 2000000000000000 : ℝ) (419620651885313 / 250000000000000000 : ℝ) (339168102373217 / 10000000000000000 : ℝ)
    (cell12514 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · have h := gap_lower (n := 12514) (a := (8404381112809 / 10000000000000 : ℝ)) (b := (3292603391 / 2000000000000 : ℝ)) (q := (2274963214439 / 100000000000000 : ℝ))
      (E := (cell12514 ⟨1, by decide⟩).energy) (xi := (339168102373217 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12514 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12514]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12514])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12514) (a := (8404381112809 / 10000000000000 : ℝ)) (b := (3292603391 / 2000000000000 : ℝ)) (q := (2274963214439 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12514])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12514])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12514]

theorem cert12514_2 : CellCertificate 12514 (178392188823437 / 2000000000000000 : ℝ) (419620651885313 / 250000000000000000 : ℝ) (339168102373217 / 10000000000000000 : ℝ)
    (cell12514 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · have h := gap_lower (n := 12514) (a := (840088009343 / 1000000000000 : ℝ)) (b := (3292603391 / 2000000000000 : ℝ)) (q := (2274967180907 / 100000000000000 : ℝ))
      (E := (cell12514 ⟨2, by decide⟩).energy) (xi := (339168102373217 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12514 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12514]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12514])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12514) (a := (840088009343 / 1000000000000 : ℝ)) (b := (3292603391 / 2000000000000 : ℝ)) (q := (2274967180907 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12514])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12514])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12514]

theorem cert12514_3 : CellCertificate 12514 (178392188823437 / 2000000000000000 : ℝ) (419620651885313 / 250000000000000000 : ℝ) (339168102373217 / 10000000000000000 : ℝ)
    (cell12514 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · have h := gap_lower (n := 12514) (a := (83973815723333 / 100000000000000 : ℝ)) (b := (3292603391 / 2000000000000 : ℝ)) (q := (227497121349 / 10000000000000 : ℝ))
      (E := (cell12514 ⟨3, by decide⟩).energy) (xi := (339168102373217 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12514 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12514]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12514])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12514) (a := (83973815723333 / 100000000000000 : ℝ)) (b := (3292603391 / 2000000000000 : ℝ)) (q := (227497121349 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12514])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12514])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12514]

theorem cert12514_4 : CellCertificate 12514 (178392188823437 / 2000000000000000 : ℝ) (419620651885313 / 250000000000000000 : ℝ) (339168102373217 / 10000000000000000 : ℝ)
    (cell12514 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · have h := gap_lower (n := 12514) (a := (83938855458693 / 100000000000000 : ℝ)) (b := (3292603391 / 2000000000000 : ℝ)) (q := (1137487602731 / 50000000000000 : ℝ))
      (E := (cell12514 ⟨4, by decide⟩).energy) (xi := (339168102373217 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12514 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12514]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12514])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12514) (a := (83938855458693 / 100000000000000 : ℝ)) (b := (3292603391 / 2000000000000 : ℝ)) (q := (1137487602731 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12514])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12514])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12514]

theorem cert12514_5 : CellCertificate 12514 (178392188823437 / 2000000000000000 : ℝ) (419620651885313 / 250000000000000000 : ℝ) (339168102373217 / 10000000000000000 : ℝ)
    (cell12514 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · have h := gap_lower (n := 12514) (a := (41951960052037 / 50000000000000 : ℝ)) (b := (3292603391 / 2000000000000 : ℝ)) (q := (2274979165471 / 100000000000000 : ℝ))
      (E := (cell12514 ⟨5, by decide⟩).energy) (xi := (339168102373217 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12514 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12514]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12514])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12514) (a := (41951960052037 / 50000000000000 : ℝ)) (b := (3292603391 / 2000000000000 : ℝ)) (q := (2274979165471 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12514])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12514])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12514]

theorem cert12514_6 : CellCertificate 12514 (178392188823437 / 2000000000000000 : ℝ) (419620651885313 / 250000000000000000 : ℝ) (339168102373217 / 10000000000000000 : ℝ)
    (cell12514 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · have h := gap_lower (n := 12514) (a := (16773801924673 / 20000000000000 : ℝ)) (b := (3292603391 / 2000000000000 : ℝ)) (q := (454996631967 / 20000000000000 : ℝ))
      (E := (cell12514 ⟨6, by decide⟩).energy) (xi := (339168102373217 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12514 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12514]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12514])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12514) (a := (16773801924673 / 20000000000000 : ℝ)) (b := (3292603391 / 2000000000000 : ℝ)) (q := (454996631967 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12514])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12514])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12514]

theorem cert12514_7 : CellCertificate 12514 (178392188823437 / 2000000000000000 : ℝ) (419620651885313 / 250000000000000000 : ℝ) (339168102373217 / 10000000000000000 : ℝ)
    (cell12514 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · have h := gap_lower (n := 12514) (a := (41917061990321 / 50000000000000 : ℝ)) (b := (3292603391 / 2000000000000 : ℝ)) (q := (454997439351 / 20000000000000 : ℝ))
      (E := (cell12514 ⟨7, by decide⟩).energy) (xi := (339168102373217 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12514 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12514]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12514])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12514) (a := (41917061990321 / 50000000000000 : ℝ)) (b := (3292603391 / 2000000000000 : ℝ)) (q := (454997439351 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12514])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12514])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12514]

theorem cert12514_8 : CellCertificate 12514 (178392188823437 / 2000000000000000 : ℝ) (419620651885313 / 250000000000000000 : ℝ) (339168102373217 / 10000000000000000 : ℝ)
    (cell12514 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · have h := gap_lower (n := 12514) (a := (83799263140169 / 100000000000000 : ℝ)) (b := (3292603391 / 2000000000000 : ℝ)) (q := (71093474007 / 3125000000000 : ℝ))
      (E := (cell12514 ⟨8, by decide⟩).energy) (xi := (339168102373217 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12514 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12514]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12514])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12514) (a := (83799263140169 / 100000000000000 : ℝ)) (b := (3292603391 / 2000000000000 : ℝ)) (q := (71093474007 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12514])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12514])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12514]

theorem cert12514_9 : CellCertificate 12514 (178392188823437 / 2000000000000000 : ℝ) (419620651885313 / 250000000000000000 : ℝ) (339168102373217 / 10000000000000000 : ℝ)
    (cell12514 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · have h := gap_lower (n := 12514) (a := (41882213533201 / 50000000000000 : ℝ)) (b := (3292603391 / 2000000000000 : ℝ)) (q := (2274995197793 / 100000000000000 : ℝ))
      (E := (cell12514 ⟨9, by decide⟩).energy) (xi := (339168102373217 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12514 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12514]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12514])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12514) (a := (41882213533201 / 50000000000000 : ℝ)) (b := (3292603391 / 2000000000000 : ℝ)) (q := (2274995197793 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12514])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12514])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12514]

theorem cert12514_10 : CellCertificate 12514 (178392188823437 / 2000000000000000 : ℝ) (419620651885313 / 250000000000000000 : ℝ) (339168102373217 / 10000000000000000 : ℝ)
    (cell12514 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · have h := gap_lower (n := 12514) (a := (41864807861989 / 50000000000000 : ℝ)) (b := (3292603391 / 2000000000000 : ℝ)) (q := (284374897107 / 12500000000000 : ℝ))
      (E := (cell12514 ⟨10, by decide⟩).energy) (xi := (339168102373217 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12514 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12514]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12514])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12514) (a := (41864807861989 / 50000000000000 : ℝ)) (b := (3292603391 / 2000000000000 : ℝ)) (q := (284374897107 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12514])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12514])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12514]

theorem cert12514_11 : CellCertificate 12514 (178392188823437 / 2000000000000000 : ℝ) (419620651885313 / 250000000000000000 : ℝ) (339168102373217 / 10000000000000000 : ℝ)
    (cell12514 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · have h := gap_lower (n := 12514) (a := (83694829077721 / 100000000000000 : ℝ)) (b := (3292603391 / 2000000000000 : ℝ)) (q := (2275003170509 / 100000000000000 : ℝ))
      (E := (cell12514 ⟨11, by decide⟩).energy) (xi := (339168102373217 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12514 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12514]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12514])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12514) (a := (83694829077721 / 100000000000000 : ℝ)) (b := (3292603391 / 2000000000000 : ℝ)) (q := (2275003170509 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12514])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12514])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12514]

theorem cert12514_12 : CellCertificate 12514 (178392188823437 / 2000000000000000 : ℝ) (419620651885313 / 250000000000000000 : ℝ) (339168102373217 / 10000000000000000 : ℝ)
    (cell12514 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · have h := gap_lower (n := 12514) (a := (83660067092639 / 100000000000000 : ℝ)) (b := (3292603391 / 2000000000000 : ℝ)) (q := (2275007185619 / 100000000000000 : ℝ))
      (E := (cell12514 ⟨12, by decide⟩).energy) (xi := (339168102373217 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12514 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12514]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12514])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12514) (a := (83660067092639 / 100000000000000 : ℝ)) (b := (3292603391 / 2000000000000 : ℝ)) (q := (2275007185619 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12514])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12514])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12514]

theorem cert12514_13 : CellCertificate 12514 (178392188823437 / 2000000000000000 : ℝ) (419620651885313 / 250000000000000000 : ℝ) (339168102373217 / 10000000000000000 : ℝ)
    (cell12514 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · have h := gap_lower (n := 12514) (a := (20906332433481 / 25000000000000 : ℝ)) (b := (3292603391 / 2000000000000 : ℝ)) (q := (2275011170709 / 100000000000000 : ℝ))
      (E := (cell12514 ⟨13, by decide⟩).energy) (xi := (339168102373217 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12514 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12514]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12514])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12514) (a := (20906332433481 / 25000000000000 : ℝ)) (b := (3292603391 / 2000000000000 : ℝ)) (q := (2275011170709 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12514])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12514])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12514]

theorem cert12514_14 : CellCertificate 12514 (178392188823437 / 2000000000000000 : ℝ) (419620651885313 / 250000000000000000 : ℝ) (339168102373217 / 10000000000000000 : ℝ)
    (cell12514 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · have h := gap_lower (n := 12514) (a := (41795308483473 / 50000000000000 : ℝ)) (b := (3292603391 / 2000000000000 : ℝ)) (q := (28437689151 / 1250000000000 : ℝ))
      (E := (cell12514 ⟨14, by decide⟩).energy) (xi := (339168102373217 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12514 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12514]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12514])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12514) (a := (41795308483473 / 50000000000000 : ℝ)) (b := (3292603391 / 2000000000000 : ℝ)) (q := (28437689151 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12514])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12514])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12514]

theorem cert12514_15 : CellCertificate 12514 (178392188823437 / 2000000000000000 : ℝ) (419620651885313 / 250000000000000000 : ℝ) (339168102373217 / 10000000000000000 : ℝ)
    (cell12514 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · have h := gap_lower (n := 12514) (a := (83555928757257 / 100000000000000 : ℝ)) (b := (3292603391 / 2000000000000 : ℝ)) (q := (284377391741 / 12500000000000 : ℝ))
      (E := (cell12514 ⟨15, by decide⟩).energy) (xi := (339168102373217 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12514 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12514]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12514])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12514) (a := (83555928757257 / 100000000000000 : ℝ)) (b := (3292603391 / 2000000000000 : ℝ)) (q := (284377391741 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12514])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12514])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12514]

theorem cert12514_16 : CellCertificate 12514 (178392188823437 / 2000000000000000 : ℝ) (419620651885313 / 250000000000000000 : ℝ) (339168102373217 / 10000000000000000 : ℝ)
    (cell12514 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · have h := gap_lower (n := 12514) (a := (8352126507059 / 10000000000000 : ℝ)) (b := (3292603391 / 2000000000000 : ℝ)) (q := (2275023123963 / 100000000000000 : ℝ))
      (E := (cell12514 ⟨16, by decide⟩).energy) (xi := (339168102373217 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12514 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12514]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12514])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12514) (a := (8352126507059 / 10000000000000 : ℝ)) (b := (3292603391 / 2000000000000 : ℝ)) (q := (2275023123963 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12514])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12514])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12514]

theorem cert12514_17 : CellCertificate 12514 (178392188823437 / 2000000000000000 : ℝ) (419620651885313 / 250000000000000000 : ℝ) (339168102373217 / 10000000000000000 : ℝ)
    (cell12514 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · have h := gap_lower (n := 12514) (a := (20871656468213 / 25000000000000 : ℝ)) (b := (3292603391 / 2000000000000 : ℝ)) (q := (1137513582969 / 50000000000000 : ℝ))
      (E := (cell12514 ⟨17, by decide⟩).energy) (xi := (339168102373217 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12514 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12514]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12514])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12514) (a := (20871656468213 / 25000000000000 : ℝ)) (b := (3292603391 / 2000000000000 : ℝ)) (q := (1137513582969 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12514])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12514])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12514]

theorem cert12514_18 : CellCertificate 12514 (178392188823437 / 2000000000000000 : ℝ) (419620651885313 / 250000000000000000 : ℝ) (339168102373217 / 10000000000000000 : ℝ)
    (cell12514 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · have h := gap_lower (n := 12514) (a := (8345201113013 / 10000000000000 : ℝ)) (b := (3292603391 / 2000000000000 : ℝ)) (q := (2275031148817 / 100000000000000 : ℝ))
      (E := (cell12514 ⟨18, by decide⟩).energy) (xi := (339168102373217 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12514 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12514]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12514])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12514) (a := (8345201113013 / 10000000000000 : ℝ)) (b := (3292603391 / 2000000000000 : ℝ)) (q := (2275031148817 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12514])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12514])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12514]

theorem cert12514_19 : CellCertificate 12514 (178392188823437 / 2000000000000000 : ℝ) (419620651885313 / 250000000000000000 : ℝ) (339168102373217 / 10000000000000000 : ℝ)
    (cell12514 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · have h := gap_lower (n := 12514) (a := (41708710404343 / 50000000000000 : ℝ)) (b := (3292603391 / 2000000000000 : ℝ)) (q := (14218969599 / 625000000000 : ℝ))
      (E := (cell12514 ⟨19, by decide⟩).energy) (xi := (339168102373217 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12514 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12514]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12514])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12514) (a := (41708710404343 / 50000000000000 : ℝ)) (b := (3292603391 / 2000000000000 : ℝ)) (q := (14218969599 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12514])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12514])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12514]

theorem cert12515_0 : CellCertificate 12515 (445966103080761 / 5000000000000000 : ℝ) (839174222562737 / 500000000000000000 : ℝ) (42392539603663 / 1250000000000000 : ℝ)
    (cell12515 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · have h := gap_lower (n := 12515) (a := (16815766151937 / 20000000000000 : ℝ)) (b := (1286069131 / 781250000000 : ℝ)) (q := (454965798501 / 20000000000000 : ℝ))
      (E := (cell12515 ⟨0, by decide⟩).energy) (xi := (42392539603663 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12515 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12515]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12515])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12515) (a := (16815766151937 / 20000000000000 : ℝ)) (b := (1286069131 / 781250000000 : ℝ)) (q := (454965798501 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12515])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12515])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12515]

theorem cert12515_1 : CellCertificate 12515 (445966103080761 / 5000000000000000 : ℝ) (839174222562737 / 500000000000000000 : ℝ) (42392539603663 / 1250000000000000 : ℝ)
    (cell12515 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · have h := gap_lower (n := 12515) (a := (21010948968453 / 25000000000000 : ℝ)) (b := (1286069131 / 781250000000 : ℝ)) (q := (568708243189 / 25000000000000 : ℝ))
      (E := (cell12515 ⟨1, by decide⟩).energy) (xi := (42392539603663 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12515 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12515]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12515])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12515) (a := (21010948968453 / 25000000000000 : ℝ)) (b := (1286069131 / 781250000000 : ℝ)) (q := (568708243189 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12515])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12515])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12515]

theorem cert12515_2 : CellCertificate 12515 (445966103080761 / 5000000000000000 : ℝ) (839174222562737 / 500000000000000000 : ℝ) (42392539603663 / 1250000000000000 : ℝ)
    (cell12515 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · have h := gap_lower (n := 12515) (a := (21002196501747 / 25000000000000 : ℝ)) (b := (1286069131 / 781250000000 : ℝ)) (q := (2274836952813 / 100000000000000 : ℝ))
      (E := (cell12515 ⟨2, by decide⟩).energy) (xi := (42392539603663 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12515 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12515]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12515])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12515) (a := (21002196501747 / 25000000000000 : ℝ)) (b := (1286069131 / 781250000000 : ℝ)) (q := (2274836952813 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12515])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12515])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12515]

theorem cert12515_3 : CellCertificate 12515 (445966103080761 / 5000000000000000 : ℝ) (839174222562737 / 500000000000000000 : ℝ) (42392539603663 / 1250000000000000 : ℝ)
    (cell12515 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · have h := gap_lower (n := 12515) (a := (3358952044901 / 4000000000000 : ℝ)) (b := (1286069131 / 781250000000 : ℝ)) (q := (568710235477 / 25000000000000 : ℝ))
      (E := (cell12515 ⟨3, by decide⟩).energy) (xi := (42392539603663 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12515 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12515]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12515])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12515) (a := (3358952044901 / 4000000000000 : ℝ)) (b := (1286069131 / 781250000000 : ℝ)) (q := (568710235477 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12515])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12515])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12515]

theorem cert12515_4 : CellCertificate 12515 (445966103080761 / 5000000000000000 : ℝ) (839174222562737 / 500000000000000000 : ℝ) (42392539603663 / 1250000000000000 : ℝ)
    (cell12515 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · have h := gap_lower (n := 12515) (a := (41969420591963 / 50000000000000 : ℝ)) (b := (1286069131 / 781250000000 : ℝ)) (q := (454968989803 / 20000000000000 : ℝ))
      (E := (cell12515 ⟨4, by decide⟩).energy) (xi := (42392539603663 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12515 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12515]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12515])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12515) (a := (41969420591963 / 50000000000000 : ℝ)) (b := (1286069131 / 781250000000 : ℝ)) (q := (454968989803 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12515])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12515])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12515]

theorem cert12515_5 : CellCertificate 12515 (445966103080761 / 5000000000000000 : ℝ) (839174222562737 / 500000000000000000 : ℝ) (42392539603663 / 1250000000000000 : ℝ)
    (cell12515 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · have h := gap_lower (n := 12515) (a := (10487988269361 / 12500000000000 : ℝ)) (b := (1286069131 / 781250000000 : ℝ)) (q := (113742446247 / 5000000000000 : ℝ))
      (E := (cell12515 ⟨5, by decide⟩).energy) (xi := (42392539603663 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12515 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12515]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12515])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12515) (a := (10487988269361 / 12500000000000 : ℝ)) (b := (1286069131 / 781250000000 : ℝ)) (q := (113742446247 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12515])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12515])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12515]

theorem cert12515_6 : CellCertificate 12515 (445966103080761 / 5000000000000000 : ℝ) (839174222562737 / 500000000000000000 : ℝ) (42392539603663 / 1250000000000000 : ℝ)
    (cell12515 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · have h := gap_lower (n := 12515) (a := (838689959993 / 1000000000000 : ℝ)) (b := (1286069131 / 781250000000 : ℝ)) (q := (1137426468001 / 50000000000000 : ℝ))
      (E := (cell12515 ⟨6, by decide⟩).energy) (xi := (42392539603663 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12515 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12515]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12515])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12515) (a := (838689959993 / 1000000000000 : ℝ)) (b := (1286069131 / 781250000000 : ℝ)) (q := (1137426468001 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12515])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12515])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12515]

theorem cert12515_7 : CellCertificate 12515 (445966103080761 / 5000000000000000 : ℝ) (839174222562737 / 500000000000000000 : ℝ) (42392539603663 / 1250000000000000 : ℝ)
    (cell12515 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · have h := gap_lower (n := 12515) (a := (83834110681239 / 100000000000000 : ℝ)) (b := (1286069131 / 781250000000 : ℝ)) (q := (454971386489 / 20000000000000 : ℝ))
      (E := (cell12515 ⟨7, by decide⟩).energy) (xi := (42392539603663 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12515 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12515]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12515])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12515) (a := (83834110681239 / 100000000000000 : ℝ)) (b := (1286069131 / 781250000000 : ℝ)) (q := (454971386489 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12515])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12515])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12515]

theorem cert12515_8 : CellCertificate 12515 (445966103080761 / 5000000000000000 : ℝ) (839174222562737 / 500000000000000000 : ℝ) (42392539603663 / 1250000000000000 : ℝ)
    (cell12515 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · have h := gap_lower (n := 12515) (a := (83799250164971 / 100000000000000 : ℝ)) (b := (1286069131 / 781250000000 : ℝ)) (q := (568715230537 / 25000000000000 : ℝ))
      (E := (cell12515 ⟨8, by decide⟩).energy) (xi := (42392539603663 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12515 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12515]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12515])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12515) (a := (83799250164971 / 100000000000000 : ℝ)) (b := (1286069131 / 781250000000 : ℝ)) (q := (568715230537 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12515])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12515])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12515]

theorem cert12515_9 : CellCertificate 12515 (445966103080761 / 5000000000000000 : ℝ) (839174222562737 / 500000000000000000 : ℝ) (42392539603663 / 1250000000000000 : ℝ)
    (cell12515 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · have h := gap_lower (n := 12515) (a := (83764414414951 / 100000000000000 : ℝ)) (b := (1286069131 / 781250000000 : ℝ)) (q := (227486491273 / 10000000000000 : ℝ))
      (E := (cell12515 ⟨9, by decide⟩).energy) (xi := (42392539603663 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12515 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12515]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12515])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12515) (a := (83764414414951 / 100000000000000 : ℝ)) (b := (1286069131 / 781250000000 : ℝ)) (q := (227486491273 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12515])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12515])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12515]

theorem cert12515_10 : CellCertificate 12515 (445966103080761 / 5000000000000000 : ℝ) (839174222562737 / 500000000000000000 : ℝ) (42392539603663 / 1250000000000000 : ℝ)
    (cell12515 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · have h := gap_lower (n := 12515) (a := (41864801697909 / 50000000000000 : ℝ)) (b := (1286069131 / 781250000000 : ℝ)) (q := (56871722789 / 2500000000000 : ℝ))
      (E := (cell12515 ⟨10, by decide⟩).energy) (xi := (42392539603663 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12515 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12515]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12515])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12515) (a := (41864801697909 / 50000000000000 : ℝ)) (b := (1286069131 / 781250000000 : ℝ)) (q := (56871722789 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12515])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12515])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12515]

theorem cert12515_11 : CellCertificate 12515 (445966103080761 / 5000000000000000 : ℝ) (839174222562737 / 500000000000000000 : ℝ) (42392539603663 / 1250000000000000 : ℝ)
    (cell12515 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · have h := gap_lower (n := 12515) (a := (41847408536199 / 50000000000000 : ℝ)) (b := (1286069131 / 781250000000 : ℝ)) (q := (2274872925757 / 100000000000000 : ℝ))
      (E := (cell12515 ⟨11, by decide⟩).energy) (xi := (42392539603663 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12515 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12515]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12515])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12515) (a := (41847408536199 / 50000000000000 : ℝ)) (b := (1286069131 / 781250000000 : ℝ)) (q := (2274872925757 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12515])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12515])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12515]

theorem cert12515_12 : CellCertificate 12515 (445966103080761 / 5000000000000000 : ℝ) (839174222562737 / 500000000000000000 : ℝ) (42392539603663 / 1250000000000000 : ℝ)
    (cell12515 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · have h := gap_lower (n := 12515) (a := (836600554097 / 1000000000000 : ℝ)) (b := (1286069131 / 781250000000 : ℝ)) (q := (1137438452057 / 50000000000000 : ℝ))
      (E := (cell12515 ⟨12, by decide⟩).energy) (xi := (42392539603663 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12515 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12515]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12515])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12515) (a := (836600554097 / 1000000000000 : ℝ)) (b := (1286069131 / 781250000000 : ℝ)) (q := (1137438452057 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12515])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12515])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12515]

theorem cert12515_13 : CellCertificate 12515 (445966103080761 / 5000000000000000 : ℝ) (839174222562737 / 500000000000000000 : ℝ) (42392539603663 / 1250000000000000 : ℝ)
    (cell12515 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · have h := gap_lower (n := 12515) (a := (41812659186457 / 50000000000000 : ℝ)) (b := (1286069131 / 781250000000 : ℝ)) (q := (568720227819 / 25000000000000 : ℝ))
      (E := (cell12515 ⟨13, by decide⟩).energy) (xi := (42392539603663 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12515 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12515]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12515])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12515) (a := (41812659186457 / 50000000000000 : ℝ)) (b := (1286069131 / 781250000000 : ℝ)) (q := (568720227819 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12515])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12515])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12515]

theorem cert12515_14 : CellCertificate 12515 (445966103080761 / 5000000000000000 : ℝ) (839174222562737 / 500000000000000000 : ℝ) (42392539603663 / 1250000000000000 : ℝ)
    (cell12515 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · have h := gap_lower (n := 12515) (a := (41795302963707 / 50000000000000 : ℝ)) (b := (1286069131 / 781250000000 : ℝ)) (q := (2274884895493 / 100000000000000 : ℝ))
      (E := (cell12515 ⟨14, by decide⟩).energy) (xi := (42392539603663 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12515 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12515]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12515])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12515) (a := (41795302963707 / 50000000000000 : ℝ)) (b := (1286069131 / 781250000000 : ℝ)) (q := (2274884895493 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12515])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12515])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12515]

theorem cert12515_15 : CellCertificate 12515 (445966103080761 / 5000000000000000 : ℝ) (839174222562737 / 500000000000000000 : ℝ) (42392539603663 / 1250000000000000 : ℝ)
    (cell12515 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · have h := gap_lower (n := 12515) (a := (2611122438711 / 3125000000000 : ℝ)) (b := (1286069131 / 781250000000 : ℝ)) (q := (2274888920959 / 100000000000000 : ℝ))
      (E := (cell12515 ⟨15, by decide⟩).energy) (xi := (42392539603663 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12515 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12515]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12515])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12515) (a := (2611122438711 / 3125000000000 : ℝ)) (b := (1286069131 / 781250000000 : ℝ)) (q := (2274888920959 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12515])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12515])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12515]

theorem cert12515_16 : CellCertificate 12515 (445966103080761 / 5000000000000000 : ℝ) (839174222562737 / 500000000000000000 : ℝ) (42392539603663 / 1250000000000000 : ℝ)
    (cell12515 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · have h := gap_lower (n := 12515) (a := (83521254672661 / 100000000000000 : ℝ)) (b := (1286069131 / 781250000000 : ℝ)) (q := (454978587077 / 20000000000000 : ℝ))
      (E := (cell12515 ⟨16, by decide⟩).energy) (xi := (42392539603663 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12515 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12515]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12515])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12515) (a := (83521254672661 / 100000000000000 : ℝ)) (b := (1286069131 / 781250000000 : ℝ)) (q := (454978587077 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12515])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12515])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12515]

theorem cert12515_17 : CellCertificate 12515 (445966103080761 / 5000000000000000 : ℝ) (839174222562737 / 500000000000000000 : ℝ) (42392539603663 / 1250000000000000 : ℝ)
    (cell12515 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · have h := gap_lower (n := 12515) (a := (83486615795051 / 100000000000000 : ℝ)) (b := (1286069131 / 781250000000 : ℝ)) (q := (17772631923 / 781250000000 : ℝ))
      (E := (cell12515 ⟨17, by decide⟩).energy) (xi := (42392539603663 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12515 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12515]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12515])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12515) (a := (83486615795051 / 100000000000000 : ℝ)) (b := (1286069131 / 781250000000 : ℝ)) (q := (17772631923 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12515])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12515])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12515]

theorem cert12515_18 : CellCertificate 12515 (445966103080761 / 5000000000000000 : ℝ) (839174222562737 / 500000000000000000 : ℝ) (42392539603663 / 1250000000000000 : ℝ)
    (cell12515 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · have h := gap_lower (n := 12515) (a := (83452001372009 / 100000000000000 : ℝ)) (b := (1286069131 / 781250000000 : ℝ)) (q := (2274900894907 / 100000000000000 : ℝ))
      (E := (cell12515 ⟨18, by decide⟩).energy) (xi := (42392539603663 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12515 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12515]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12515])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12515) (a := (83452001372009 / 100000000000000 : ℝ)) (b := (1286069131 / 781250000000 : ℝ)) (q := (2274900894907 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12515])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12515])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12515]

theorem cert12515_19 : CellCertificate 12515 (445966103080761 / 5000000000000000 : ℝ) (839174222562737 / 500000000000000000 : ℝ) (42392539603663 / 1250000000000000 : ℝ)
    (cell12515 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · have h := gap_lower (n := 12515) (a := (20854352842449 / 25000000000000 : ℝ)) (b := (1286069131 / 781250000000 : ℝ)) (q := (1137452454293 / 50000000000000 : ℝ))
      (E := (cell12515 ⟨19, by decide⟩).energy) (xi := (42392539603663 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12515 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12515]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12515])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12515) (a := (20854352842449 / 25000000000000 : ℝ)) (b := (1286069131 / 781250000000 : ℝ)) (q := (1137452454293 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12515])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12515])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12515]

theorem cert12516_0 : CellCertificate 12516 (178380694524307 / 2000000000000000 : ℝ) (1678214304155391 / 1000000000000000000 : ℝ) (10597266747491 / 312500000000000 : ℝ)
    (cell12516 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · have h := gap_lower (n := 12516) (a := (8407881518047 / 10000000000000 : ℝ)) (b := (164603530161 / 100000000000000 : ℝ)) (q := (2274698790849 / 100000000000000 : ℝ))
      (E := (cell12516 ⟨0, by decide⟩).energy) (xi := (10597266747491 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12516 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12516]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12516])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12516) (a := (8407881518047 / 10000000000000 : ℝ)) (b := (164603530161 / 100000000000000 : ℝ)) (q := (2274698790849 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12516])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12516])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12516]

theorem cert12516_1 : CellCertificate 12516 (178380694524307 / 2000000000000000 : ℝ) (1678214304155391 / 1000000000000000000 : ℝ) (10597266747491 / 312500000000000 : ℝ)
    (cell12516 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · have h := gap_lower (n := 12516) (a := (84043780621987 / 100000000000000 : ℝ)) (b := (164603530161 / 100000000000000 : ℝ)) (q := (2274702783969 / 100000000000000 : ℝ))
      (E := (cell12516 ⟨1, by decide⟩).energy) (xi := (10597266747491 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12516 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12516]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12516])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12516) (a := (84043780621987 / 100000000000000 : ℝ)) (b := (164603530161 / 100000000000000 : ℝ)) (q := (2274702783969 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12516])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12516])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12516]

theorem cert12516_2 : CellCertificate 12516 (178380694524307 / 2000000000000000 : ℝ) (1678214304155391 / 1000000000000000000 : ℝ) (10597266747491 / 312500000000000 : ℝ)
    (cell12516 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · have h := gap_lower (n := 12516) (a := (84008771082089 / 100000000000000 : ℝ)) (b := (164603530161 / 100000000000000 : ℝ)) (q := (28433834721 / 1250000000000 : ℝ))
      (E := (cell12516 ⟨2, by decide⟩).energy) (xi := (10597266747491 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12516 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12516]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12516])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12516) (a := (84008771082089 / 100000000000000 : ℝ)) (b := (164603530161 / 100000000000000 : ℝ)) (q := (28433834721 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12516])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12516])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12516]

theorem cert12516_3 : CellCertificate 12516 (178380694524307 / 2000000000000000 : ℝ) (1678214304155391 / 1000000000000000000 : ℝ) (10597266747491 / 312500000000000 : ℝ)
    (cell12516 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · have h := gap_lower (n := 12516) (a := (83973786524089 / 100000000000000 : ℝ)) (b := (164603530161 / 100000000000000 : ℝ)) (q := (2274710781213 / 100000000000000 : ℝ))
      (E := (cell12516 ⟨3, by decide⟩).energy) (xi := (10597266747491 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12516 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12516]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12516])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12516) (a := (83973786524089 / 100000000000000 : ℝ)) (b := (164603530161 / 100000000000000 : ℝ)) (q := (2274710781213 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12516])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12516])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12516]

theorem cert12516_4 : CellCertificate 12516 (178380694524307 / 2000000000000000 : ℝ) (1678214304155391 / 1000000000000000000 : ℝ) (10597266747491 / 312500000000000 : ℝ)
    (cell12516 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · have h := gap_lower (n := 12516) (a := (83938826911491 / 100000000000000 : ℝ)) (b := (164603530161 / 100000000000000 : ℝ)) (q := (2274714745657 / 100000000000000 : ℝ))
      (E := (cell12516 ⟨4, by decide⟩).energy) (xi := (10597266747491 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12516 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12516]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12516])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12516) (a := (83938826911491 / 100000000000000 : ℝ)) (b := (164603530161 / 100000000000000 : ℝ)) (q := (2274714745657 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12516])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12516])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12516]

theorem cert12516_5 : CellCertificate 12516 (178380694524307 / 2000000000000000 : ℝ) (1678214304155391 / 1000000000000000000 : ℝ) (10597266747491 / 312500000000000 : ℝ)
    (cell12516 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · have h := gap_lower (n := 12516) (a := (41951946103997 / 50000000000000 : ℝ)) (b := (164603530161 / 100000000000000 : ℝ)) (q := (2274718737563 / 100000000000000 : ℝ))
      (E := (cell12516 ⟨5, by decide⟩).energy) (xi := (10597266747491 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12516 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12516]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12516])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12516) (a := (41951946103997 / 50000000000000 : ℝ)) (b := (164603530161 / 100000000000000 : ℝ)) (q := (2274718737563 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12516])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12516])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12516]

theorem cert12516_6 : CellCertificate 12516 (178380694524307 / 2000000000000000 : ℝ) (1678214304155391 / 1000000000000000000 : ℝ) (10597266747491 / 312500000000000 : ℝ)
    (cell12516 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · have h := gap_lower (n := 12516) (a := (41934491188743 / 50000000000000 : ℝ)) (b := (164603530161 / 100000000000000 : ℝ)) (q := (568680691347 / 25000000000000 : ℝ))
      (E := (cell12516 ⟨6, by decide⟩).energy) (xi := (10597266747491 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12516 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12516]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12516])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12516) (a := (41934491188743 / 50000000000000 : ℝ)) (b := (164603530161 / 100000000000000 : ℝ)) (q := (568680691347 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12516])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12516])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12516]

theorem cert12516_7 : CellCertificate 12516 (178380694524307 / 2000000000000000 : ℝ) (1678214304155391 / 1000000000000000000 : ℝ) (10597266747491 / 312500000000000 : ℝ)
    (cell12516 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · have h := gap_lower (n := 12516) (a := (83834097384047 / 100000000000000 : ℝ)) (b := (164603530161 / 100000000000000 : ℝ)) (q := (3639562847 / 160000000000 : ℝ))
      (E := (cell12516 ⟨7, by decide⟩).energy) (xi := (10597266747491 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12516 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12516]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12516])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12516) (a := (83834097384047 / 100000000000000 : ℝ)) (b := (164603530161 / 100000000000000 : ℝ)) (q := (3639562847 / 160000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12516])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12516])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12516]

theorem cert12516_8 : CellCertificate 12516 (178380694524307 / 2000000000000000 : ℝ) (1678214304155391 / 1000000000000000000 : ℝ) (10597266747491 / 312500000000000 : ℝ)
    (cell12516 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · have h := gap_lower (n := 12516) (a := (10474904648993 / 12500000000000 : ℝ)) (b := (164603530161 / 100000000000000 : ℝ)) (q := (2274730729421 / 100000000000000 : ℝ))
      (E := (cell12516 ⟨8, by decide⟩).energy) (xi := (10597266747491 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12516 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12516]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12516])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12516) (a := (10474904648993 / 12500000000000 : ℝ)) (b := (164603530161 / 100000000000000 : ℝ)) (q := (2274730729421 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12516])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12516])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12516]

theorem cert12516_9 : CellCertificate 12516 (178380694524307 / 2000000000000000 : ℝ) (1678214304155391 / 1000000000000000000 : ℝ) (10597266747491 / 312500000000000 : ℝ)
    (cell12516 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · have h := gap_lower (n := 12516) (a := (83764401765631 / 100000000000000 : ℝ)) (b := (164603530161 / 100000000000000 : ℝ)) (q := (2274734739081 / 100000000000000 : ℝ))
      (E := (cell12516 ⟨9, by decide⟩).energy) (xi := (10597266747491 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12516 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12516]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12516])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12516) (a := (83764401765631 / 100000000000000 : ℝ)) (b := (164603530161 / 100000000000000 : ℝ)) (q := (2274734739081 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12516])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12516])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12516]

theorem cert12516_10 : CellCertificate 12516 (178380694524307 / 2000000000000000 : ℝ) (1678214304155391 / 1000000000000000000 : ℝ) (10597266747491 / 312500000000000 : ℝ)
    (cell12516 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · have h := gap_lower (n := 12516) (a := (334918364279 / 400000000000 : ℝ)) (b := (164603530161 / 100000000000000 : ℝ)) (q := (2274738757767 / 100000000000000 : ℝ))
      (E := (cell12516 ⟨10, by decide⟩).energy) (xi := (10597266747491 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12516 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12516]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12516])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12516) (a := (334918364279 / 400000000000 : ℝ)) (b := (164603530161 / 100000000000000 : ℝ)) (q := (2274738757767 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12516])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12516])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12516]

theorem cert12516_11 : CellCertificate 12516 (178380694524307 / 2000000000000000 : ℝ) (1678214304155391 / 1000000000000000000 : ℝ) (10597266747491 / 312500000000000 : ℝ)
    (cell12516 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · have h := gap_lower (n := 12516) (a := (83694805069127 / 100000000000000 : ℝ)) (b := (164603530161 / 100000000000000 : ℝ)) (q := (2274742734547 / 100000000000000 : ℝ))
      (E := (cell12516 ⟨11, by decide⟩).energy) (xi := (10597266747491 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12516 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12516]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12516])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12516) (a := (83694805069127 / 100000000000000 : ℝ)) (b := (164603530161 / 100000000000000 : ℝ)) (q := (2274742734547 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12516])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12516])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12516]

theorem cert12516_12 : CellCertificate 12516 (178380694524307 / 2000000000000000 : ℝ) (1678214304155391 / 1000000000000000000 : ℝ) (10597266747491 / 312500000000000 : ℝ)
    (cell12516 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · have h := gap_lower (n := 12516) (a := (20915010932193 / 25000000000000 : ℝ)) (b := (164603530161 / 100000000000000 : ℝ)) (q := (142171670893 / 6250000000000 : ℝ))
      (E := (cell12516 ⟨12, by decide⟩).energy) (xi := (10597266747491 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12516 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12516]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12516])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12516) (a := (20915010932193 / 25000000000000 : ℝ)) (b := (164603530161 / 100000000000000 : ℝ)) (q := (142171670893 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12516])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12516])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12516]

theorem cert12516_13 : CellCertificate 12516 (178380694524307 / 2000000000000000 : ℝ) (1678214304155391 / 1000000000000000000 : ℝ) (10597266747491 / 312500000000000 : ℝ)
    (cell12516 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · have h := gap_lower (n := 12516) (a := (20906326753469 / 25000000000000 : ℝ)) (b := (164603530161 / 100000000000000 : ℝ)) (q := (227475076361 / 10000000000000 : ℝ))
      (E := (cell12516 ⟨13, by decide⟩).energy) (xi := (10597266747491 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12516 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12516]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12516])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12516) (a := (20906326753469 / 25000000000000 : ℝ)) (b := (164603530161 / 100000000000000 : ℝ)) (q := (227475076361 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12516])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12516])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12516]

theorem cert12516_14 : CellCertificate 12516 (178380694524307 / 2000000000000000 : ℝ) (1678214304155391 / 1000000000000000000 : ℝ) (10597266747491 / 312500000000000 : ℝ)
    (cell12516 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · have h := gap_lower (n := 12516) (a := (41795297444907 / 50000000000000 : ℝ)) (b := (164603530161 / 100000000000000 : ℝ)) (q := (7108608477 / 312500000000 : ℝ))
      (E := (cell12516 ⟨14, by decide⟩).energy) (xi := (10597266747491 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12516 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12516]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12516])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12516) (a := (41795297444907 / 50000000000000 : ℝ)) (b := (164603530161 / 100000000000000 : ℝ)) (q := (7108608477 / 312500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12516])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12516])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12516]

theorem cert12516_15 : CellCertificate 12516 (178380694524307 / 2000000000000000 : ℝ) (1678214304155391 / 1000000000000000000 : ℝ) (10597266747491 / 312500000000000 : ℝ)
    (cell12516 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · have h := gap_lower (n := 12516) (a := (4177795366107 / 5000000000000 : ℝ)) (b := (164603530161 / 100000000000000 : ℝ)) (q := (1137379351823 / 50000000000000 : ℝ))
      (E := (cell12516 ⟨15, by decide⟩).energy) (xi := (10597266747491 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12516 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12516]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12516])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12516) (a := (4177795366107 / 5000000000000 : ℝ)) (b := (164603530161 / 100000000000000 : ℝ)) (q := (1137379351823 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12516])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12516])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12516]

theorem cert12516_16 : CellCertificate 12516 (178380694524307 / 2000000000000000 : ℝ) (1678214304155391 / 1000000000000000000 : ℝ) (10597266747491 / 312500000000000 : ℝ)
    (cell12516 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · have h := gap_lower (n := 12516) (a := (41760622138293 / 50000000000000 : ℝ)) (b := (164603530161 / 100000000000000 : ℝ)) (q := (2274762742503 / 100000000000000 : ℝ))
      (E := (cell12516 ⟨16, by decide⟩).energy) (xi := (10597266747491 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12516 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12516]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12516])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12516) (a := (41760622138293 / 50000000000000 : ℝ)) (b := (164603530161 / 100000000000000 : ℝ)) (q := (2274762742503 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12516])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12516])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12516]

theorem cert12516_17 : CellCertificate 12516 (178380694524307 / 2000000000000000 : ℝ) (1678214304155391 / 1000000000000000000 : ℝ) (10597266747491 / 312500000000000 : ℝ)
    (cell12516 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · have h := gap_lower (n := 12516) (a := (10435825714883 / 12500000000000 : ℝ)) (b := (164603530161 / 100000000000000 : ℝ)) (q := (4442903747 / 195312500000 : ℝ))
      (E := (cell12516 ⟨17, by decide⟩).energy) (xi := (10597266747491 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12516 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12516]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12516])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12516) (a := (10435825714883 / 12500000000000 : ℝ)) (b := (164603530161 / 100000000000000 : ℝ)) (q := (4442903747 / 195312500000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12516])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12516])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12516]

theorem cert12516_18 : CellCertificate 12516 (178380694524307 / 2000000000000000 : ℝ) (1678214304155391 / 1000000000000000000 : ℝ) (10597266747491 / 312500000000000 : ℝ)
    (cell12516 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · have h := gap_lower (n := 12516) (a := (83451991615661 / 100000000000000 : ℝ)) (b := (164603530161 / 100000000000000 : ℝ)) (q := (2274770753201 / 100000000000000 : ℝ))
      (E := (cell12516 ⟨18, by decide⟩).energy) (xi := (10597266747491 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12516 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12516]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12516])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12516) (a := (83451991615661 / 100000000000000 : ℝ)) (b := (164603530161 / 100000000000000 : ℝ)) (q := (2274770753201 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12516])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12516])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12516]

theorem cert12516_19 : CellCertificate 12516 (178380694524307 / 2000000000000000 : ℝ) (1678214304155391 / 1000000000000000000 : ℝ) (10597266747491 / 312500000000000 : ℝ)
    (cell12516 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · have h := gap_lower (n := 12516) (a := (83417401932641 / 100000000000000 : ℝ)) (b := (164603530161 / 100000000000000 : ℝ)) (q := (1137387367693 / 50000000000000 : ℝ))
      (E := (cell12516 ⟨19, by decide⟩).energy) (xi := (10597266747491 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12516 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12516]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12516])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12516) (a := (83417401932641 / 100000000000000 : ℝ)) (b := (164603530161 / 100000000000000 : ℝ)) (q := (1137387367693 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12516])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12516])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12516]

theorem cert12517_0 : CellCertificate 12517 (891874743496159 / 10000000000000000 : ℝ) (1678080184625863 / 1000000000000000000 : ℝ) (8477118991079 / 250000000000000 : ℝ)
    (cell12517 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · have h := gap_lower (n := 12517) (a := (21019699900937 / 25000000000000 : ℝ)) (b := (164590213729 / 100000000000000 : ℝ)) (q := (284321080253 / 12500000000000 : ℝ))
      (E := (cell12517 ⟨0, by decide⟩).energy) (xi := (8477118991079 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12517 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12517]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12517])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12517) (a := (21019699900937 / 25000000000000 : ℝ)) (b := (164590213729 / 100000000000000 : ℝ)) (q := (284321080253 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12517])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12517])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12517]

theorem cert12517_1 : CellCertificate 12517 (891874743496159 / 10000000000000000 : ℝ) (1678080184625863 / 1000000000000000000 : ℝ) (8477118991079 / 250000000000000 : ℝ)
    (cell12517 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · have h := gap_lower (n := 12517) (a := (42021882686307 / 50000000000000 : ℝ)) (b := (164590213729 / 100000000000000 : ℝ)) (q := (2274572648077 / 100000000000000 : ℝ))
      (E := (cell12517 ⟨1, by decide⟩).energy) (xi := (8477118991079 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12517 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12517]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12517])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12517) (a := (42021882686307 / 50000000000000 : ℝ)) (b := (164590213729 / 100000000000000 : ℝ)) (q := (2274572648077 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12517])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12517])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12517]

theorem cert12517_2 : CellCertificate 12517 (891874743496159 / 10000000000000000 : ℝ) (1678080184625863 / 1000000000000000000 : ℝ) (8477118991079 / 250000000000000 : ℝ)
    (cell12517 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · have h := gap_lower (n := 12517) (a := (42004378079801 / 50000000000000 : ℝ)) (b := (164590213729 / 100000000000000 : ℝ)) (q := (2274576655507 / 100000000000000 : ℝ))
      (E := (cell12517 ⟨2, by decide⟩).energy) (xi := (8477118991079 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12517 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12517]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12517])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12517) (a := (42004378079801 / 50000000000000 : ℝ)) (b := (164590213729 / 100000000000000 : ℝ)) (q := (2274576655507 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12517])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12517])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12517]

theorem cert12517_3 : CellCertificate 12517 (891874743496159 / 10000000000000000 : ℝ) (1678080184625863 / 1000000000000000000 : ℝ) (8477118991079 / 250000000000000 : ℝ)
    (cell12517 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · have h := gap_lower (n := 12517) (a := (10496721491003 / 12500000000000 : ℝ)) (b := (164590213729 / 100000000000000 : ℝ)) (q := (2274580615683 / 100000000000000 : ℝ))
      (E := (cell12517 ⟨3, by decide⟩).energy) (xi := (8477118991079 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12517 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12517]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12517])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12517) (a := (10496721491003 / 12500000000000 : ℝ)) (b := (164590213729 / 100000000000000 : ℝ)) (q := (2274580615683 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12517])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12517])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12517]

theorem cert12517_4 : CellCertificate 12517 (891874743496159 / 10000000000000000 : ℝ) (1678080184625863 / 1000000000000000000 : ℝ) (8477118991079 / 250000000000000 : ℝ)
    (cell12517 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · have h := gap_lower (n := 12517) (a := (83938812641387 / 100000000000000 : ℝ)) (b := (164590213729 / 100000000000000 : ℝ)) (q := (2274584595391 / 100000000000000 : ℝ))
      (E := (cell12517 ⟨4, by decide⟩).energy) (xi := (8477118991079 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12517 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12517]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12517])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12517) (a := (83938812641387 / 100000000000000 : ℝ)) (b := (164590213729 / 100000000000000 : ℝ)) (q := (2274584595391 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12517])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12517])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12517]

theorem cert12517_5 : CellCertificate 12517 (891874743496159 / 10000000000000000 : ℝ) (1678080184625863 / 1000000000000000000 : ℝ) (8477118991079 / 250000000000000 : ℝ)
    (cell12517 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · have h := gap_lower (n := 12517) (a := (83903878263391 / 100000000000000 : ℝ)) (b := (164590213729 / 100000000000000 : ℝ)) (q := (1137294301671 / 50000000000000 : ℝ))
      (E := (cell12517 ⟨5, by decide⟩).energy) (xi := (8477118991079 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12517 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12517]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12517])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12517) (a := (83903878263391 / 100000000000000 : ℝ)) (b := (164590213729 / 100000000000000 : ℝ)) (q := (1137294301671 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12517])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12517])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12517]

theorem cert12517_6 : CellCertificate 12517 (891874743496159 / 10000000000000000 : ℝ) (1678080184625863 / 1000000000000000000 : ℝ) (8477118991079 / 250000000000000 : ℝ)
    (cell12517 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · have h := gap_lower (n := 12517) (a := (20967242189481 / 25000000000000 : ℝ)) (b := (164590213729 / 100000000000000 : ℝ)) (q := (1137296295031 / 50000000000000 : ℝ))
      (E := (cell12517 ⟨6, by decide⟩).energy) (xi := (8477118991079 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12517 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12517]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12517])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12517) (a := (20967242189481 / 25000000000000 : ℝ)) (b := (164590213729 / 100000000000000 : ℝ)) (q := (1137296295031 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12517])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12517])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12517]

theorem cert12517_7 : CellCertificate 12517 (891874743496159 / 10000000000000000 : ℝ) (1678080184625863 / 1000000000000000000 : ℝ) (8477118991079 / 250000000000000 : ℝ)
    (cell12517 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · have h := gap_lower (n := 12517) (a := (83834084089067 / 100000000000000 : ℝ)) (b := (164590213729 / 100000000000000 : ℝ)) (q := (2274596621633 / 100000000000000 : ℝ))
      (E := (cell12517 ⟨7, by decide⟩).energy) (xi := (8477118991079 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12517 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12517]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12517])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12517) (a := (83834084089067 / 100000000000000 : ℝ)) (b := (164590213729 / 100000000000000 : ℝ)) (q := (2274596621633 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12517])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12517])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12517]

theorem cert12517_8 : CellCertificate 12517 (891874743496159 / 10000000000000000 : ℝ) (1678080184625863 / 1000000000000000000 : ℝ) (8477118991079 / 250000000000000 : ℝ)
    (cell12517 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · have h := gap_lower (n := 12517) (a := (2618725756909 / 3125000000000 : ℝ)) (b := (164590213729 / 100000000000000 : ℝ)) (q := (2274600590043 / 100000000000000 : ℝ))
      (E := (cell12517 ⟨8, by decide⟩).energy) (xi := (8477118991079 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12517 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12517]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12517])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12517) (a := (2618725756909 / 3125000000000 : ℝ)) (b := (164590213729 / 100000000000000 : ℝ)) (q := (2274600590043 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12517])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12517])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12517]

theorem cert12517_9 : CellCertificate 12517 (891874743496159 / 10000000000000000 : ℝ) (1678080184625863 / 1000000000000000000 : ℝ) (8477118991079 / 250000000000000 : ℝ)
    (cell12517 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · have h := gap_lower (n := 12517) (a := (83764389118443 / 100000000000000 : ℝ)) (b := (164590213729 / 100000000000000 : ℝ)) (q := (568651154711 / 25000000000000 : ℝ))
      (E := (cell12517 ⟨9, by decide⟩).energy) (xi := (8477118991079 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12517 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12517]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12517])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12517) (a := (83764389118443 / 100000000000000 : ℝ)) (b := (164590213729 / 100000000000000 : ℝ)) (q := (568651154711 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12517])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12517])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12517]

theorem cert12517_10 : CellCertificate 12517 (891874743496159 / 10000000000000000 : ℝ) (1678080184625863 / 1000000000000000000 : ℝ) (8477118991079 / 250000000000000 : ℝ)
    (cell12517 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · have h := gap_lower (n := 12517) (a := (41864789372887 / 50000000000000 : ℝ)) (b := (164590213729 / 100000000000000 : ℝ)) (q := (17770379683 / 781250000000 : ℝ))
      (E := (cell12517 ⟨10, by decide⟩).energy) (xi := (8477118991079 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12517 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12517]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12517])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12517) (a := (41864789372887 / 50000000000000 : ℝ)) (b := (164590213729 / 100000000000000 : ℝ)) (q := (17770379683 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12517])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12517])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12517]

theorem cert12517_11 : CellCertificate 12517 (891874743496159 / 10000000000000000 : ℝ) (1678080184625863 / 1000000000000000000 : ℝ) (8477118991079 / 250000000000000 : ℝ)
    (cell12517 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · have h := gap_lower (n := 12517) (a := (20923698266977 / 25000000000000 : ℝ)) (b := (164590213729 / 100000000000000 : ℝ)) (q := (2274612596877 / 100000000000000 : ℝ))
      (E := (cell12517 ⟨11, by decide⟩).energy) (xi := (8477118991079 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12517 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12517]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12517])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12517) (a := (20923698266977 / 25000000000000 : ℝ)) (b := (164590213729 / 100000000000000 : ℝ)) (q := (2274612596877 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12517])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12517])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12517]

theorem cert12517_12 : CellCertificate 12517 (891874743496159 / 10000000000000000 : ℝ) (1678080184625863 / 1000000000000000000 : ℝ) (8477118991079 / 250000000000000 : ℝ)
    (cell12517 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · have h := gap_lower (n := 12517) (a := (1307188000779 / 1562500000000 : ℝ)) (b := (164590213729 / 100000000000000 : ℝ)) (q := (568654154517 / 25000000000000 : ℝ))
      (E := (cell12517 ⟨12, by decide⟩).energy) (xi := (8477118991079 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12517 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12517]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12517])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12517) (a := (1307188000779 / 1562500000000 : ℝ)) (b := (164590213729 / 100000000000000 : ℝ)) (q := (568654154517 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12517])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12517])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12517]

theorem cert12517_13 : CellCertificate 12517 (891874743496159 / 10000000000000000 : ℝ) (1678080184625863 / 1000000000000000000 : ℝ) (8477118991079 / 250000000000000 : ℝ)
    (cell12517 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · have h := gap_lower (n := 12517) (a := (8362529565681 / 10000000000000 : ℝ)) (b := (164590213729 / 100000000000000 : ℝ)) (q := (2274620611517 / 100000000000000 : ℝ))
      (E := (cell12517 ⟨13, by decide⟩).energy) (xi := (8477118991079 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12517 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12517]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12517])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12517) (a := (8362529565681 / 10000000000000 : ℝ)) (b := (164590213729 / 100000000000000 : ℝ)) (q := (2274620611517 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12517])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12517])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12517]

theorem cert12517_14 : CellCertificate 12517 (891874743496159 / 10000000000000000 : ℝ) (1678080184625863 / 1000000000000000000 : ℝ) (8477118991079 / 250000000000000 : ℝ)
    (cell12517 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · have h := gap_lower (n := 12517) (a := (83590583854147 / 100000000000000 : ℝ)) (b := (164590213729 / 100000000000000 : ℝ)) (q := (2274624583521 / 100000000000000 : ℝ))
      (E := (cell12517 ⟨14, by decide⟩).energy) (xi := (8477118991079 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12517 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12517]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12517])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12517) (a := (83590583854147 / 100000000000000 : ℝ)) (b := (164590213729 / 100000000000000 : ℝ)) (q := (2274624583521 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12517])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12517])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12517]

theorem cert12517_15 : CellCertificate 12517 (891874743496159 / 10000000000000000 : ℝ) (1678080184625863 / 1000000000000000000 : ℝ) (8477118991079 / 250000000000000 : ℝ)
    (cell12517 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · have h := gap_lower (n := 12517) (a := (4177794830371 / 5000000000000 : ℝ)) (b := (164590213729 / 100000000000000 : ℝ)) (q := (1137314299137 / 50000000000000 : ℝ))
      (E := (cell12517 ⟨15, by decide⟩).energy) (xi := (8477118991079 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12517 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12517]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12517])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12517) (a := (4177794830371 / 5000000000000 : ℝ)) (b := (164590213729 / 100000000000000 : ℝ)) (q := (1137314299137 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12517])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12517])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12517]

theorem cert12517_16 : CellCertificate 12517 (891874743496159 / 10000000000000000 : ℝ) (1678080184625863 / 1000000000000000000 : ℝ) (8477118991079 / 250000000000000 : ℝ)
    (cell12517 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · have h := gap_lower (n := 12517) (a := (20880308470591 / 25000000000000 : ℝ)) (b := (164590213729 / 100000000000000 : ℝ)) (q := (568658150871 / 25000000000000 : ℝ))
      (E := (cell12517 ⟨16, by decide⟩).energy) (xi := (8477118991079 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12517 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12517]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12517])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12517) (a := (20880308470591 / 25000000000000 : ℝ)) (b := (164590213729 / 100000000000000 : ℝ)) (q := (568658150871 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12517])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12517])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12517]

theorem cert12517_17 : CellCertificate 12517 (891874743496159 / 10000000000000000 : ℝ) (1678080184625863 / 1000000000000000000 : ℝ) (8477118991079 / 250000000000000 : ℝ)
    (cell12517 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · have h := gap_lower (n := 12517) (a := (83486595644891 / 100000000000000 : ℝ)) (b := (164590213729 / 100000000000000 : ℝ)) (q := (2274636604711 / 100000000000000 : ℝ))
      (E := (cell12517 ⟨17, by decide⟩).energy) (xi := (8477118991079 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12517 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12517]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12517])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12517) (a := (83486595644891 / 100000000000000 : ℝ)) (b := (164590213729 / 100000000000000 : ℝ)) (q := (2274636604711 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12517])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12517])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12517]

theorem cert12517_18 : CellCertificate 12517 (891874743496159 / 10000000000000000 : ℝ) (1678080184625863 / 1000000000000000000 : ℝ) (8477118991079 / 250000000000000 : ℝ)
    (cell12517 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · have h := gap_lower (n := 12517) (a := (2607874433159 / 3125000000000 : ℝ)) (b := (164590213729 / 100000000000000 : ℝ)) (q := (284330075909 / 12500000000000 : ℝ))
      (E := (cell12517 ⟨18, by decide⟩).energy) (xi := (8477118991079 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12517 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12517]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12517])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12517) (a := (2607874433159 / 3125000000000 : ℝ)) (b := (164590213729 / 100000000000000 : ℝ)) (q := (284330075909 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12517])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12517])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12517]

theorem cert12517_19 : CellCertificate 12517 (891874743496159 / 10000000000000000 : ℝ) (1678080184625863 / 1000000000000000000 : ℝ) (8477118991079 / 250000000000000 : ℝ)
    (cell12517 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · have h := gap_lower (n := 12517) (a := (41708696248611 / 50000000000000 : ℝ)) (b := (164590213729 / 100000000000000 : ℝ)) (q := (1137322279001 / 50000000000000 : ℝ))
      (E := (cell12517 ⟨19, by decide⟩).energy) (xi := (8477118991079 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12517 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12517]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12517])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12517) (a := (41708696248611 / 50000000000000 : ℝ)) (b := (164590213729 / 100000000000000 : ℝ)) (q := (1137322279001 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12517])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12517])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12517]

theorem cert12518_0 : CellCertificate 12518 (891846018784327 / 10000000000000000 : ℝ) (419486521632937 / 250000000000000000 : ℝ) (10595530874949 / 312500000000000 : ℝ)
    (cell12518 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · have h := gap_lower (n := 12518) (a := (84078784029517 / 100000000000000 : ℝ)) (b := (164576899471 / 100000000000000 : ℝ)) (q := (2274438546033 / 100000000000000 : ℝ))
      (E := (cell12518 ⟨0, by decide⟩).energy) (xi := (10595530874949 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12518 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12518]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12518])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12518) (a := (84078784029517 / 100000000000000 : ℝ)) (b := (164576899471 / 100000000000000 : ℝ)) (q := (2274438546033 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12518])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12518])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12518]

theorem cert12518_1 : CellCertificate 12518 (891846018784327 / 10000000000000000 : ℝ) (419486521632937 / 250000000000000000 : ℝ) (10595530874949 / 312500000000000 : ℝ)
    (cell12518 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · have h := gap_lower (n := 12518) (a := (21010937531423 / 25000000000000 : ℝ)) (b := (164576899471 / 100000000000000 : ℝ)) (q := (454888513017 / 20000000000000 : ℝ))
      (E := (cell12518 ⟨1, by decide⟩).energy) (xi := (10595530874949 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12518 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12518]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12518])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12518) (a := (21010937531423 / 25000000000000 : ℝ)) (b := (164576899471 / 100000000000000 : ℝ)) (q := (454888513017 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12518])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12518])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12518]

theorem cert12518_2 : CellCertificate 12518 (891846018784327 / 10000000000000000 : ℝ) (419486521632937 / 250000000000000000 : ℝ) (10595530874949 / 312500000000000 : ℝ)
    (cell12518 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · have h := gap_lower (n := 12518) (a := (3360349649581 / 4000000000000 : ℝ)) (b := (164576899471 / 100000000000000 : ℝ)) (q := (113722326423 / 5000000000000 : ℝ))
      (E := (cell12518 ⟨2, by decide⟩).energy) (xi := (10595530874949 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12518 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12518]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12518])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12518) (a := (3360349649581 / 4000000000000 : ℝ)) (b := (164576899471 / 100000000000000 : ℝ)) (q := (113722326423 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12518])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12518])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12518]

theorem cert12518_3 : CellCertificate 12518 (891846018784327 / 10000000000000000 : ℝ) (419486521632937 / 250000000000000000 : ℝ) (10595530874949 / 312500000000000 : ℝ)
    (cell12518 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · have h := gap_lower (n := 12518) (a := (8397375733433 / 10000000000000 : ℝ)) (b := (164576899471 / 100000000000000 : ℝ)) (q := (2274450503181 / 100000000000000 : ℝ))
      (E := (cell12518 ⟨3, by decide⟩).energy) (xi := (10595530874949 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12518 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12518]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12518])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12518) (a := (8397375733433 / 10000000000000 : ℝ)) (b := (164576899471 / 100000000000000 : ℝ)) (q := (2274450503181 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12518])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12518])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12518]

theorem cert12518_4 : CellCertificate 12518 (891846018784327 / 10000000000000000 : ℝ) (419486521632937 / 250000000000000000 : ℝ) (10595530874949 / 312500000000000 : ℝ)
    (cell12518 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · have h := gap_lower (n := 12518) (a := (41969399186807 / 50000000000000 : ℝ)) (b := (164576899471 / 100000000000000 : ℝ)) (q := (284306812277 / 12500000000000 : ℝ))
      (E := (cell12518 ⟨4, by decide⟩).energy) (xi := (10595530874949 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12518 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12518]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12518])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12518) (a := (41969399186807 / 50000000000000 : ℝ)) (b := (164576899471 / 100000000000000 : ℝ)) (q := (284306812277 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12518])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12518])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12518]

theorem cert12518_5 : CellCertificate 12518 (891846018784327 / 10000000000000000 : ℝ) (419486521632937 / 250000000000000000 : ℝ) (10595530874949 / 312500000000000 : ℝ)
    (cell12518 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · have h := gap_lower (n := 12518) (a := (41951932160539 / 50000000000000 : ℝ)) (b := (164576899471 / 100000000000000 : ℝ)) (q := (1137229261139 / 50000000000000 : ℝ))
      (E := (cell12518 ⟨5, by decide⟩).energy) (xi := (10595530874949 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12518 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12518]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12518])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12518) (a := (41951932160539 / 50000000000000 : ℝ)) (b := (164576899471 / 100000000000000 : ℝ)) (q := (1137229261139 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12518])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12518])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12518]

theorem cert12518_6 : CellCertificate 12518 (891846018784327 / 10000000000000000 : ℝ) (419486521632937 / 250000000000000000 : ℝ) (10595530874949 / 312500000000000 : ℝ)
    (cell12518 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · have h := gap_lower (n := 12518) (a := (20967238785153 / 25000000000000 : ℝ)) (b := (164576899471 / 100000000000000 : ℝ)) (q := (2274462525889 / 100000000000000 : ℝ))
      (E := (cell12518 ⟨6, by decide⟩).energy) (xi := (10595530874949 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12518 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12518]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12518])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12518) (a := (20967238785153 / 25000000000000 : ℝ)) (b := (164576899471 / 100000000000000 : ℝ)) (q := (2274462525889 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12518])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12518])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12518]

theorem cert12518_7 : CellCertificate 12518 (891846018784327 / 10000000000000000 : ℝ) (419486521632937 / 250000000000000000 : ℝ) (10595530874949 / 312500000000000 : ℝ)
    (cell12518 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · have h := gap_lower (n := 12518) (a := (10479258849537 / 12500000000000 : ℝ)) (b := (164576899471 / 100000000000000 : ℝ)) (q := (1137233258589 / 50000000000000 : ℝ))
      (E := (cell12518 ⟨7, by decide⟩).energy) (xi := (10595530874949 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12518 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12518]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12518])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12518) (a := (10479258849537 / 12500000000000 : ℝ)) (b := (164576899471 / 100000000000000 : ℝ)) (q := (1137233258589 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12518])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12518])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12518]

theorem cert12518_8 : CellCertificate 12518 (891846018784327 / 10000000000000000 : ℝ) (419486521632937 / 250000000000000000 : ℝ) (10595530874949 / 312500000000000 : ℝ)
    (cell12518 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · have h := gap_lower (n := 12518) (a := (41899605626201 / 50000000000000 : ℝ)) (b := (164576899471 / 100000000000000 : ℝ)) (q := (454894100803 / 20000000000000 : ℝ))
      (E := (cell12518 ⟨8, by decide⟩).energy) (xi := (10595530874949 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12518 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12518]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12518])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12518) (a := (41899605626201 / 50000000000000 : ℝ)) (b := (164576899471 / 100000000000000 : ℝ)) (q := (454894100803 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12518])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12518])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12518]

theorem cert12518_9 : CellCertificate 12518 (891846018784327 / 10000000000000000 : ℝ) (419486521632937 / 250000000000000000 : ℝ) (10595530874949 / 312500000000000 : ℝ)
    (cell12518 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · have h := gap_lower (n := 12518) (a := (10470547059173 / 12500000000000 : ℝ)) (b := (164576899471 / 100000000000000 : ℝ)) (q := (1137237247011 / 50000000000000 : ℝ))
      (E := (cell12518 ⟨9, by decide⟩).energy) (xi := (10595530874949 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12518 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12518]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12518])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12518) (a := (10470547059173 / 12500000000000 : ℝ)) (b := (164576899471 / 100000000000000 : ℝ)) (q := (1137237247011 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12518])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12518])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12518]

theorem cert12518_10 : CellCertificate 12518 (891846018784327 / 10000000000000000 : ℝ) (419486521632937 / 250000000000000000 : ℝ) (10595530874949 / 312500000000000 : ℝ)
    (cell12518 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · have h := gap_lower (n := 12518) (a := (83729566423887 / 100000000000000 : ℝ)) (b := (164576899471 / 100000000000000 : ℝ)) (q := (2274478494563 / 100000000000000 : ℝ))
      (E := (cell12518 ⟨10, by decide⟩).energy) (xi := (10595530874949 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12518 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12518]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12518])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12518) (a := (83729566423887 / 100000000000000 : ℝ)) (b := (164576899471 / 100000000000000 : ℝ)) (q := (2274478494563 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12518])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12518])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12518]

theorem cert12518_11 : CellCertificate 12518 (891846018784327 / 10000000000000000 : ℝ) (419486521632937 / 250000000000000000 : ℝ) (10595530874949 / 312500000000000 : ℝ)
    (cell12518 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · have h := gap_lower (n := 12518) (a := (83694781068739 / 100000000000000 : ℝ)) (b := (164576899471 / 100000000000000 : ℝ)) (q := (2274482512753 / 100000000000000 : ℝ))
      (E := (cell12518 ⟨11, by decide⟩).energy) (xi := (10595530874949 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12518 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12518]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12518])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12518) (a := (83694781068739 / 100000000000000 : ℝ)) (b := (164576899471 / 100000000000000 : ℝ)) (q := (2274482512753 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12518])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12518])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12518]

theorem cert12518_12 : CellCertificate 12518 (891846018784327 / 10000000000000000 : ℝ) (419486521632937 / 250000000000000000 : ℝ) (10595530874949 / 312500000000000 : ℝ)
    (cell12518 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · have h := gap_lower (n := 12518) (a := (1673200407459 / 2000000000000 : ℝ)) (b := (164576899471 / 100000000000000 : ℝ)) (q := (284310812173 / 12500000000000 : ℝ))
      (E := (cell12518 ⟨12, by decide⟩).energy) (xi := (10595530874949 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12518 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12518]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12518])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12518) (a := (1673200407459 / 2000000000000 : ℝ)) (b := (164576899471 / 100000000000000 : ℝ)) (q := (284310812173 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12518])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12518])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12518]

theorem cert12518_13 : CellCertificate 12518 (891846018784327 / 10000000000000000 : ℝ) (419486521632937 / 250000000000000000 : ℝ) (10595530874949 / 312500000000000 : ℝ)
    (cell12518 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · have h := gap_lower (n := 12518) (a := (20906321075429 / 25000000000000 : ℝ)) (b := (164576899471 / 100000000000000 : ℝ)) (q := (2274490513097 / 100000000000000 : ℝ))
      (E := (cell12518 ⟨13, by decide⟩).energy) (xi := (10595530874949 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12518 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12518]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12518])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12518) (a := (20906321075429 / 25000000000000 : ℝ)) (b := (164576899471 / 100000000000000 : ℝ)) (q := (2274490513097 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12518])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12518])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12518]

theorem cert12518_14 : CellCertificate 12518 (891846018784327 / 10000000000000000 : ℝ) (419486521632937 / 250000000000000000 : ℝ) (10595530874949 / 312500000000000 : ℝ)
    (cell12518 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · have h := gap_lower (n := 12518) (a := (83590572820411 / 100000000000000 : ℝ)) (b := (164576899471 / 100000000000000 : ℝ)) (q := (2274494508139 / 100000000000000 : ℝ))
      (E := (cell12518 ⟨14, by decide⟩).energy) (xi := (10595530874949 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12518 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12518]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12518])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12518) (a := (83590572820411 / 100000000000000 : ℝ)) (b := (164576899471 / 100000000000000 : ℝ)) (q := (2274494508139 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12518])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12518])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12518]

theorem cert12518_15 : CellCertificate 12518 (891846018784327 / 10000000000000000 : ℝ) (419486521632937 / 250000000000000000 : ℝ) (10595530874949 / 312500000000000 : ℝ)
    (cell12518 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · have h := gap_lower (n := 12518) (a := (83555885894593 / 100000000000000 : ℝ)) (b := (164576899471 / 100000000000000 : ℝ)) (q := (2274498488559 / 100000000000000 : ℝ))
      (E := (cell12518 ⟨15, by decide⟩).energy) (xi := (10595530874949 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12518 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12518]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12518])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12518) (a := (83555885894593 / 100000000000000 : ℝ)) (b := (164576899471 / 100000000000000 : ℝ)) (q := (2274498488559 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12518])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12518])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12518]

theorem cert12518_16 : CellCertificate 12518 (891846018784327 / 10000000000000000 : ℝ) (419486521632937 / 250000000000000000 : ℝ) (10595530874949 / 312500000000000 : ℝ)
    (cell12518 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · have h := gap_lower (n := 12518) (a := (16704244697999 / 20000000000000 : ℝ)) (b := (164576899471 / 100000000000000 : ℝ)) (q := (2274502518329 / 100000000000000 : ℝ))
      (E := (cell12518 ⟨16, by decide⟩).energy) (xi := (10595530874949 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12518 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12518]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12518])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12518) (a := (16704244697999 / 20000000000000 : ℝ)) (b := (164576899471 / 100000000000000 : ℝ)) (q := (2274502518329 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12518])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12518])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12518]

theorem cert12518_17 : CellCertificate 12518 (891846018784327 / 10000000000000000 : ℝ) (419486521632937 / 250000000000000000 : ℝ) (10595530874949 / 312500000000000 : ℝ)
    (cell12518 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · have h := gap_lower (n := 12518) (a := (8348658557253 / 10000000000000 : ℝ)) (b := (164576899471 / 100000000000000 : ℝ)) (q := (1137253243349 / 50000000000000 : ℝ))
      (E := (cell12518 ⟨17, by decide⟩).energy) (xi := (10595530874949 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12518 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12518]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12518])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12518) (a := (8348658557253 / 10000000000000 : ℝ)) (b := (164576899471 / 100000000000000 : ℝ)) (q := (1137253243349 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12518])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12518])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12518]

theorem cert12518_18 : CellCertificate 12518 (891846018784327 / 10000000000000000 : ℝ) (419486521632937 / 250000000000000000 : ℝ) (10595530874949 / 312500000000000 : ℝ)
    (cell12518 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · have h := gap_lower (n := 12518) (a := (83451972108289 / 100000000000000 : ℝ)) (b := (164576899471 / 100000000000000 : ℝ)) (q := (454902103067 / 20000000000000 : ℝ))
      (E := (cell12518 ⟨18, by decide⟩).energy) (xi := (10595530874949 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12518 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12518]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12518])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12518) (a := (83451972108289 / 100000000000000 : ℝ)) (b := (164576899471 / 100000000000000 : ℝ)) (q := (454902103067 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12518])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12518])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12518]

theorem cert12518_19 : CellCertificate 12518 (891846018784327 / 10000000000000000 : ℝ) (419486521632937 / 250000000000000000 : ℝ) (10595530874949 / 312500000000000 : ℝ)
    (cell12518 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · have h := gap_lower (n := 12518) (a := (5213586441471 / 6250000000000 : ℝ)) (b := (164576899471 / 100000000000000 : ℝ)) (q := (142157155807 / 6250000000000 : ℝ))
      (E := (cell12518 ⟨19, by decide⟩).energy) (xi := (10595530874949 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12518 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12518]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12518])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12518) (a := (5213586441471 / 6250000000000 : ℝ)) (b := (164576899471 / 100000000000000 : ℝ)) (q := (142157155807 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12518])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12518])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12518]

theorem cert12519_0 : CellCertificate 12519 (445908649242487 / 5000000000000000 : ℝ) (419453002466977 / 250000000000000000 : ℝ) (339029220984057 / 10000000000000000 : ℝ)
    (cell12519 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · have h := gap_lower (n := 12519) (a := (42039384228889 / 50000000000000 : ℝ)) (b := (41140896847 / 25000000000000 : ℝ)) (q := (1137154251437 / 50000000000000 : ℝ))
      (E := (cell12519 ⟨0, by decide⟩).energy) (xi := (339029220984057 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12519 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12519]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12519])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12519) (a := (42039384228889 / 50000000000000 : ℝ)) (b := (41140896847 / 25000000000000 : ℝ)) (q := (1137154251437 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12519])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12519])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12519]

theorem cert12519_1 : CellCertificate 12519 (445908649242487 / 5000000000000000 : ℝ) (419453002466977 / 250000000000000000 : ℝ) (339029220984057 / 10000000000000000 : ℝ)
    (cell12519 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · have h := gap_lower (n := 12519) (a := (42021867440611 / 50000000000000 : ℝ)) (b := (41140896847 / 25000000000000 : ℝ)) (q := (1137156238587 / 50000000000000 : ℝ))
      (E := (cell12519 ⟨1, by decide⟩).energy) (xi := (339029220984057 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12519 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12519]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12519])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12519) (a := (42021867440611 / 50000000000000 : ℝ)) (b := (41140896847 / 25000000000000 : ℝ)) (q := (1137156238587 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12519])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12519])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12519]

theorem cert12519_2 : CellCertificate 12519 (445908649242487 / 5000000000000000 : ℝ) (419453002466977 / 250000000000000000 : ℝ) (339029220984057 / 10000000000000000 : ℝ)
    (cell12519 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · have h := gap_lower (n := 12519) (a := (84008726321859 / 100000000000000 : ℝ)) (b := (41140896847 / 25000000000000 : ℝ)) (q := (454863302443 / 20000000000000 : ℝ))
      (E := (cell12519 ⟨2, by decide⟩).energy) (xi := (339029220984057 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12519 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12519]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12519])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12519) (a := (84008726321859 / 100000000000000 : ℝ)) (b := (41140896847 / 25000000000000 : ℝ)) (q := (454863302443 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12519])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12519])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12519]

theorem cert12519_3 : CellCertificate 12519 (445908649242487 / 5000000000000000 : ℝ) (419453002466977 / 250000000000000000 : ℝ) (339029220984057 / 10000000000000000 : ℝ)
    (cell12519 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · have h := gap_lower (n := 12519) (a := (83973742743007 / 100000000000000 : ℝ)) (b := (41140896847 / 25000000000000 : ℝ)) (q := (2274320501567 / 100000000000000 : ℝ))
      (E := (cell12519 ⟨3, by decide⟩).energy) (xi := (339029220984057 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12519 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12519]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12519])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12519) (a := (83973742743007 / 100000000000000 : ℝ)) (b := (41140896847 / 25000000000000 : ℝ)) (q := (2274320501567 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12519])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12519])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12519]

theorem cert12519_4 : CellCertificate 12519 (445908649242487 / 5000000000000000 : ℝ) (419453002466977 / 250000000000000000 : ℝ) (339029220984057 / 10000000000000000 : ℝ)
    (cell12519 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · have h := gap_lower (n := 12519) (a := (83938784108171 / 100000000000000 : ℝ)) (b := (41140896847 / 25000000000000 : ℝ)) (q := (1137162227067 / 50000000000000 : ℝ))
      (E := (cell12519 ⟨4, by decide⟩).energy) (xi := (339029220984057 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12519 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12519]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12519])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12519) (a := (83938784108171 / 100000000000000 : ℝ)) (b := (41140896847 / 25000000000000 : ℝ)) (q := (1137162227067 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12519])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12519])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12519]

theorem cert12519_5 : CellCertificate 12519 (445908649242487 / 5000000000000000 : ℝ) (419453002466977 / 250000000000000000 : ℝ) (339029220984057 / 10000000000000000 : ℝ)
    (cell12519 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · have h := gap_lower (n := 12519) (a := (16780770076211 / 20000000000000 : ℝ)) (b := (41140896847 / 25000000000000 : ℝ)) (q := (568582123593 / 25000000000000 : ℝ))
      (E := (cell12519 ⟨5, by decide⟩).energy) (xi := (339029220984057 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12519 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12519]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12519])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12519) (a := (16780770076211 / 20000000000000 : ℝ)) (b := (41140896847 / 25000000000000 : ℝ)) (q := (568582123593 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12519])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12519])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12519]

theorem cert12519_6 : CellCertificate 12519 (445908649242487 / 5000000000000000 : ℝ) (419453002466977 / 250000000000000000 : ℝ) (339029220984057 / 10000000000000000 : ℝ)
    (cell12519 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · have h := gap_lower (n := 12519) (a := (83868941525549 / 100000000000000 : ℝ)) (b := (41140896847 / 25000000000000 : ℝ)) (q := (2274332457007 / 100000000000000 : ℝ))
      (E := (cell12519 ⟨6, by decide⟩).energy) (xi := (339029220984057 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12519 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12519]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12519])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12519) (a := (83868941525549 / 100000000000000 : ℝ)) (b := (41140896847 / 25000000000000 : ℝ)) (q := (2274332457007 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12519])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12519])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12519]

theorem cert12519_7 : CellCertificate 12519 (445908649242487 / 5000000000000000 : ℝ) (419453002466977 / 250000000000000000 : ℝ) (339029220984057 / 10000000000000000 : ℝ)
    (cell12519 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · have h := gap_lower (n := 12519) (a := (10479257188217 / 12500000000000 : ℝ)) (b := (41140896847 / 25000000000000 : ℝ)) (q := (2274336466009 / 100000000000000 : ℝ))
      (E := (cell12519 ⟨7, by decide⟩).energy) (xi := (339029220984057 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12519 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12519]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12519])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12519) (a := (10479257188217 / 12500000000000 : ℝ)) (b := (41140896847 / 25000000000000 : ℝ)) (q := (2274336466009 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12519])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12519])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12519]

theorem cert12519_8 : CellCertificate 12519 (445908649242487 / 5000000000000000 : ℝ) (419453002466977 / 250000000000000000 : ℝ) (339029220984057 / 10000000000000000 : ℝ)
    (cell12519 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · have h := gap_lower (n := 12519) (a := (41899599142943 / 50000000000000 : ℝ)) (b := (41140896847 / 25000000000000 : ℝ)) (q := (2274340471339 / 100000000000000 : ℝ))
      (E := (cell12519 ⟨8, by decide⟩).energy) (xi := (339029220984057 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12519 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12519]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12519])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12519) (a := (41899599142943 / 50000000000000 : ℝ)) (b := (41140896847 / 25000000000000 : ℝ)) (q := (2274340471339 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12519])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12519])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12519]

theorem cert12519_9 : CellCertificate 12519 (445908649242487 / 5000000000000000 : ℝ) (419453002466977 / 250000000000000000 : ℝ) (339029220984057 / 10000000000000000 : ℝ)
    (cell12519 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · have h := gap_lower (n := 12519) (a := (10470545478807 / 12500000000000 : ℝ)) (b := (41140896847 / 25000000000000 : ℝ)) (q := (2274344480617 / 100000000000000 : ℝ))
      (E := (cell12519 ⟨9, by decide⟩).energy) (xi := (339029220984057 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12519 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12519]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12519])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12519) (a := (10470545478807 / 12500000000000 : ℝ)) (b := (41140896847 / 25000000000000 : ℝ)) (q := (2274344480617 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12519])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12519])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12519]

theorem cert12519_10 : CellCertificate 12519 (445908649242487 / 5000000000000000 : ℝ) (419453002466977 / 250000000000000000 : ℝ) (339029220984057 / 10000000000000000 : ℝ)
    (cell12519 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · have h := gap_lower (n := 12519) (a := (83729554104091 / 100000000000000 : ℝ)) (b := (41140896847 / 25000000000000 : ℝ)) (q := (113717422159 / 5000000000000 : ℝ))
      (E := (cell12519 ⟨10, by decide⟩).energy) (xi := (339029220984057 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12519 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12519]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12519])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12519) (a := (83729554104091 / 100000000000000 : ℝ)) (b := (41140896847 / 25000000000000 : ℝ)) (q := (113717422159 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12519])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12519])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12519]

theorem cert12519_11 : CellCertificate 12519 (445908649242487 / 5000000000000000 : ℝ) (419453002466977 / 250000000000000000 : ℝ) (339029220984057 / 10000000000000000 : ℝ)
    (cell12519 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · have h := gap_lower (n := 12519) (a := (4184738453581 / 5000000000000 : ℝ)) (b := (41140896847 / 25000000000000 : ℝ)) (q := (568588120543 / 25000000000000 : ℝ))
      (E := (cell12519 ⟨11, by decide⟩).energy) (xi := (339029220984057 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12519 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12519]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12519])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12519) (a := (4184738453581 / 5000000000000 : ℝ)) (b := (41140896847 / 25000000000000 : ℝ)) (q := (568588120543 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12519])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12519])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12519]

theorem cert12519_12 : CellCertificate 12519 (445908649242487 / 5000000000000000 : ℝ) (419453002466977 / 250000000000000000 : ℝ) (339029220984057 / 10000000000000000 : ℝ)
    (cell12519 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · have h := gap_lower (n := 12519) (a := (16732001739611 / 20000000000000 : ℝ)) (b := (41140896847 / 25000000000000 : ℝ)) (q := (568589107577 / 25000000000000 : ℝ))
      (E := (cell12519 ⟨12, by decide⟩).energy) (xi := (339029220984057 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12519 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12519]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12519])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12519) (a := (16732001739611 / 20000000000000 : ℝ)) (b := (41140896847 / 25000000000000 : ℝ)) (q := (568589107577 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12519])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12519])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12519]

theorem cert12519_13 : CellCertificate 12519 (445908649242487 / 5000000000000000 : ℝ) (419453002466977 / 250000000000000000 : ℝ) (339029220984057 / 10000000000000000 : ℝ)
    (cell12519 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · have h := gap_lower (n := 12519) (a := (5226579559287 / 6250000000000 : ℝ)) (b := (41140896847 / 25000000000000 : ℝ)) (q := (2274360468349 / 100000000000000 : ℝ))
      (E := (cell12519 ⟨13, by decide⟩).energy) (xi := (339029220984057 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12519 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12519]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12519])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12519) (a := (5226579559287 / 6250000000000 : ℝ)) (b := (41140896847 / 25000000000000 : ℝ)) (q := (2274360468349 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12519])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12519])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12519]

theorem cert12519_14 : CellCertificate 12519 (445908649242487 / 5000000000000000 : ℝ) (419453002466977 / 250000000000000000 : ℝ) (339029220984057 / 10000000000000000 : ℝ)
    (cell12519 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · have h := gap_lower (n := 12519) (a := (83590561788607 / 100000000000000 : ℝ)) (b := (41140896847 / 25000000000000 : ℝ)) (q := (2274364428373 / 100000000000000 : ℝ))
      (E := (cell12519 ⟨14, by decide⟩).energy) (xi := (339029220984057 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12519 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12519]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12519])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12519) (a := (83590561788607 / 100000000000000 : ℝ)) (b := (41140896847 / 25000000000000 : ℝ)) (q := (2274364428373 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12519])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12519])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12519]

theorem cert12519_15 : CellCertificate 12519 (445908649242487 / 5000000000000000 : ℝ) (419453002466977 / 250000000000000000 : ℝ) (339029220984057 / 10000000000000000 : ℝ)
    (cell12519 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · have h := gap_lower (n := 12519) (a := (83555875183657 / 100000000000000 : ℝ)) (b := (41140896847 / 25000000000000 : ℝ)) (q := (1137184216323 / 50000000000000 : ℝ))
      (E := (cell12519 ⟨15, by decide⟩).energy) (xi := (339029220984057 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12519 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12519]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12519])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12519) (a := (83555875183657 / 100000000000000 : ℝ)) (b := (41140896847 / 25000000000000 : ℝ)) (q := (1137184216323 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12519])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12519])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12519]

theorem cert12519_16 : CellCertificate 12519 (445908649242487 / 5000000000000000 : ℝ) (419453002466977 / 250000000000000000 : ℝ) (339029220984057 / 10000000000000000 : ℝ)
    (cell12519 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · have h := gap_lower (n := 12519) (a := (83521213099477 / 100000000000000 : ℝ)) (b := (41140896847 / 25000000000000 : ℝ)) (q := (2274372428873 / 100000000000000 : ℝ))
      (E := (cell12519 ⟨16, by decide⟩).energy) (xi := (339029220984057 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12519 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12519]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12519])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12519) (a := (83521213099477 / 100000000000000 : ℝ)) (b := (41140896847 / 25000000000000 : ℝ)) (q := (2274372428873 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12519])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12519])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12519]

theorem cert12519_17 : CellCertificate 12519 (445908649242487 / 5000000000000000 : ℝ) (419453002466977 / 250000000000000000 : ℝ) (339029220984057 / 10000000000000000 : ℝ)
    (cell12519 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · have h := gap_lower (n := 12519) (a := (41743287750991 / 50000000000000 : ℝ)) (b := (41140896847 / 25000000000000 : ℝ)) (q := (568594105653 / 25000000000000 : ℝ))
      (E := (cell12519 ⟨17, by decide⟩).energy) (xi := (339029220984057 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12519 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12519]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12519])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12519) (a := (41743287750991 / 50000000000000 : ℝ)) (b := (41140896847 / 25000000000000 : ℝ)) (q := (568594105653 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12519])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12519])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12519]

theorem cert12519_18 : CellCertificate 12519 (445908649242487 / 5000000000000000 : ℝ) (419453002466977 / 250000000000000000 : ℝ) (339029220984057 / 10000000000000000 : ℝ)
    (cell12519 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · have h := gap_lower (n := 12519) (a := (83451962357263 / 100000000000000 : ℝ)) (b := (41140896847 / 25000000000000 : ℝ)) (q := (2274380419177 / 100000000000000 : ℝ))
      (E := (cell12519 ⟨18, by decide⟩).energy) (xi := (339029220984057 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12519 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12519]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12519])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12519) (a := (83451962357263 / 100000000000000 : ℝ)) (b := (41140896847 / 25000000000000 : ℝ)) (q := (2274380419177 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12519])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12519])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12519]

theorem cert12519_19 : CellCertificate 12519 (445908649242487 / 5000000000000000 : ℝ) (419453002466977 / 250000000000000000 : ℝ) (339029220984057 / 10000000000000000 : ℝ)
    (cell12519 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · have h := gap_lower (n := 12519) (a := (2606792925987 / 3125000000000 : ℝ)) (b := (41140896847 / 25000000000000 : ℝ)) (q := (1137192211821 / 50000000000000 : ℝ))
      (E := (cell12519 ⟨19, by decide⟩).energy) (xi := (339029220984057 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12519 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12519]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12519])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12519) (a := (2606792925987 / 3125000000000 : ℝ)) (b := (41140896847 / 25000000000000 : ℝ)) (q := (1137192211821 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12519])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12519])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12519]

theorem cert12520_0 : CellCertificate 12520 (178357716519407 / 2000000000000000 : ℝ) (209709744328651 / 125000000000000000 : ℝ) (339001458598949 / 10000000000000000 : ℝ)
    (cell12520 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · have h := gap_lower (n := 12520) (a := (8407875288853 / 10000000000000 : ℝ)) (b := (82275138739 / 50000000000000 : ℝ)) (q := (284272314069 / 12500000000000 : ℝ))
      (E := (cell12520 ⟨0, by decide⟩).energy) (xi := (339001458598949 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12520 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12520]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12520])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12520) (a := (8407875288853 / 10000000000000 : ℝ)) (b := (82275138739 / 50000000000000 : ℝ)) (q := (284272314069 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12520])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12520])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12520]

theorem cert12520_1 : CellCertificate 12520 (178357716519407 / 2000000000000000 : ℝ) (209709744328651 / 125000000000000000 : ℝ) (339001458598949 / 10000000000000000 : ℝ)
    (cell12520 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · have h := gap_lower (n := 12520) (a := (84043719639201 / 100000000000000 : ℝ)) (b := (82275138739 / 50000000000000 : ℝ)) (q := (2274182499981 / 100000000000000 : ℝ))
      (E := (cell12520 ⟨1, by decide⟩).energy) (xi := (339001458598949 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12520 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12520]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12520])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12520) (a := (84043719639201 / 100000000000000 : ℝ)) (b := (82275138739 / 50000000000000 : ℝ)) (q := (2274182499981 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12520])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12520])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12520]

theorem cert12520_2 : CellCertificate 12520 (178357716519407 / 2000000000000000 : ℝ) (209709744328651 / 125000000000000000 : ℝ) (339001458598949 / 10000000000000000 : ℝ)
    (cell12520 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · have h := gap_lower (n := 12520) (a := (21002177851651 / 25000000000000 : ℝ)) (b := (82275138739 / 50000000000000 : ℝ)) (q := (454837298219 / 20000000000000 : ℝ))
      (E := (cell12520 ⟨2, by decide⟩).energy) (xi := (339001458598949 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12520 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12520]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12520])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12520) (a := (21002177851651 / 25000000000000 : ℝ)) (b := (82275138739 / 50000000000000 : ℝ)) (q := (454837298219 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12520])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12520])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12520]

theorem cert12520_3 : CellCertificate 12520 (178357716519407 / 2000000000000000 : ℝ) (209709744328651 / 125000000000000000 : ℝ) (339001458598949 / 10000000000000000 : ℝ)
    (cell12520 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · have h := gap_lower (n := 12520) (a := (83973728154053 / 100000000000000 : ℝ)) (b := (82275138739 / 50000000000000 : ℝ)) (q := (2274190495123 / 100000000000000 : ℝ))
      (E := (cell12520 ⟨3, by decide⟩).energy) (xi := (339001458598949 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12520 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12520]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12520])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12520) (a := (83973728154053 / 100000000000000 : ℝ)) (b := (82275138739 / 50000000000000 : ℝ)) (q := (2274190495123 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12520])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12520])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12520]

theorem cert12520_4 : CellCertificate 12520 (178357716519407 / 2000000000000000 : ℝ) (209709744328651 / 125000000000000000 : ℝ) (339001458598949 / 10000000000000000 : ℝ)
    (cell12520 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · have h := gap_lower (n := 12520) (a := (41969384922529 / 50000000000000 : ℝ)) (b := (82275138739 / 50000000000000 : ℝ)) (q := (2274194463147 / 100000000000000 : ℝ))
      (E := (cell12520 ⟨4, by decide⟩).energy) (xi := (339001458598949 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12520 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12520]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12520])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12520) (a := (41969384922529 / 50000000000000 : ℝ)) (b := (82275138739 / 50000000000000 : ℝ)) (q := (2274194463147 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12520])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12520])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12520]

theorem cert12520_5 : CellCertificate 12520 (178357716519407 / 2000000000000000 : ℝ) (209709744328651 / 125000000000000000 : ℝ) (339001458598949 / 10000000000000000 : ℝ)
    (cell12520 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · have h := gap_lower (n := 12520) (a := (83903836443321 / 100000000000000 : ℝ)) (b := (82275138739 / 50000000000000 : ℝ)) (q := (568549615429 / 25000000000000 : ℝ))
      (E := (cell12520 ⟨5, by decide⟩).energy) (xi := (339001458598949 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12520 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12520]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12520])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12520) (a := (83903836443321 / 100000000000000 : ℝ)) (b := (82275138739 / 50000000000000 : ℝ)) (q := (568549615429 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12520])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12520])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12520]

theorem cert12520_6 : CellCertificate 12520 (178357716519407 / 2000000000000000 : ℝ) (209709744328651 / 125000000000000000 : ℝ) (339001458598949 / 10000000000000000 : ℝ)
    (cell12520 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · have h := gap_lower (n := 12520) (a := (2620903997273 / 3125000000000 : ℝ)) (b := (82275138739 / 50000000000000 : ℝ)) (q := (2274202499281 / 100000000000000 : ℝ))
      (E := (cell12520 ⟨6, by decide⟩).energy) (xi := (339001458598949 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12520 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12520]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12520])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12520) (a := (2620903997273 / 3125000000000 : ℝ)) (b := (82275138739 / 50000000000000 : ℝ)) (q := (2274202499281 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12520])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12520])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12520]

theorem cert12520_7 : CellCertificate 12520 (178357716519407 / 2000000000000000 : ℝ) (209709744328651 / 125000000000000000 : ℝ) (339001458598949 / 10000000000000000 : ℝ)
    (cell12520 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · have h := gap_lower (n := 12520) (a := (16766808843477 / 20000000000000 : ℝ)) (b := (82275138739 / 50000000000000 : ℝ)) (q := (71068952129 / 3125000000000 : ℝ))
      (E := (cell12520 ⟨7, by decide⟩).energy) (xi := (339001458598949 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12520 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12520]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12520])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12520) (a := (16766808843477 / 20000000000000 : ℝ)) (b := (82275138739 / 50000000000000 : ℝ)) (q := (71068952129 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12520])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12520])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12520]

theorem cert12520_8 : CellCertificate 12520 (178357716519407 / 2000000000000000 : ℝ) (209709744328651 / 125000000000000000 : ℝ) (339001458598949 / 10000000000000000 : ℝ)
    (cell12520 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · have h := gap_lower (n := 12520) (a := (83799185321539 / 100000000000000 : ℝ)) (b := (82275138739 / 50000000000000 : ℝ)) (q := (142138155751 / 6250000000000 : ℝ))
      (E := (cell12520 ⟨8, by decide⟩).energy) (xi := (339001458598949 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12520 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12520]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12520])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12520) (a := (83799185321539 / 100000000000000 : ℝ)) (b := (82275138739 / 50000000000000 : ℝ)) (q := (142138155751 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12520])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12520])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12520]

theorem cert12520_9 : CellCertificate 12520 (178357716519407 / 2000000000000000 : ℝ) (209709744328651 / 125000000000000000 : ℝ) (339001458598949 / 10000000000000000 : ℝ)
    (cell12520 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · have h := gap_lower (n := 12520) (a := (83764351189657 / 100000000000000 : ℝ)) (b := (82275138739 / 50000000000000 : ℝ)) (q := (2274214462627 / 100000000000000 : ℝ))
      (E := (cell12520 ⟨9, by decide⟩).energy) (xi := (339001458598949 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12520 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12520]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12520])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12520) (a := (83764351189657 / 100000000000000 : ℝ)) (b := (82275138739 / 50000000000000 : ℝ)) (q := (2274214462627 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12520])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12520])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12520]

theorem cert12520_10 : CellCertificate 12520 (178357716519407 / 2000000000000000 : ℝ) (209709744328651 / 125000000000000000 : ℝ) (339001458598949 / 10000000000000000 : ℝ)
    (cell12520 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · have h := gap_lower (n := 12520) (a := (5233096361649 / 6250000000000 : ℝ)) (b := (82275138739 / 50000000000000 : ℝ)) (q := (14213865283 / 625000000000 : ℝ))
      (E := (cell12520 ⟨10, by decide⟩).energy) (xi := (339001458598949 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12520 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12520]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12520])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12520) (a := (5233096361649 / 6250000000000 : ℝ)) (b := (82275138739 / 50000000000000 : ℝ)) (q := (14213865283 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12520])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12520])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12520]

theorem cert12520_11 : CellCertificate 12520 (178357716519407 / 2000000000000000 : ℝ) (209709744328651 / 125000000000000000 : ℝ) (339001458598949 / 10000000000000000 : ℝ)
    (cell12520 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · have h := gap_lower (n := 12520) (a := (83694757076551 / 100000000000000 : ℝ)) (b := (82275138739 / 50000000000000 : ℝ)) (q := (142138902943 / 6250000000000 : ℝ))
      (E := (cell12520 ⟨11, by decide⟩).energy) (xi := (339001458598949 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12520 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12520]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12520])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12520) (a := (83694757076551 / 100000000000000 : ℝ)) (b := (82275138739 / 50000000000000 : ℝ)) (q := (142138902943 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12520])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12520])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12520]

theorem cert12520_12 : CellCertificate 12520 (178357716519407 / 2000000000000000 : ℝ) (209709744328651 / 125000000000000000 : ℝ) (339001458598949 / 10000000000000000 : ℝ)
    (cell12520 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · have h := gap_lower (n := 12520) (a := (8365999702517 / 10000000000000 : ℝ)) (b := (82275138739 / 50000000000000 : ℝ)) (q := (454845294983 / 20000000000000 : ℝ))
      (E := (cell12520 ⟨12, by decide⟩).energy) (xi := (339001458598949 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12520 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12520]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12520])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12520) (a := (8365999702517 / 10000000000000 : ℝ)) (b := (82275138739 / 50000000000000 : ℝ)) (q := (454845294983 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12520])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12520])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12520]

theorem cert12520_13 : CellCertificate 12520 (178357716519407 / 2000000000000000 : ℝ) (209709744328651 / 125000000000000000 : ℝ) (339001458598949 / 10000000000000000 : ℝ)
    (cell12520 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · have h := gap_lower (n := 12520) (a := (41812630798719 / 50000000000000 : ℝ)) (b := (82275138739 / 50000000000000 : ℝ)) (q := (568557619319 / 25000000000000 : ℝ))
      (E := (cell12520 ⟨13, by decide⟩).energy) (xi := (339001458598949 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12520 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12520]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12520])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12520) (a := (41812630798719 / 50000000000000 : ℝ)) (b := (82275138739 / 50000000000000 : ℝ)) (q := (568557619319 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12520])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12520])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12520]

theorem cert12520_14 : CellCertificate 12520 (178357716519407 / 2000000000000000 : ℝ) (209709744328651 / 125000000000000000 : ℝ) (339001458598949 / 10000000000000000 : ℝ)
    (cell12520 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · have h := gap_lower (n := 12520) (a := (83590550758733 / 100000000000000 : ℝ)) (b := (82275138739 / 50000000000000 : ℝ)) (q := (2274234460467 / 100000000000000 : ℝ))
      (E := (cell12520 ⟨14, by decide⟩).energy) (xi := (339001458598949 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12520 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12520]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12520])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12520) (a := (83590550758733 / 100000000000000 : ℝ)) (b := (82275138739 / 50000000000000 : ℝ)) (q := (2274234460467 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12520])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12520])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12520]

theorem cert12520_15 : CellCertificate 12520 (178357716519407 / 2000000000000000 : ℝ) (209709744328651 / 125000000000000000 : ℝ) (339001458598949 / 10000000000000000 : ℝ)
    (cell12520 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · have h := gap_lower (n := 12520) (a := (20888966118653 / 25000000000000 : ℝ)) (b := (82275138739 / 50000000000000 : ℝ)) (q := (454847686107 / 20000000000000 : ℝ))
      (E := (cell12520 ⟨15, by decide⟩).energy) (xi := (339001458598949 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12520 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12520]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12520])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12520) (a := (20888966118653 / 25000000000000 : ℝ)) (b := (82275138739 / 50000000000000 : ℝ)) (q := (454847686107 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12520])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12520])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12520]

theorem cert12520_16 : CellCertificate 12520 (178357716519407 / 2000000000000000 : ℝ) (209709744328651 / 125000000000000000 : ℝ) (339001458598949 / 10000000000000000 : ℝ)
    (cell12520 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · have h := gap_lower (n := 12520) (a := (83521202710811 / 100000000000000 : ℝ)) (b := (82275138739 / 50000000000000 : ℝ)) (q := (45484849029 / 2000000000000 : ℝ))
      (E := (cell12520 ⟨16, by decide⟩).energy) (xi := (339001458598949 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12520 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12520]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12520])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12520) (a := (83521202710811 / 100000000000000 : ℝ)) (b := (82275138739 / 50000000000000 : ℝ)) (q := (45484849029 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12520])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12520])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12520]

theorem cert12520_17 : CellCertificate 12520 (178357716519407 / 2000000000000000 : ℝ) (209709744328651 / 125000000000000000 : ℝ) (339001458598949 / 10000000000000000 : ℝ)
    (cell12520 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · have h := gap_lower (n := 12520) (a := (83486565433247 / 100000000000000 : ℝ)) (b := (82275138739 / 50000000000000 : ℝ)) (q := (2274246470647 / 100000000000000 : ℝ))
      (E := (cell12520 ⟨17, by decide⟩).energy) (xi := (339001458598949 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12520 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12520]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12520])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12520) (a := (83486565433247 / 100000000000000 : ℝ)) (b := (82275138739 / 50000000000000 : ℝ)) (q := (2274246470647 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12520])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12520])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12520]

theorem cert12520_18 : CellCertificate 12520 (178357716519407 / 2000000000000000 : ℝ) (209709744328651 / 125000000000000000 : ℝ) (339001458598949 / 10000000000000000 : ℝ)
    (cell12520 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · have h := gap_lower (n := 12520) (a := (83451952608009 / 100000000000000 : ℝ)) (b := (82275138739 / 50000000000000 : ℝ)) (q := (568562608807 / 25000000000000 : ℝ))
      (E := (cell12520 ⟨18, by decide⟩).energy) (xi := (339001458598949 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12520 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12520]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12520])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12520) (a := (83451952608009 / 100000000000000 : ℝ)) (b := (82275138739 / 50000000000000 : ℝ)) (q := (568562608807 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12520])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12520])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12520]

theorem cert12520_19 : CellCertificate 12520 (178357716519407 / 2000000000000000 : ℝ) (209709744328651 / 125000000000000000 : ℝ) (339001458598949 / 10000000000000000 : ℝ)
    (cell12520 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · have h := gap_lower (n := 12520) (a := (41708682100683 / 50000000000000 : ℝ)) (b := (82275138739 / 50000000000000 : ℝ)) (q := (1137127233333 / 50000000000000 : ℝ))
      (E := (cell12520 ⟨19, by decide⟩).energy) (xi := (339001458598949 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12520 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12520]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12520])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12520) (a := (41708682100683 / 50000000000000 : ℝ)) (b := (82275138739 / 50000000000000 : ℝ)) (q := (1137127233333 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12520])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12520])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12520]

theorem cert12521_0 : CellCertificate 12521 (222939967779861 / 2500000000000000 : ℝ) (167754392081051 / 100000000000000000 : ℝ) (84743425210441 / 2500000000000000 : ℝ)
    (cell12521 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · have h := gap_lower (n := 12521) (a := (21019684330443 / 25000000000000 : ℝ)) (b := (8226848487 / 5000000000000 : ℝ)) (q := (90961940691 / 4000000000000 : ℝ))
      (E := (cell12521 ⟨0, by decide⟩).energy) (xi := (84743425210441 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12521 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12521]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12521])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12521) (a := (21019684330443 / 25000000000000 : ℝ)) (b := (8226848487 / 5000000000000 : ℝ)) (q := (90961940691 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12521])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12521])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12521]

theorem cert12521_1 : CellCertificate 12521 (222939967779861 / 2500000000000000 : ℝ) (167754392081051 / 100000000000000000 : ℝ) (84743425210441 / 2500000000000000 : ℝ)
    (cell12521 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · have h := gap_lower (n := 12521) (a := (84043704399631 / 100000000000000 : ℝ)) (b := (8226848487 / 5000000000000 : ℝ)) (q := (18192420143 / 800000000000 : ℝ))
      (E := (cell12521 ⟨1, by decide⟩).energy) (xi := (84743425210441 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12521 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12521]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12521])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12521) (a := (84043704399631 / 100000000000000 : ℝ)) (b := (8226848487 / 5000000000000 : ℝ)) (q := (18192420143 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12521])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12521])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12521]

theorem cert12521_2 : CellCertificate 12521 (222939967779861 / 2500000000000000 : ℝ) (167754392081051 / 100000000000000000 : ℝ) (84743425210441 / 2500000000000000 : ℝ)
    (cell12521 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · have h := gap_lower (n := 12521) (a := (84008696493757 / 100000000000000 : ℝ)) (b := (8226848487 / 5000000000000 : ℝ)) (q := (454811304589 / 20000000000000 : ℝ))
      (E := (cell12521 ⟨2, by decide⟩).energy) (xi := (84743425210441 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12521 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12521]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12521])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12521) (a := (84008696493757 / 100000000000000 : ℝ)) (b := (8226848487 / 5000000000000 : ℝ)) (q := (454811304589 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12521])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12521])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12521]

theorem cert12521_3 : CellCertificate 12521 (222939967779861 / 2500000000000000 : ℝ) (167754392081051 / 100000000000000000 : ℝ) (84743425210441 / 2500000000000000 : ℝ)
    (cell12521 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · have h := gap_lower (n := 12521) (a := (20993428391867 / 25000000000000 : ℝ)) (b := (8226848487 / 5000000000000 : ℝ)) (q := (2274060541711 / 100000000000000 : ℝ))
      (E := (cell12521 ⟨3, by decide⟩).energy) (xi := (84743425210441 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12521 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12521]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12521])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12521) (a := (20993428391867 / 25000000000000 : ℝ)) (b := (8226848487 / 5000000000000 : ℝ)) (q := (2274060541711 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12521])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12521])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12521]

theorem cert12521_4 : CellCertificate 12521 (222939967779861 / 2500000000000000 : ℝ) (167754392081051 / 100000000000000000 : ℝ) (84743425210441 / 2500000000000000 : ℝ)
    (cell12521 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · have h := gap_lower (n := 12521) (a := (83938755584273 / 100000000000000 : ℝ)) (b := (8226848487 / 5000000000000 : ℝ)) (q := (1137032262629 / 50000000000000 : ℝ))
      (E := (cell12521 ⟨4, by decide⟩).energy) (xi := (84743425210441 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12521 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12521]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12521])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12521) (a := (83938755584273 / 100000000000000 : ℝ)) (b := (8226848487 / 5000000000000 : ℝ)) (q := (1137032262629 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12521])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12521])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12521]

theorem cert12521_5 : CellCertificate 12521 (222939967779861 / 2500000000000000 : ℝ) (167754392081051 / 100000000000000000 : ℝ) (84743425210441 / 2500000000000000 : ℝ)
    (cell12521 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · have h := gap_lower (n := 12521) (a := (83903822507877 / 100000000000000 : ℝ)) (b := (8226848487 / 5000000000000 : ℝ)) (q := (2274068540131 / 100000000000000 : ℝ))
      (E := (cell12521 ⟨5, by decide⟩).energy) (xi := (84743425210441 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12521 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12521]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12521])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12521) (a := (83903822507877 / 100000000000000 : ℝ)) (b := (8226848487 / 5000000000000 : ℝ)) (q := (2274068540131 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12521])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12521])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12521]

theorem cert12521_6 : CellCertificate 12521 (222939967779861 / 2500000000000000 : ℝ) (167754392081051 / 100000000000000000 : ℝ) (84743425210441 / 2500000000000000 : ℝ)
    (cell12521 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · have h := gap_lower (n := 12521) (a := (20967228575543 / 25000000000000 : ℝ)) (b := (8226848487 / 5000000000000 : ℝ)) (q := (2274072536849 / 100000000000000 : ℝ))
      (E := (cell12521 ⟨6, by decide⟩).energy) (xi := (84743425210441 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12521 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12521]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12521])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12521) (a := (20967228575543 / 25000000000000 : ℝ)) (b := (8226848487 / 5000000000000 : ℝ)) (q := (2274072536849 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12521])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12521])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12521]

theorem cert12521_7 : CellCertificate 12521 (222939967779861 / 2500000000000000 : ℝ) (167754392081051 / 100000000000000000 : ℝ) (84743425210441 / 2500000000000000 : ℝ)
    (cell12521 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · have h := gap_lower (n := 12521) (a := (41917015465621 / 50000000000000 : ℝ)) (b := (8226848487 / 5000000000000 : ℝ)) (q := (2274076523539 / 100000000000000 : ℝ))
      (E := (cell12521 ⟨7, by decide⟩).energy) (xi := (84743425210441 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12521 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12521]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12521])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12521) (a := (41917015465621 / 50000000000000 : ℝ)) (b := (8226848487 / 5000000000000 : ℝ)) (q := (2274076523539 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12521])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12521])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12521]

theorem cert12521_8 : CellCertificate 12521 (222939967779861 / 2500000000000000 : ℝ) (167754392081051 / 100000000000000000 : ℝ) (84743425210441 / 2500000000000000 : ℝ)
    (cell12521 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · have h := gap_lower (n := 12521) (a := (261872413623 / 312500000000 : ℝ)) (b := (8226848487 / 5000000000000 : ℝ)) (q := (227408050807 / 10000000000000 : ℝ))
      (E := (cell12521 ⟨8, by decide⟩).energy) (xi := (84743425210441 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12521 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12521]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12521])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12521) (a := (261872413623 / 312500000000 : ℝ)) (b := (8226848487 / 5000000000000 : ℝ)) (q := (227408050807 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12521])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12521])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12521]

theorem cert12521_9 : CellCertificate 12521 (222939967779861 / 2500000000000000 : ℝ) (167754392081051 / 100000000000000000 : ℝ) (84743425210441 / 2500000000000000 : ℝ)
    (cell12521 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · have h := gap_lower (n := 12521) (a := (83764338550987 / 100000000000000 : ℝ)) (b := (8226848487 / 5000000000000 : ℝ)) (q := (284260562257 / 12500000000000 : ℝ))
      (E := (cell12521 ⟨9, by decide⟩).energy) (xi := (84743425210441 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12521 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12521]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12521])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12521) (a := (83764338550987 / 100000000000000 : ℝ)) (b := (8226848487 / 5000000000000 : ℝ)) (q := (284260562257 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12521])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12521])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12521]

theorem cert12521_10 : CellCertificate 12521 (222939967779861 / 2500000000000000 : ℝ) (167754392081051 / 100000000000000000 : ℝ) (84743425210441 / 2500000000000000 : ℝ)
    (cell12521 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · have h := gap_lower (n := 12521) (a := (41864764735383 / 50000000000000 : ℝ)) (b := (8226848487 / 5000000000000 : ℝ)) (q := (17766316413 / 781250000000 : ℝ))
      (E := (cell12521 ⟨10, by decide⟩).energy) (xi := (84743425210441 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12521 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12521]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12521])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12521) (a := (41864764735383 / 50000000000000 : ℝ)) (b := (8226848487 / 5000000000000 : ℝ)) (q := (17766316413 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12521])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12521])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12521]

theorem cert12521_11 : CellCertificate 12521 (222939967779861 / 2500000000000000 : ℝ) (167754392081051 / 100000000000000000 : ℝ) (84743425210441 / 2500000000000000 : ℝ)
    (cell12521 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · have h := gap_lower (n := 12521) (a := (83694745083531 / 100000000000000 : ℝ)) (b := (8226848487 / 5000000000000 : ℝ)) (q := (1137046261801 / 50000000000000 : ℝ))
      (E := (cell12521 ⟨11, by decide⟩).energy) (xi := (84743425210441 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12521 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12521]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12521])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12521) (a := (83694745083531 / 100000000000000 : ℝ)) (b := (8226848487 / 5000000000000 : ℝ)) (q := (1137046261801 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12521])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12521])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12521]

theorem cert12521_12 : CellCertificate 12521 (222939967779861 / 2500000000000000 : ℝ) (167754392081051 / 100000000000000000 : ℝ) (84743425210441 / 2500000000000000 : ℝ)
    (cell12521 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · have h := gap_lower (n := 12521) (a := (41829992677147 / 50000000000000 : ℝ)) (b := (8226848487 / 5000000000000 : ℝ)) (q := (1137048257531 / 50000000000000 : ℝ))
      (E := (cell12521 ⟨12, by decide⟩).energy) (xi := (84743425210441 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12521 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12521]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12521])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12521) (a := (41829992677147 / 50000000000000 : ℝ)) (b := (8226848487 / 5000000000000 : ℝ)) (q := (1137048257531 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12521])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12521])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12521]

theorem cert12521_13 : CellCertificate 12521 (222939967779861 / 2500000000000000 : ℝ) (167754392081051 / 100000000000000000 : ℝ) (84743425210441 / 2500000000000000 : ℝ)
    (cell12521 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · have h := gap_lower (n := 12521) (a := (41812625124127 / 50000000000000 : ℝ)) (b := (8226848487 / 5000000000000 : ℝ)) (q := (284262560223 / 12500000000000 : ℝ))
      (E := (cell12521 ⟨13, by decide⟩).energy) (xi := (84743425210441 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12521 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12521]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12521])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12521) (a := (41812625124127 / 50000000000000 : ℝ)) (b := (8226848487 / 5000000000000 : ℝ)) (q := (284262560223 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12521])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12521])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12521]

theorem cert12521_14 : CellCertificate 12521 (222939967779861 / 2500000000000000 : ℝ) (167754392081051 / 100000000000000000 : ℝ) (84743425210441 / 2500000000000000 : ℝ)
    (cell12521 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · have h := gap_lower (n := 12521) (a := (83590539730789 / 100000000000000 : ℝ)) (b := (8226848487 / 5000000000000 : ℝ)) (q := (2274104488181 / 100000000000000 : ℝ))
      (E := (cell12521 ⟨14, by decide⟩).energy) (xi := (84743425210441 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12521 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12521]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12521])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12521) (a := (83590539730789 / 100000000000000 : ℝ)) (b := (8226848487 / 5000000000000 : ℝ)) (q := (2274104488181 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12521])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12521])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12521]

theorem cert12521_15 : CellCertificate 12521 (222939967779861 / 2500000000000000 : ℝ) (167754392081051 / 100000000000000000 : ℝ) (84743425210441 / 2500000000000000 : ℝ)
    (cell12521 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · have h := gap_lower (n := 12521) (a := (83555853767457 / 100000000000000 : ℝ)) (b := (8226848487 / 5000000000000 : ℝ)) (q := (2274108482229 / 100000000000000 : ℝ))
      (E := (cell12521 ⟨15, by decide⟩).energy) (xi := (84743425210441 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12521 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12521]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12521])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12521) (a := (83555853767457 / 100000000000000 : ℝ)) (b := (8226848487 / 5000000000000 : ℝ)) (q := (2274108482229 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12521])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12521])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12521]

theorem cert12521_16 : CellCertificate 12521 (222939967779861 / 2500000000000000 : ℝ) (167754392081051 / 100000000000000000 : ℝ) (84743425210441 / 2500000000000000 : ℝ)
    (cell12521 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · have h := gap_lower (n := 12521) (a := (83521192323997 / 100000000000000 : ℝ)) (b := (8226848487 / 5000000000000 : ℝ)) (q := (454822505579 / 20000000000000 : ℝ))
      (E := (cell12521 ⟨16, by decide⟩).energy) (xi := (84743425210441 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12521 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12521]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12521])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12521) (a := (83521192323997 / 100000000000000 : ℝ)) (b := (8226848487 / 5000000000000 : ℝ)) (q := (454822505579 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12521])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12521])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12521]

theorem cert12521_17 : CellCertificate 12521 (222939967779861 / 2500000000000000 : ℝ) (167754392081051 / 100000000000000000 : ℝ) (84743425210441 / 2500000000000000 : ℝ)
    (cell12521 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · have h := gap_lower (n := 12521) (a := (83486555366323 / 100000000000000 : ℝ)) (b := (8226848487 / 5000000000000 : ℝ)) (q := (90964660577 / 4000000000000 : ℝ))
      (E := (cell12521 ⟨17, by decide⟩).energy) (xi := (84743425210441 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12521 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12521]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12521])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12521) (a := (83486555366323 / 100000000000000 : ℝ)) (b := (8226848487 / 5000000000000 : ℝ)) (q := (90964660577 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12521])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12521])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12521]

theorem cert12521_18 : CellCertificate 12521 (222939967779861 / 2500000000000000 : ℝ) (167754392081051 / 100000000000000000 : ℝ) (84743425210441 / 2500000000000000 : ℝ)
    (cell12521 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · have h := gap_lower (n := 12521) (a := (5215746428783 / 6250000000000 : ℝ)) (b := (8226848487 / 5000000000000 : ℝ)) (q := (90964820211 / 4000000000000 : ℝ))
      (E := (cell12521 ⟨18, by decide⟩).energy) (xi := (84743425210441 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12521 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12521]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12521])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12521) (a := (5215746428783 / 6250000000000 : ℝ)) (b := (8226848487 / 5000000000000 : ℝ)) (q := (90964820211 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12521])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12521])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12521]

theorem cert12521_19 : CellCertificate 12521 (222939967779861 / 2500000000000000 : ℝ) (167754392081051 / 100000000000000000 : ℝ) (84743425210441 / 2500000000000000 : ℝ)
    (cell12521 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · have h := gap_lower (n := 12521) (a := (83417354772881 / 100000000000000 : ℝ)) (b := (8226848487 / 5000000000000 : ℝ)) (q := (2274124505513 / 100000000000000 : ℝ))
      (E := (cell12521 ⟨19, by decide⟩).energy) (xi := (84743425210441 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12521 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12521]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12521])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12521) (a := (83417354772881 / 100000000000000 : ℝ)) (b := (8226848487 / 5000000000000 : ℝ)) (q := (2274124505513 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12521])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12521])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12521]

theorem cert12522_0 : CellCertificate 12522 (445865582025569 / 5000000000000000 : ℝ) (1677409908406683 / 1000000000000000000 : ℝ) (338945947711227 / 10000000000000000 : ℝ)
    (cell12522 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · have h := gap_lower (n := 12522) (a := (1313730027461 / 1562500000000 : ℝ)) (b := (6580946567 / 4000000000000 : ℝ)) (q := (568479658157 / 25000000000000 : ℝ))
      (E := (cell12522 ⟨0, by decide⟩).energy) (xi := (338945947711227 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12522 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12522]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12522])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12522) (a := (1313730027461 / 1562500000000 : ℝ)) (b := (6580946567 / 4000000000000 : ℝ)) (q := (568479658157 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12522])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12522])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12522]

theorem cert12522_1 : CellCertificate 12522 (445865582025569 / 5000000000000000 : ℝ) (1677409908406683 / 1000000000000000000 : ℝ) (338945947711227 / 10000000000000000 : ℝ)
    (cell12522 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · have h := gap_lower (n := 12522) (a := (8404368916251 / 10000000000000 : ℝ)) (b := (6580946567 / 4000000000000 : ℝ)) (q := (1136961323243 / 50000000000000 : ℝ))
      (E := (cell12522 ⟨1, by decide⟩).energy) (xi := (338945947711227 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12522 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12522]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12522])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12522) (a := (8404368916251 / 10000000000000 : ℝ)) (b := (6580946567 / 4000000000000 : ℝ)) (q := (1136961323243 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12522])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12522])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12522]

theorem cert12522_2 : CellCertificate 12522 (445865582025569 / 5000000000000000 : ℝ) (1677409908406683 / 1000000000000000000 : ℝ) (338945947711227 / 10000000000000000 : ℝ)
    (cell12522 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · have h := gap_lower (n := 12522) (a := (2100217039583 / 2500000000000 : ℝ)) (b := (6580946567 / 4000000000000 : ℝ)) (q := (28424082597 / 1250000000000 : ℝ))
      (E := (cell12522 ⟨2, by decide⟩).energy) (xi := (338945947711227 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12522 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12522]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12522])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12522) (a := (2100217039583 / 2500000000000 : ℝ)) (b := (6580946567 / 4000000000000 : ℝ)) (q := (28424082597 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12522])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12522])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12522]

theorem cert12522_3 : CellCertificate 12522 (445865582025569 / 5000000000000000 : ℝ) (1677409908406683 / 1000000000000000000 : ℝ) (338945947711227 / 10000000000000000 : ℝ)
    (cell12522 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · have h := gap_lower (n := 12522) (a := (20993424745813 / 25000000000000 : ℝ)) (b := (6580946567 / 4000000000000 : ℝ)) (q := (568482660333 / 25000000000000 : ℝ))
      (E := (cell12522 ⟨3, by decide⟩).energy) (xi := (338945947711227 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12522 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12522]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12522])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12522) (a := (20993424745813 / 25000000000000 : ℝ)) (b := (6580946567 / 4000000000000 : ℝ)) (q := (568482660333 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12522])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12522])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12522]

theorem cert12522_4 : CellCertificate 12522 (445865582025569 / 5000000000000000 : ℝ) (1677409908406683 / 1000000000000000000 : ℝ) (338945947711227 / 10000000000000000 : ℝ)
    (cell12522 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · have h := gap_lower (n := 12522) (a := (83938741325817 / 100000000000000 : ℝ)) (b := (6580946567 / 4000000000000 : ℝ)) (q := (1136967320233 / 50000000000000 : ℝ))
      (E := (cell12522 ⟨4, by decide⟩).energy) (xi := (338945947711227 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12522 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12522]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12522])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12522) (a := (83938741325817 / 100000000000000 : ℝ)) (b := (6580946567 / 4000000000000 : ℝ)) (q := (1136967320233 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12522])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12522])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12522]

theorem cert12522_5 : CellCertificate 12522 (445865582025569 / 5000000000000000 : ℝ) (1677409908406683 / 1000000000000000000 : ℝ) (338945947711227 / 10000000000000000 : ℝ)
    (cell12522 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · have h := gap_lower (n := 12522) (a := (65549850449 / 78125000000 : ℝ)) (b := (6580946567 / 4000000000000 : ℝ)) (q := (2273938613799 / 100000000000000 : ℝ))
      (E := (cell12522 ⟨5, by decide⟩).energy) (xi := (338945947711227 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12522 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12522]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12522])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12522) (a := (65549850449 / 78125000000 : ℝ)) (b := (6580946567 / 4000000000000 : ℝ)) (q := (2273938613799 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12522])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12522])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12522]

theorem cert12522_6 : CellCertificate 12522 (445865582025569 / 5000000000000000 : ℝ) (1677409908406683 / 1000000000000000000 : ℝ) (338945947711227 / 10000000000000000 : ℝ)
    (cell12522 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · have h := gap_lower (n := 12522) (a := (16773780138771 / 20000000000000 : ℝ)) (b := (6580946567 / 4000000000000 : ℝ)) (q := (454788525529 / 20000000000000 : ℝ))
      (E := (cell12522 ⟨6, by decide⟩).energy) (xi := (338945947711227 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12522 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12522]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12522])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12522) (a := (16773780138771 / 20000000000000 : ℝ)) (b := (6580946567 / 4000000000000 : ℝ)) (q := (454788525529 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12522])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12522])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12522]

theorem cert12522_7 : CellCertificate 12522 (445865582025569 / 5000000000000000 : ℝ) (1677409908406683 / 1000000000000000000 : ℝ) (338945947711227 / 10000000000000000 : ℝ)
    (cell12522 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · have h := gap_lower (n := 12522) (a := (83834017647307 / 100000000000000 : ℝ)) (b := (6580946567 / 4000000000000 : ℝ)) (q := (2273946632241 / 100000000000000 : ℝ))
      (E := (cell12522 ⟨7, by decide⟩).energy) (xi := (338945947711227 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12522 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12522]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12522])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12522) (a := (83834017647307 / 100000000000000 : ℝ)) (b := (6580946567 / 4000000000000 : ℝ)) (q := (2273946632241 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12522])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12522])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12522]

theorem cert12522_8 : CellCertificate 12522 (445865582025569 / 5000000000000000 : ℝ) (1677409908406683 / 1000000000000000000 : ℝ) (338945947711227 / 10000000000000000 : ℝ)
    (cell12522 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · have h := gap_lower (n := 12522) (a := (1675983187987 / 2000000000000 : ℝ)) (b := (6580946567 / 4000000000000 : ℝ)) (q := (1136975317729 / 50000000000000 : ℝ))
      (E := (cell12522 ⟨8, by decide⟩).energy) (xi := (338945947711227 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12522 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12522]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12522])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12522) (a := (1675983187987 / 2000000000000 : ℝ)) (b := (6580946567 / 4000000000000 : ℝ)) (q := (1136975317729 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12522])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12522])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12522]

theorem cert12522_9 : CellCertificate 12522 (445865582025569 / 5000000000000000 : ℝ) (1677409908406683 / 1000000000000000000 : ℝ) (338945947711227 / 10000000000000000 : ℝ)
    (cell12522 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · have h := gap_lower (n := 12522) (a := (20941081478611 / 25000000000000 : ℝ)) (b := (6580946567 / 4000000000000 : ℝ)) (q := (1136977293453 / 50000000000000 : ℝ))
      (E := (cell12522 ⟨9, by decide⟩).energy) (xi := (338945947711227 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12522 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12522]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12522])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12522) (a := (20941081478611 / 25000000000000 : ℝ)) (b := (6580946567 / 4000000000000 : ℝ)) (q := (1136977293453 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12522])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12522])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12522]

theorem cert12522_10 : CellCertificate 12522 (445865582025569 / 5000000000000000 : ℝ) (1677409908406683 / 1000000000000000000 : ℝ) (338945947711227 / 10000000000000000 : ℝ)
    (cell12522 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · have h := gap_lower (n := 12522) (a := (83729517157237 / 100000000000000 : ℝ)) (b := (6580946567 / 4000000000000 : ℝ)) (q := (2273958609931 / 100000000000000 : ℝ))
      (E := (cell12522 ⟨10, by decide⟩).energy) (xi := (338945947711227 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12522 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12522]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12522])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12522) (a := (83729517157237 / 100000000000000 : ℝ)) (b := (6580946567 / 4000000000000 : ℝ)) (q := (2273958609931 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12522])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12522])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12522]

theorem cert12522_11 : CellCertificate 12522 (445865582025569 / 5000000000000000 : ℝ) (1677409908406683 / 1000000000000000000 : ℝ) (338945947711227 / 10000000000000000 : ℝ)
    (cell12522 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · have h := gap_lower (n := 12522) (a := (83694733092559 / 100000000000000 : ℝ)) (b := (6580946567 / 4000000000000 : ℝ)) (q := (454792519123 / 20000000000000 : ℝ))
      (E := (cell12522 ⟨11, by decide⟩).energy) (xi := (338945947711227 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12522 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12522]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12522])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12522) (a := (83694733092559 / 100000000000000 : ℝ)) (b := (6580946567 / 4000000000000 : ℝ)) (q := (454792519123 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12522])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12522])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12522]

theorem cert12522_12 : CellCertificate 12522 (445865582025569 / 5000000000000000 : ℝ) (1677409908406683 / 1000000000000000000 : ℝ) (338945947711227 / 10000000000000000 : ℝ)
    (cell12522 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · have h := gap_lower (n := 12522) (a := (20914993421357 / 25000000000000 : ℝ)) (b := (6580946567 / 4000000000000 : ℝ)) (q := (113698330441 / 5000000000000 : ℝ))
      (E := (cell12522 ⟨12, by decide⟩).energy) (xi := (338945947711227 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12522 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12522]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12522])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12522) (a := (20914993421357 / 25000000000000 : ℝ)) (b := (6580946567 / 4000000000000 : ℝ)) (q := (113698330441 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12522])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12522])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12522]

theorem cert12522_13 : CellCertificate 12522 (445865582025569 / 5000000000000000 : ℝ) (1677409908406683 / 1000000000000000000 : ℝ) (338945947711227 / 10000000000000000 : ℝ)
    (cell12522 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · have h := gap_lower (n := 12522) (a := (1045315486263 / 1250000000000 : ℝ)) (b := (6580946567 / 4000000000000 : ℝ)) (q := (2273970598063 / 100000000000000 : ℝ))
      (E := (cell12522 ⟨13, by decide⟩).energy) (xi := (338945947711227 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12522 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12522]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12522])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12522) (a := (1045315486263 / 1250000000000 : ℝ)) (b := (6580946567 / 4000000000000 : ℝ)) (q := (2273970598063 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12522])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12522])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12522]

theorem cert12522_14 : CellCertificate 12522 (445865582025569 / 5000000000000000 : ℝ) (1677409908406683 / 1000000000000000000 : ℝ) (338945947711227 / 10000000000000000 : ℝ)
    (cell12522 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · have h := gap_lower (n := 12522) (a := (3343621148191 / 4000000000000 : ℝ)) (b := (6580946567 / 4000000000000 : ℝ)) (q := (568493656939 / 25000000000000 : ℝ))
      (E := (cell12522 ⟨14, by decide⟩).energy) (xi := (338945947711227 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12522 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12522]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12522])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12522) (a := (3343621148191 / 4000000000000 : ℝ)) (b := (6580946567 / 4000000000000 : ℝ)) (q := (568493656939 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12522])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12522])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12522]

theorem cert12522_15 : CellCertificate 12522 (445865582025569 / 5000000000000000 : ℝ) (1677409908406683 / 1000000000000000000 : ℝ) (338945947711227 / 10000000000000000 : ℝ)
    (cell12522 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · have h := gap_lower (n := 12522) (a := (83555843062193 / 100000000000000 : ℝ)) (b := (6580946567 / 4000000000000 : ℝ)) (q := (142123661733 / 6250000000000 : ℝ))
      (E := (cell12522 ⟨15, by decide⟩).energy) (xi := (338945947711227 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12522 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12522]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12522])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12522) (a := (83555843062193 / 100000000000000 : ℝ)) (b := (6580946567 / 4000000000000 : ℝ)) (q := (142123661733 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12522])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12522])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12522]

theorem cert12522_16 : CellCertificate 12522 (445865582025569 / 5000000000000000 : ℝ) (1677409908406683 / 1000000000000000000 : ℝ) (338945947711227 / 10000000000000000 : ℝ)
    (cell12522 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · have h := gap_lower (n := 12522) (a := (10440147742379 / 12500000000000 : ℝ)) (b := (6580946567 / 4000000000000 : ℝ)) (q := (2273982600043 / 100000000000000 : ℝ))
      (E := (cell12522 ⟨16, by decide⟩).energy) (xi := (338945947711227 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12522 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12522]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12522])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12522) (a := (10440147742379 / 12500000000000 : ℝ)) (b := (6580946567 / 4000000000000 : ℝ)) (q := (2273982600043 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12522])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12522])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12522]

theorem cert12522_17 : CellCertificate 12522 (445865582025569 / 5000000000000000 : ℝ) (1677409908406683 / 1000000000000000000 : ℝ) (338945947711227 / 10000000000000000 : ℝ)
    (cell12522 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · have h := gap_lower (n := 12522) (a := (8348654530121 / 10000000000000 : ℝ)) (b := (6580946567 / 4000000000000 : ℝ)) (q := (454797322427 / 20000000000000 : ℝ))
      (E := (cell12522 ⟨17, by decide⟩).energy) (xi := (338945947711227 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12522 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12522]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12522])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12522) (a := (8348654530121 / 10000000000000 : ℝ)) (b := (6580946567 / 4000000000000 : ℝ)) (q := (454797322427 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12522])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12522])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12522]

theorem cert12522_18 : CellCertificate 12522 (445865582025569 / 5000000000000000 : ℝ) (1677409908406683 / 1000000000000000000 : ℝ) (338945947711227 / 10000000000000000 : ℝ)
    (cell12522 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · have h := gap_lower (n := 12522) (a := (83451933114819 / 100000000000000 : ℝ)) (b := (6580946567 / 4000000000000 : ℝ)) (q := (71062205347 / 3125000000000 : ℝ))
      (E := (cell12522 ⟨18, by decide⟩).energy) (xi := (338945947711227 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12522 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12522]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12522])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12522) (a := (83451933114819 / 100000000000000 : ℝ)) (b := (6580946567 / 4000000000000 : ℝ)) (q := (71062205347 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12522])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12522])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12522]

theorem cert12522_19 : CellCertificate 12522 (445865582025569 / 5000000000000000 : ℝ) (1677409908406683 / 1000000000000000000 : ℝ) (338945947711227 / 10000000000000000 : ℝ)
    (cell12522 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · have h := gap_lower (n := 12522) (a := (5213584084133 / 6250000000000 : ℝ)) (b := (6580946567 / 4000000000000 : ℝ)) (q := (1136997299211 / 50000000000000 : ℝ))
      (E := (cell12522 ⟨19, by decide⟩).energy) (xi := (338945947711227 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12522 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12522]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12522])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12522) (a := (5213584084133 / 6250000000000 : ℝ)) (b := (6580946567 / 4000000000000 : ℝ)) (q := (1136997299211 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12522])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12522])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12522]

theorem cert12523_0 : CellCertificate 12523 (891702461391051 / 10000000000000000 : ℝ) (838637958706297 / 500000000000000000 : ℝ) (16945909960303 / 500000000000000 : ℝ)
    (cell12523 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · have h := gap_lower (n := 12523) (a := (21019676548931 / 25000000000000 : ℝ)) (b := (164510360781 / 100000000000000 : ℝ)) (q := (2273788800823 / 100000000000000 : ℝ))
      (E := (cell12523 ⟨0, by decide⟩).energy) (xi := (16945909960303 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12523 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12523]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12523])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12523) (a := (21019676548931 / 25000000000000 : ℝ)) (b := (164510360781 / 100000000000000 : ℝ)) (q := (2273788800823 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12523])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12523])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12523]

theorem cert12523_1 : CellCertificate 12523 (891702461391051 / 10000000000000000 : ℝ) (838637958706297 / 500000000000000000 : ℝ) (16945909960303 / 500000000000000 : ℝ)
    (cell12523 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · have h := gap_lower (n := 12523) (a := (84043673927837 / 100000000000000 : ℝ)) (b := (164510360781 / 100000000000000 : ℝ)) (q := (568448192547 / 25000000000000 : ℝ))
      (E := (cell12523 ⟨1, by decide⟩).energy) (xi := (16945909960303 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12523 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12523]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12523])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12523) (a := (84043673927837 / 100000000000000 : ℝ)) (b := (164510360781 / 100000000000000 : ℝ)) (q := (568448192547 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12523])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12523])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12523]

theorem cert12523_2 : CellCertificate 12523 (891702461391051 / 10000000000000000 : ℝ) (838637958706297 / 500000000000000000 : ℝ) (16945909960303 / 500000000000000 : ℝ)
    (cell12523 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · have h := gap_lower (n := 12523) (a := (84008666675291 / 100000000000000 : ℝ)) (b := (164510360781 / 100000000000000 : ℝ)) (q := (1136898401693 / 50000000000000 : ℝ))
      (E := (cell12523 ⟨2, by decide⟩).energy) (xi := (16945909960303 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12523 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12523]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12523])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12523) (a := (84008666675291 / 100000000000000 : ℝ)) (b := (164510360781 / 100000000000000 : ℝ)) (q := (1136898401693 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12523])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12523])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12523]

theorem cert12523_3 : CellCertificate 12523 (891702461391051 / 10000000000000000 : ℝ) (838637958706297 / 500000000000000000 : ℝ) (16945909960303 / 500000000000000 : ℝ)
    (cell12523 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · have h := gap_lower (n := 12523) (a := (20993421100351 / 25000000000000 : ℝ)) (b := (164510360781 / 100000000000000 : ℝ)) (q := (2273800793987 / 100000000000000 : ℝ))
      (E := (cell12523 ⟨3, by decide⟩).energy) (xi := (16945909960303 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12523 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12523]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12523])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12523) (a := (20993421100351 / 25000000000000 : ℝ)) (b := (164510360781 / 100000000000000 : ℝ)) (q := (2273800793987 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12523])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12523])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12523]

theorem cert12523_4 : CellCertificate 12523 (891702461391051 / 10000000000000000 : ℝ) (838637958706297 / 500000000000000000 : ℝ) (16945909960303 / 500000000000000 : ℝ)
    (cell12523 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · have h := gap_lower (n := 12523) (a := (83938727069689 / 100000000000000 : ℝ)) (b := (164510360781 / 100000000000000 : ℝ)) (q := (2273804750887 / 100000000000000 : ℝ))
      (E := (cell12523 ⟨4, by decide⟩).energy) (xi := (16945909960303 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12523 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12523]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12523])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12523) (a := (83938727069689 / 100000000000000 : ℝ)) (b := (164510360781 / 100000000000000 : ℝ)) (q := (2273804750887 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12523])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12523])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12523]

theorem cert12523_5 : CellCertificate 12523 (891702461391051 / 10000000000000000 : ℝ) (838637958706297 / 500000000000000000 : ℝ) (16945909960303 / 500000000000000 : ℝ)
    (cell12523 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · have h := gap_lower (n := 12523) (a := (83903794643851 / 100000000000000 : ℝ)) (b := (164510360781 / 100000000000000 : ℝ)) (q := (2273808740631 / 100000000000000 : ℝ))
      (E := (cell12523 ⟨5, by decide⟩).energy) (xi := (16945909960303 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12523 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12523]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12523])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12523) (a := (83903794643851 / 100000000000000 : ℝ)) (b := (164510360781 / 100000000000000 : ℝ)) (q := (2273808740631 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12523])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12523])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12523]

theorem cert12523_6 : CellCertificate 12523 (891702461391051 / 10000000000000000 : ℝ) (838637958706297 / 500000000000000000 : ℝ) (16945909960303 / 500000000000000 : ℝ)
    (cell12523 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · have h := gap_lower (n := 12523) (a := (41934443543893 / 50000000000000 : ℝ)) (b := (164510360781 / 100000000000000 : ℝ)) (q := (568453192917 / 25000000000000 : ℝ))
      (E := (cell12523 ⟨6, by decide⟩).energy) (xi := (16945909960303 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12523 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12523]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12523])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12523) (a := (41934443543893 / 50000000000000 : ℝ)) (b := (164510360781 / 100000000000000 : ℝ)) (q := (568453192917 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12523])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12523])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12523]

theorem cert12523_7 : CellCertificate 12523 (891702461391051 / 10000000000000000 : ℝ) (838637958706297 / 500000000000000000 : ℝ) (16945909960303 / 500000000000000 : ℝ)
    (cell12523 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · have h := gap_lower (n := 12523) (a := (83834004365581 / 100000000000000 : ℝ)) (b := (164510360781 / 100000000000000 : ℝ)) (q := (56845418407 / 2500000000000 : ℝ))
      (E := (cell12523 ⟨7, by decide⟩).energy) (xi := (16945909960303 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12523 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12523]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12523])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12523) (a := (83834004365581 / 100000000000000 : ℝ)) (b := (164510360781 / 100000000000000 : ℝ)) (q := (56845418407 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12523])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12523])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12523]

theorem cert12523_8 : CellCertificate 12523 (891702461391051 / 10000000000000000 : ℝ) (838637958706297 / 500000000000000000 : ℝ) (16945909960303 / 500000000000000 : ℝ)
    (cell12523 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · have h := gap_lower (n := 12523) (a := (20949786610377 / 25000000000000 : ℝ)) (b := (164510360781 / 100000000000000 : ℝ)) (q := (142113797389 / 6250000000000 : ℝ))
      (E := (cell12523 ⟨8, by decide⟩).energy) (xi := (16945909960303 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12523 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12523]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12523])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12523) (a := (20949786610377 / 25000000000000 : ℝ)) (b := (164510360781 / 100000000000000 : ℝ)) (q := (142113797389 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12523])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12523])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12523]

theorem cert12523_9 : CellCertificate 12523 (891702461391051 / 10000000000000000 : ℝ) (838637958706297 / 500000000000000000 : ℝ) (16945909960303 / 500000000000000 : ℝ)
    (cell12523 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · have h := gap_lower (n := 12523) (a := (8376431328003 / 10000000000000 : ℝ)) (b := (164510360781 / 100000000000000 : ℝ)) (q := (1136912364589 / 50000000000000 : ℝ))
      (E := (cell12523 ⟨9, by decide⟩).energy) (xi := (16945909960303 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12523 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12523]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12523])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12523) (a := (8376431328003 / 10000000000000 : ℝ)) (b := (164510360781 / 100000000000000 : ℝ)) (q := (1136912364589 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12523])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12523])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12523]

theorem cert12523_10 : CellCertificate 12523 (891702461391051 / 10000000000000000 : ℝ) (838637958706297 / 500000000000000000 : ℝ) (16945909960303 / 500000000000000 : ℝ)
    (cell12523 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · have h := gap_lower (n := 12523) (a := (16745900969159 / 20000000000000 : ℝ)) (b := (164510360781 / 100000000000000 : ℝ)) (q := (1136914386243 / 50000000000000 : ℝ))
      (E := (cell12523 ⟨10, by decide⟩).energy) (xi := (16945909960303 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12523 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12523]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12523])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12523) (a := (16745900969159 / 20000000000000 : ℝ)) (b := (164510360781 / 100000000000000 : ℝ)) (q := (1136914386243 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12523])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12523])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12523]

theorem cert12523_11 : CellCertificate 12523 (891702461391051 / 10000000000000000 : ℝ) (838637958706297 / 500000000000000000 : ℝ) (16945909960303 / 500000000000000 : ℝ)
    (cell12523 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · have h := gap_lower (n := 12523) (a := (20923680275909 / 25000000000000 : ℝ)) (b := (164510360781 / 100000000000000 : ℝ)) (q := (1136916360589 / 50000000000000 : ℝ))
      (E := (cell12523 ⟨11, by decide⟩).energy) (xi := (16945909960303 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12523 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12523]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12523])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12523) (a := (20923680275909 / 25000000000000 : ℝ)) (b := (164510360781 / 100000000000000 : ℝ)) (q := (1136916360589 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12523])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12523])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12523]

theorem cert12523_12 : CellCertificate 12523 (891702461391051 / 10000000000000000 : ℝ) (838637958706297 / 500000000000000000 : ℝ) (16945909960303 / 500000000000000 : ℝ)
    (cell12523 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · have h := gap_lower (n := 12523) (a := (83659962018569 / 100000000000000 : ℝ)) (b := (164510360781 / 100000000000000 : ℝ)) (q := (454767351239 / 20000000000000 : ℝ))
      (E := (cell12523 ⟨12, by decide⟩).energy) (xi := (16945909960303 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12523 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12523]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12523])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12523) (a := (83659962018569 / 100000000000000 : ℝ)) (b := (164510360781 / 100000000000000 : ℝ)) (q := (454767351239 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12523])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12523])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12523]

theorem cert12523_13 : CellCertificate 12523 (891702461391051 / 10000000000000000 : ℝ) (838637958706297 / 500000000000000000 : ℝ) (16945909960303 / 500000000000000 : ℝ)
    (cell12523 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · have h := gap_lower (n := 12523) (a := (41812613777897 / 50000000000000 : ℝ)) (b := (164510360781 / 100000000000000 : ℝ)) (q := (2273840768023 / 100000000000000 : ℝ))
      (E := (cell12523 ⟨13, by decide⟩).energy) (xi := (16945909960303 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12523 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12523]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12523])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12523) (a := (41812613777897 / 50000000000000 : ℝ)) (b := (164510360781 / 100000000000000 : ℝ)) (q := (2273840768023 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12523])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12523])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12523]

theorem cert12523_14 : CellCertificate 12523 (891702461391051 / 10000000000000000 : ℝ) (838637958706297 / 500000000000000000 : ℝ) (16945909960303 / 500000000000000 : ℝ)
    (cell12523 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · have h := gap_lower (n := 12523) (a := (8359051768069 / 10000000000000 : ℝ)) (b := (164510360781 / 100000000000000 : ℝ)) (q := (1136922381477 / 50000000000000 : ℝ))
      (E := (cell12523 ⟨14, by decide⟩).energy) (xi := (16945909960303 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12523 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12523]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12523])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12523) (a := (8359051768069 / 10000000000000 : ℝ)) (b := (164510360781 / 100000000000000 : ℝ)) (q := (1136922381477 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12523])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12523])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12523]

theorem cert12523_15 : CellCertificate 12523 (891702461391051 / 10000000000000000 : ℝ) (838637958706297 / 500000000000000000 : ℝ) (16945909960303 / 500000000000000 : ℝ)
    (cell12523 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · have h := gap_lower (n := 12523) (a := (41777916179409 / 50000000000000 : ℝ)) (b := (164510360781 / 100000000000000 : ℝ)) (q := (1136924373517 / 50000000000000 : ℝ))
      (E := (cell12523 ⟨15, by decide⟩).energy) (xi := (16945909960303 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12523 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12523]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12523])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12523) (a := (41777916179409 / 50000000000000 : ℝ)) (b := (164510360781 / 100000000000000 : ℝ)) (q := (1136924373517 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12523])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12523])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12523]

theorem cert12523_16 : CellCertificate 12523 (891702461391051 / 10000000000000000 : ℝ) (838637958706297 / 500000000000000000 : ℝ) (16945909960303 / 500000000000000 : ℝ)
    (cell12523 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · have h := gap_lower (n := 12523) (a := (41760585777959 / 50000000000000 : ℝ)) (b := (164510360781 / 100000000000000 : ℝ)) (q := (2273852726061 / 100000000000000 : ℝ))
      (E := (cell12523 ⟨16, by decide⟩).energy) (xi := (16945909960303 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12523 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12523]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12523])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12523) (a := (41760585777959 / 50000000000000 : ℝ)) (b := (164510360781 / 100000000000000 : ℝ)) (q := (2273852726061 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12523])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12523])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12523]

theorem cert12523_17 : CellCertificate 12523 (891702461391051 / 10000000000000000 : ℝ) (838637958706297 / 500000000000000000 : ℝ) (16945909960303 / 500000000000000 : ℝ)
    (cell12523 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · have h := gap_lower (n := 12523) (a := (20871633809477 / 25000000000000 : ℝ)) (b := (164510360781 / 100000000000000 : ℝ)) (q := (113692838189 / 5000000000000 : ℝ))
      (E := (cell12523 ⟨17, by decide⟩).energy) (xi := (16945909960303 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12523 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12523]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12523])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12523) (a := (20871633809477 / 25000000000000 : ℝ)) (b := (164510360781 / 100000000000000 : ℝ)) (q := (113692838189 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12523])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12523])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12523]

theorem cert12523_18 : CellCertificate 12523 (891702461391051 / 10000000000000000 : ℝ) (838637958706297 / 500000000000000000 : ℝ) (16945909960303 / 500000000000000 : ℝ)
    (cell12523 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · have h := gap_lower (n := 12523) (a := (83451923370881 / 100000000000000 : ℝ)) (b := (164510360781 / 100000000000000 : ℝ)) (q := (1136930374573 / 50000000000000 : ℝ))
      (E := (cell12523 ⟨18, by decide⟩).energy) (xi := (16945909960303 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12523 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12523]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12523])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12523) (a := (83451923370881 / 100000000000000 : ℝ)) (b := (164510360781 / 100000000000000 : ℝ)) (q := (1136930374573 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12523])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12523])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12523]

theorem cert12523_19 : CellCertificate 12523 (891702461391051 / 10000000000000000 : ℝ) (838637958706297 / 500000000000000000 : ℝ) (16945909960303 / 500000000000000 : ℝ)
    (cell12523 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · have h := gap_lower (n := 12523) (a := (83417335921107 / 100000000000000 : ℝ)) (b := (164510360781 / 100000000000000 : ℝ)) (q := (2273864745393 / 100000000000000 : ℝ))
      (E := (cell12523 ⟨19, by decide⟩).energy) (xi := (16945909960303 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12523 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12523]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12523])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12523) (a := (83417335921107 / 100000000000000 : ℝ)) (b := (164510360781 / 100000000000000 : ℝ)) (q := (2273864745393 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12523])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12523])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12523]

theorem cert12524_0 : CellCertificate 12524 (891673763138121 / 10000000000000000 : ℝ) (1677141947823113 / 1000000000000000000 : ℝ) (338890455324987 / 10000000000000000 : ℝ)
    (cell12524 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · have h := gap_lower (n := 12524) (a := (84078690636433 / 100000000000000 : ℝ)) (b := (164497059559 / 100000000000000 : ℝ)) (q := (1136829482033 / 50000000000000 : ℝ))
      (E := (cell12524 ⟨0, by decide⟩).energy) (xi := (338890455324987 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12524 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12524]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12524])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12524) (a := (84078690636433 / 100000000000000 : ℝ)) (b := (164497059559 / 100000000000000 : ℝ)) (q := (1136829482033 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12524])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12524])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12524]

theorem cert12524_1 : CellCertificate 12524 (891673763138121 / 10000000000000000 : ℝ) (1677141947823113 / 1000000000000000000 : ℝ) (338890455324987 / 10000000000000000 : ℝ)
    (cell12524 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · have h := gap_lower (n := 12524) (a := (21010914673903 / 25000000000000 : ℝ)) (b := (164497059559 / 100000000000000 : ℝ)) (q := (568415736699 / 25000000000000 : ℝ))
      (E := (cell12524 ⟨1, by decide⟩).energy) (xi := (338890455324987 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12524 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12524]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12524])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12524) (a := (21010914673903 / 25000000000000 : ℝ)) (b := (164497059559 / 100000000000000 : ℝ)) (q := (568415736699 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12524])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12524])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12524]

theorem cert12524_2 : CellCertificate 12524 (891673763138121 / 10000000000000000 : ℝ) (1677141947823113 / 1000000000000000000 : ℝ) (338890455324987 / 10000000000000000 : ℝ)
    (cell12524 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · have h := gap_lower (n := 12524) (a := (84008651769669 / 100000000000000 : ℝ)) (b := (164497059559 / 100000000000000 : ℝ)) (q := (142104183519 / 6250000000000 : ℝ))
      (E := (cell12524 ⟨2, by decide⟩).energy) (xi := (338890455324987 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12524 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12524]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12524])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12524) (a := (84008651769669 / 100000000000000 : ℝ)) (b := (164497059559 / 100000000000000 : ℝ)) (q := (142104183519 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12524])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12524])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12524]

theorem cert12524_3 : CellCertificate 12524 (891673763138121 / 10000000000000000 : ℝ) (1677141947823113 / 1000000000000000000 : ℝ) (338890455324987 / 10000000000000000 : ℝ)
    (cell12524 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · have h := gap_lower (n := 12524) (a := (83973669821923 / 100000000000000 : ℝ)) (b := (164497059559 / 100000000000000 : ℝ)) (q := (284208867727 / 12500000000000 : ℝ))
      (E := (cell12524 ⟨3, by decide⟩).energy) (xi := (338890455324987 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12524 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12524]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12524])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12524) (a := (83973669821923 / 100000000000000 : ℝ)) (b := (164497059559 / 100000000000000 : ℝ)) (q := (284208867727 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12524])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12524])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12524]

theorem cert12524_4 : CellCertificate 12524 (891673763138121 / 10000000000000000 : ℝ) (1677141947823113 / 1000000000000000000 : ℝ) (338890455324987 / 10000000000000000 : ℝ)
    (cell12524 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · have h := gap_lower (n := 12524) (a := (5246169550993 / 6250000000000 : ℝ)) (b := (164497059559 / 100000000000000 : ℝ)) (q := (1136837486147 / 50000000000000 : ℝ))
      (E := (cell12524 ⟨4, by decide⟩).energy) (xi := (338890455324987 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12524 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12524]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12524])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12524) (a := (5246169550993 / 6250000000000 : ℝ)) (b := (164497059559 / 100000000000000 : ℝ)) (q := (1136837486147 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12524])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12524])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12524]

theorem cert12524_5 : CellCertificate 12524 (891673763138121 / 10000000000000000 : ℝ) (1677141947823113 / 1000000000000000000 : ℝ) (338890455324987 / 10000000000000000 : ℝ)
    (cell12524 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · have h := gap_lower (n := 12524) (a := (83903780715269 / 100000000000000 : ℝ)) (b := (164497059559 / 100000000000000 : ℝ)) (q := (2273678978537 / 100000000000000 : ℝ))
      (E := (cell12524 ⟨5, by decide⟩).energy) (xi := (338890455324987 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12524 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12524]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12524])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12524) (a := (83903780715269 / 100000000000000 : ℝ)) (b := (164497059559 / 100000000000000 : ℝ)) (q := (2273678978537 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12524])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12524])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12524]

theorem cert12524_6 : CellCertificate 12524 (891673763138121 / 10000000000000000 : ℝ) (1677141947823113 / 1000000000000000000 : ℝ) (338890455324987 / 10000000000000000 : ℝ)
    (cell12524 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · have h := gap_lower (n := 12524) (a := (16773774696793 / 20000000000000 : ℝ)) (b := (164497059559 / 100000000000000 : ℝ)) (q := (56842074223 / 2500000000000 : ℝ))
      (E := (cell12524 ⟨6, by decide⟩).energy) (xi := (338890455324987 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12524 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12524]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12524])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12524) (a := (16773774696793 / 20000000000000 : ℝ)) (b := (164497059559 / 100000000000000 : ℝ)) (q := (56842074223 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12524])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12524])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12524]

theorem cert12524_7 : CellCertificate 12524 (891673763138121 / 10000000000000000 : ℝ) (1677141947823113 / 1000000000000000000 : ℝ) (338890455324987 / 10000000000000000 : ℝ)
    (cell12524 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · have h := gap_lower (n := 12524) (a := (83833991086061 / 100000000000000 : ℝ)) (b := (164497059559 / 100000000000000 : ℝ)) (q := (142105434473 / 6250000000000 : ℝ))
      (E := (cell12524 ⟨7, by decide⟩).energy) (xi := (338890455324987 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12524 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12524]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12524])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12524) (a := (83833991086061 / 100000000000000 : ℝ)) (b := (164497059559 / 100000000000000 : ℝ)) (q := (142105434473 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12524])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12524])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12524]

theorem cert12524_8 : CellCertificate 12524 (891673763138121 / 10000000000000000 : ℝ) (1677141947823113 / 1000000000000000000 : ℝ) (338890455324987 / 10000000000000000 : ℝ)
    (cell12524 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · have h := gap_lower (n := 12524) (a := (10474891685729 / 12500000000000 : ℝ)) (b := (164497059559 / 100000000000000 : ℝ)) (q := (568422733587 / 25000000000000 : ℝ))
      (E := (cell12524 ⟨8, by decide⟩).energy) (xi := (338890455324987 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12524 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12524]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12524])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12524) (a := (10474891685729 / 12500000000000 : ℝ)) (b := (164497059559 / 100000000000000 : ℝ)) (q := (568422733587 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12524])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12524])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12524]

theorem cert12524_9 : CellCertificate 12524 (891673763138121 / 10000000000000000 : ℝ) (1677141947823113 / 1000000000000000000 : ℝ) (338890455324987 / 10000000000000000 : ℝ)
    (cell12524 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · have h := gap_lower (n := 12524) (a := (83764300647743 / 100000000000000 : ℝ)) (b := (164497059559 / 100000000000000 : ℝ)) (q := (2273694924871 / 100000000000000 : ℝ))
      (E := (cell12524 ⟨9, by decide⟩).energy) (xi := (338890455324987 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12524 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12524]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12524])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12524) (a := (83764300647743 / 100000000000000 : ℝ)) (b := (164497059559 / 100000000000000 : ℝ)) (q := (2273694924871 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12524])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12524])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12524]

theorem cert12524_10 : CellCertificate 12524 (891673763138121 / 10000000000000000 : ℝ) (1677141947823113 / 1000000000000000000 : ℝ) (338890455324987 / 10000000000000000 : ℝ)
    (cell12524 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · have h := gap_lower (n := 12524) (a := (83729492536441 / 100000000000000 : ℝ)) (b := (164497059559 / 100000000000000 : ℝ)) (q := (4547397861 / 200000000000 : ℝ))
      (E := (cell12524 ⟨10, by decide⟩).energy) (xi := (338890455324987 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12524 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12524]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12524])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12524) (a := (83729492536441 / 100000000000000 : ℝ)) (b := (164497059559 / 100000000000000 : ℝ)) (q := (4547397861 / 200000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12524])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12524])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12524]

theorem cert12524_11 : CellCertificate 12524 (891673763138121 / 10000000000000000 : ℝ) (1677141947823113 / 1000000000000000000 : ℝ) (338890455324987 / 10000000000000000 : ℝ)
    (cell12524 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · have h := gap_lower (n := 12524) (a := (83694709116761 / 100000000000000 : ℝ)) (b := (164497059559 / 100000000000000 : ℝ)) (q := (1136851479171 / 50000000000000 : ℝ))
      (E := (cell12524 ⟨11, by decide⟩).energy) (xi := (338890455324987 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12524 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12524]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12524])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12524) (a := (83694709116761 / 100000000000000 : ℝ)) (b := (164497059559 / 100000000000000 : ℝ)) (q := (1136851479171 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12524])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12524])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12524]

theorem cert12524_12 : CellCertificate 12524 (891673763138121 / 10000000000000000 : ℝ) (1677141947823113 / 1000000000000000000 : ℝ) (338890455324987 / 10000000000000000 : ℝ)
    (cell12524 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · have h := gap_lower (n := 12524) (a := (83659950353719 / 100000000000000 : ℝ)) (b := (164497059559 / 100000000000000 : ℝ)) (q := (17763335603 / 781250000000 : ℝ))
      (E := (cell12524 ⟨12, by decide⟩).energy) (xi := (338890455324987 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12524 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12524]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12524])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12524) (a := (83659950353719 / 100000000000000 : ℝ)) (b := (164497059559 / 100000000000000 : ℝ)) (q := (17763335603 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12524])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12524])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12524]

theorem cert12524_13 : CellCertificate 12524 (891673763138121 / 10000000000000000 : ℝ) (1677141947823113 / 1000000000000000000 : ℝ) (338890455324987 / 10000000000000000 : ℝ)
    (cell12524 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · have h := gap_lower (n := 12524) (a := (20906304053129 / 25000000000000 : ℝ)) (b := (164497059559 / 100000000000000 : ℝ)) (q := (454742186713 / 20000000000000 : ℝ))
      (E := (cell12524 ⟨13, by decide⟩).energy) (xi := (338890455324987 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12524 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12524]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12524])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12524) (a := (20906304053129 / 25000000000000 : ℝ)) (b := (164497059559 / 100000000000000 : ℝ)) (q := (454742186713 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12524])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12524])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12524]

theorem cert12524_14 : CellCertificate 12524 (891673763138121 / 10000000000000000 : ℝ) (1677141947823113 / 1000000000000000000 : ℝ) (338890455324987 / 10000000000000000 : ℝ)
    (cell12524 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · have h := gap_lower (n := 12524) (a := (41795253329267 / 50000000000000 : ℝ)) (b := (164497059559 / 100000000000000 : ℝ)) (q := (454742990379 / 20000000000000 : ℝ))
      (E := (cell12524 ⟨14, by decide⟩).energy) (xi := (338890455324987 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12524 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12524]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12524])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12524) (a := (41795253329267 / 50000000000000 : ℝ)) (b := (164497059559 / 100000000000000 : ℝ)) (q := (454742990379 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12524])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12524])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12524]

theorem cert12524_15 : CellCertificate 12524 (891673763138121 / 10000000000000000 : ℝ) (1677141947823113 / 1000000000000000000 : ℝ) (338890455324987 / 10000000000000000 : ℝ)
    (cell12524 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · have h := gap_lower (n := 12524) (a := (83555821657333 / 100000000000000 : ℝ)) (b := (164497059559 / 100000000000000 : ℝ)) (q := (2273718902003 / 100000000000000 : ℝ))
      (E := (cell12524 ⟨15, by decide⟩).energy) (xi := (338890455324987 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12524 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12524]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12524])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12524) (a := (83555821657333 / 100000000000000 : ℝ)) (b := (164497059559 / 100000000000000 : ℝ)) (q := (2273718902003 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12524])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12524])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12524]

theorem cert12524_16 : CellCertificate 12524 (891673763138121 / 10000000000000000 : ℝ) (1677141947823113 / 1000000000000000000 : ℝ) (338890455324987 / 10000000000000000 : ℝ)
    (cell12524 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · have h := gap_lower (n := 12524) (a := (41760580587327 / 50000000000000 : ℝ)) (b := (164497059559 / 100000000000000 : ℝ)) (q := (2273722905951 / 100000000000000 : ℝ))
      (E := (cell12524 ⟨16, by decide⟩).energy) (xi := (338890455324987 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12524 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12524]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12524])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12524) (a := (41760580587327 / 50000000000000 : ℝ)) (b := (164497059559 / 100000000000000 : ℝ)) (q := (2273722905951 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12524])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12524])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12524]

theorem cert12524_17 : CellCertificate 12524 (891673763138121 / 10000000000000000 : ℝ) (1677141947823113 / 1000000000000000000 : ℝ) (338890455324987 / 10000000000000000 : ℝ)
    (cell12524 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · have h := gap_lower (n := 12524) (a := (2608953911763 / 3125000000000 : ℝ)) (b := (164497059559 / 100000000000000 : ℝ)) (q := (2273726911171 / 100000000000000 : ℝ))
      (E := (cell12524 ⟨17, by decide⟩).energy) (xi := (338890455324987 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12524 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12524]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12524])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12524) (a := (2608953911763 / 3125000000000 : ℝ)) (b := (164497059559 / 100000000000000 : ℝ)) (q := (2273726911171 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12524])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12524])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12524]

theorem cert12524_18 : CellCertificate 12524 (891673763138121 / 10000000000000000 : ℝ) (1677141947823113 / 1000000000000000000 : ℝ) (338890455324987 / 10000000000000000 : ℝ)
    (cell12524 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · have h := gap_lower (n := 12524) (a := (41725956814357 / 50000000000000 : ℝ)) (b := (164497059559 / 100000000000000 : ℝ)) (q := (2273730922973 / 100000000000000 : ℝ))
      (E := (cell12524 ⟨18, by decide⟩).energy) (xi := (338890455324987 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12524 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12524]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12524])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12524) (a := (41725956814357 / 50000000000000 : ℝ)) (b := (164497059559 / 100000000000000 : ℝ)) (q := (2273730922973 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12524])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12524])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12524]

theorem cert12524_19 : CellCertificate 12524 (891673763138121 / 10000000000000000 : ℝ) (1677141947823113 / 1000000000000000000 : ℝ) (338890455324987 / 10000000000000000 : ℝ)
    (cell12524 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · have h := gap_lower (n := 12524) (a := (41708663248909 / 50000000000000 : ℝ)) (b := (164497059559 / 100000000000000 : ℝ)) (q := (1136867473213 / 50000000000000 : ℝ))
      (E := (cell12524 ⟨19, by decide⟩).energy) (xi := (338890455324987 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12524 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12524]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12524])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12524) (a := (41708663248909 / 50000000000000 : ℝ)) (b := (164497059559 / 100000000000000 : ℝ)) (q := (1136867473213 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12524])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12524])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12524]

end BstLean.Part268
